module

import StacksFrontier.RingTheory.AdjoinRoot.LocalRing
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
import StacksFrontier.RingTheory.Etale.ResidueFieldColimit
import StacksFrontier.RingTheory.Henselian.Colimit
import StacksFrontier.RingTheory.Henselian.QuasiFinite
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# The strict henselization as a union of finite étale extensions of the henselization

Let `R → R^h` be the henselization of a local ring `(R, 𝔪, κ)` and let `κ ⊆ κ^sep` be a separable
algebraic closure. For every finite subextension `κ ⊆ κ' ⊆ κ^sep` there is a finite étale local
extension `R^h ⊆ R^h(κ')` whose residue field extension is `κ ⊆ κ'`, unique up to unique
isomorphism, and the maps between them compatible with the inclusions of residue fields exist and
are unique. Their union is a strict henselization of `R`.

## Main definitions

* `IsLocalRing.FiniteIntermediateField κ Ω`: a finite subextension of `κ ⊆ Ω`.
* `IsLocalRing.FiniteEtaleLocalResidueLift R Rh Ω e L`: a finite étale local `Rh`-algebra whose
  residue field is identified with the finite subextension `L`, compatibly with `e`.

## Main results

* `IsLocalRing.IsHenselization.exists_strictHenselization_iUnion_finiteEtale`: the system of the
  rings `R^h(κ')`, its transition maps and their uniqueness, and a union of it which is strictly
  henselian and a strict henselization of both `R^h` and `R`.

## Implementation notes

The rings `R^h(κ')` are abstract local `Rh`-algebras together with injective embeddings `ι` into
the union, whose images exhaust it; this is the same as presenting them as subrings of the union,
and it lets the statement record the unique isomorphisms between any two choices. All rings live
in the universe of `R`.

## References

* [StacksProject 0BSL](https://stacks.math.columbia.edu/tag/0BSL)
* [StacksProject 04GK](https://stacks.math.columbia.edu/tag/04GK)
* [StacksProject 04GI](https://stacks.math.columbia.edu/tag/04GI)
-/

@[expose] public section

open IsLocalRing Polynomial

universe u w z t

namespace IsLocalRing

/-- A finite subextension of a field extension `κ ⊆ Ω`. -/
structure FiniteIntermediateField (κ : Type u) (Ω : Type w) [Field κ] [Field Ω] [Algebra κ Ω] where
  /-- The underlying intermediate field. -/
  toIntermediateField : IntermediateField κ Ω
  /-- The intermediate field is finite over the base field. -/
  [finiteDimensional : FiniteDimensional κ toIntermediateField]

namespace FiniteIntermediateField

variable {κ : Type u} {Ω : Type w} [Field κ] [Field Ω] [Algebra κ Ω]

/-- A finite subextension is regarded as a type through its intermediate field. -/
instance : CoeSort (FiniteIntermediateField κ Ω) (Type w) :=
  ⟨fun L => L.toIntermediateField⟩

/-- A finite subextension is finite-dimensional over the base field. -/
instance (L : FiniteIntermediateField κ Ω) : FiniteDimensional κ L := L.finiteDimensional

/-- Finite subextensions are ordered by inclusion. -/
instance : Preorder (FiniteIntermediateField κ Ω) :=
  Preorder.lift toIntermediateField

/-- The order on finite subextensions is inclusion of intermediate fields. -/
theorem le_def {L M : FiniteIntermediateField κ Ω} :
    L ≤ M ↔ L.toIntermediateField ≤ M.toIntermediateField := Iff.rfl

/-- Finite subextensions are directed: two of them lie in their compositum. -/
instance : IsDirected (FiniteIntermediateField κ Ω) (· ≤ ·) :=
  ⟨fun L M => ⟨⟨L.toIntermediateField ⊔ M.toIntermediateField⟩,
    le_def.mpr le_sup_left, le_def.mpr le_sup_right⟩⟩

/-- The base field itself is a finite subextension. -/
instance : Nonempty (FiniteIntermediateField κ Ω) := ⟨⟨⊥⟩⟩

/-- Every element of an algebraic extension lies in a finite subextension. -/
theorem exists_mem [Algebra.IsAlgebraic κ Ω] (x : Ω) :
    ∃ L : FiniteIntermediateField κ Ω, x ∈ L.toIntermediateField :=
  have := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := κ) x)
  ⟨⟨IntermediateField.adjoin κ {x}⟩, IntermediateField.subset_adjoin κ {x} rfl⟩

end FiniteIntermediateField

/-- A finite étale local extension of `Rh` whose residue field is the prescribed finite
subextension `L` of `κ ⊆ Ω`, where `κ` is the residue field of `R`, compatibly with a fixed
identification `e` of `κ` with the residue field of `Rh`. -/
structure FiniteEtaleLocalResidueLift (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] (Ω : Type w) [Field Ω]
    [Algebra (ResidueField R) Ω] (e : ResidueField R ≃+* ResidueField Rh)
    (L : FiniteIntermediateField (ResidueField R) Ω) where
  /-- The underlying finite étale local ring. -/
  carrier : Type z
  [commRing : CommRing carrier]
  [isLocalRing : IsLocalRing carrier]
  [algebra : Algebra Rh carrier]
  [isLocalHom : IsLocalHom (algebraMap Rh carrier)]
  [finite : Module.Finite Rh carrier]
  [etale : Algebra.Etale Rh carrier]
  [henselian : HenselianLocalRing carrier]
  /-- The identification of `L` with the residue field of the lift. -/
  residueEquiv : L ≃+* ResidueField carrier
  /-- The identification extends the identification `e` of the residue fields of `R` and `Rh`. -/
  residueEquiv_algebraMap : ∀ x : ResidueField R,
    residueEquiv (algebraMap (ResidueField R) L x) =
      ResidueField.map (algebraMap Rh carrier) (e x)

namespace FiniteEtaleLocalResidueLift

variable {R : Type u} [CommRing R] [IsLocalRing R] {Rh : Type u} [CommRing Rh] [IsLocalRing Rh]
  {Ω : Type w} [Field Ω] [Algebra (ResidueField R) Ω] {e : ResidueField R ≃+* ResidueField Rh}
  {L : FiniteIntermediateField (ResidueField R) Ω}

/-- A lift is regarded as a type through its underlying ring. -/
instance : CoeSort (FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L) (Type z) :=
  ⟨FiniteEtaleLocalResidueLift.carrier⟩

attribute [instance] commRing isLocalRing algebra isLocalHom finite etale henselian

end FiniteEtaleLocalResidueLift

/-- A ring map of local rings which is compatible with a map of residue fields is local. -/
theorem isLocalHom_of_residue_eq {A : Type*} {B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) (g : ResidueField A →+* ResidueField B)
    (h : ∀ x, residue B (f x) = g (residue A x)) : IsLocalHom f := by
  apply ((local_hom_TFAE f).out 4 1).mp
  intro x hx
  rw [Ideal.mem_comap, ← residue_eq_zero_iff, h, (residue_eq_zero_iff _).mpr hx, map_zero]

end IsLocalRing

namespace IsLocalRing.FiniteEtaleLocalResidueLift

variable {R : Type u} [CommRing R] [IsLocalRing R] {Rh : Type u} [CommRing Rh] [IsLocalRing Rh]
  {Ω : Type w} [Field Ω] [Algebra (ResidueField R) Ω] {e : ResidueField R ≃+* ResidueField Rh}
  {L L' : FiniteIntermediateField (ResidueField R) Ω}

/-- The map of residue fields `κ(A) ≅ L → L' ≅ κ(B)` induced by `g : L → L'`. -/
noncomputable def residueMap (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L')
    (g : L →+* L') : ResidueField A →+* ResidueField B :=
  B.residueEquiv.toRingHom.comp (g.comp A.residueEquiv.symm.toRingHom)

/-- A map between lifts inducing `g` on residue fields is injective: it is local, and a local map
out of an étale local algebra into a flat local algebra is faithfully flat. -/
theorem injective_of_residue_eq (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L') (g : L →+* L') (f : A →ₐ[Rh] B)
    (hf : ∀ a, residue B (f a) = residueMap A B g (residue A a)) : Function.Injective f := by
  have : IsLocalHom f.toRingHom := isLocalHom_of_residue_eq f.toRingHom _ hf
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower Rh A B := .of_algebraMap_eq fun r => (f.commutes r).symm
  have : Module.Flat A B := Algebra.FormallyUnramified.flat_of_restrictScalars Rh A B
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom f.toRingHom›
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff.mpr this).injective

/-- The map `residueMap A B g` is compatible with the structure maps from `Rh`. -/
theorem residueMap_residue_algebraMap (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L') (g : L →ₐ[ResidueField R] L')
    (x : Rh) :
    residueMap A B g (residue A (algebraMap Rh A x)) = algebraMap Rh (ResidueField B) x := by
  obtain ⟨y, hy⟩ := e.surjective (residue Rh x)
  have hA := A.residueEquiv_algebraMap y
  have hB := B.residueEquiv_algebraMap y
  rw [hy, ResidueField.map_residue] at hA hB
  rw [residueMap, RingHom.comp_apply, RingHom.comp_apply, ← hA]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
    AlgHom.coe_toRingHom]
  rw [g.commutes, hB, IsScalarTower.algebraMap_apply Rh B (ResidueField B),
    ResidueField.algebraMap_eq]

/-- **Lemma 04GK for the lifts.** A map `g : L → L'` of finite subextensions over `κ` is induced by
exactly one `Rh`-algebra map `A → B` between lifts of `L` and `L'`. -/
theorem existsUnique_algHom (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L') (g : L →ₐ[ResidueField R] L') :
    ∃! f : A →ₐ[Rh] B, ∀ a, residue B (f a) = residueMap A B g (residue A a) :=
  HenselianLocalRing.existsUnique_algHom_residue_of_etale
    { toRingHom := (residueMap A B g.toRingHom).comp (residue A)
      commutes' := residueMap_residue_algebraMap A B g }

/-- Maps between lifts of the same subextension inducing the identity on residue fields are
mutually inverse. -/
private theorem comp_eq_id (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L) (f : A →ₐ[Rh] B) (g : B →ₐ[Rh] A)
    (hf : ∀ a, residue B (f a) = residueMap A B (RingHom.id L) (residue A a))
    (hg : ∀ b, residue A (g b) = residueMap B A (RingHom.id L) (residue B b)) :
    g.comp f = AlgHom.id Rh A :=
  (existsUnique_algHom A A (AlgHom.id _ _)).unique (fun a => by simp [residueMap, hf, hg])
    (by simp [residueMap])

/-- Two lifts of the same finite subextension are isomorphic by exactly one isomorphism inducing
the identity of `L` on residue fields. -/
theorem existsUnique_algEquiv (A : FiniteEtaleLocalResidueLift.{u, w, z} R Rh Ω e L)
    (B : FiniteEtaleLocalResidueLift.{u, w, t} R Rh Ω e L) :
    ∃! f : A ≃ₐ[Rh] B, ∀ a, residue B (f a) = residueMap A B (RingHom.id L) (residue A a) := by
  obtain ⟨f, hf, hu⟩ := existsUnique_algHom A B (AlgHom.id _ _)
  obtain ⟨g, hg, -⟩ := existsUnique_algHom B A (AlgHom.id _ _)
  exact ⟨.ofAlgHom f g (comp_eq_id B A g f hg hf) (comp_eq_id A B f g hf hg), hf, fun j hj =>
    AlgEquiv.coe_toAlgHom_injective (hu j.toAlgHom hj)⟩

/-- **Existence of the lifts** (Lemma 04GK). A finite separable extension `K` of the residue field
of a local ring `A` is the residue field extension of a finite étale local `A`-algebra, namely
`A[X]/(p)` for a monic lift `p` of the minimal polynomial of a primitive element. -/
@[sga "3 VIA 1.2" "special case",
  sga "3 XXIV 3.9.1" "local base, special case",
  sga "3 XXIV 8.1.2" "more general"]
theorem exists_residueField_algEquiv (A : Type u) [CommRing A] [IsLocalRing A] (K : Type w)
    [Field K] [Algebra (ResidueField A) K] [FiniteDimensional (ResidueField A) K]
    [Algebra.IsSeparable (ResidueField A) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B)
      (_ : IsLocalHom (algebraMap A B)) (_ : Module.Finite A B) (_ : Algebra.Etale A B),
      Nonempty (ResidueField B ≃ₐ[ResidueField A] K) := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element (ResidueField A) K
  have hi := Algebra.IsSeparable.isIntegral (ResidueField A) β
  obtain ⟨p, hpmap, -, hp⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts _).2 fun _ => residue_surjective _) (minpoly.monic hi)
  have hirr : Irreducible (p.map (residue A)) := hpmap ▸ minpoly.irreducible hi
  have hsep : (p.map (residue A)).Separable := hpmap ▸ Algebra.IsSeparable.isSeparable _ β
  have := AdjoinRoot.isLocalRing_of_irreducible_map_residue hp hirr
  have : Module.Finite A (AdjoinRoot p) := hp.finite_adjoinRoot
  have := Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot_of_separable hp hirr hsep
  have : IsLocalHom (algebraMap A (AdjoinRoot p)) := by
    rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.isLocalHom_of_monic hp
  let θ : AdjoinRoot p →+* K := AdjoinRoot.lift
    ((algebraMap (ResidueField A) K).comp (residue A)) β (by
      rw [← Polynomial.eval₂_map, hpmap, ← Polynomial.aeval_def, minpoly.aeval])
  have hker : maximalIdeal (AdjoinRoot p) ≤ RingHom.ker θ := by
    rw [AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr, Ideal.map_le_iff_le_comap]
    intro a ha
    simp [θ, (residue_eq_zero_iff _).mpr ha]
  have : IsLocalHom θ := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (RingHom.mem_ker.mp (hker ((mem_maximalIdeal a).mpr h)))⟩
  let ψ : ResidueField (AdjoinRoot p) →ₐ[ResidueField A] K :=
    { toRingHom := ResidueField.lift θ
      commutes' := fun x => by
        obtain ⟨a, rfl⟩ := residue_surjective x
        simp [θ, AdjoinRoot.algebraMap_eq] }
  have hψβ : ψ (residue (AdjoinRoot p) (AdjoinRoot.root p)) = β := by simp [ψ, θ]
  have hadj : Algebra.adjoin (ResidueField A) {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hβ,
      IntermediateField.top_toSubalgebra]
  have hsurj : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hadj]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨_, hψβ⟩)
  exact ⟨AdjoinRoot p, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨AlgEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩⟩⟩

end IsLocalRing.FiniteEtaleLocalResidueLift

/-- Over a henselian local ring `Rh`, every finite subextension of a separable extension of the
residue field of `R` has a lift in the universe of `Rh`. -/
@[sga "3 VIA 1.2" "special case", sga "3 XXIV 8.1.2" "more general"]
theorem IsLocalRing.FiniteEtaleLocalResidueLift.nonempty {R : Type u} [CommRing R]
    [IsLocalRing R] {Rh : Type u} [CommRing Rh] [HenselianLocalRing Rh] (Ω : Type w) [Field Ω]
    [Algebra (ResidueField R) Ω]
    [Algebra.IsSeparable (ResidueField R) Ω] (e : ResidueField R ≃+* ResidueField Rh)
    (L : FiniteIntermediateField (ResidueField R) Ω) :
    Nonempty (FiniteEtaleLocalResidueLift.{u, w, u} R Rh Ω e L) := by
  let : Algebra (ResidueField Rh) L :=
    ((algebraMap (ResidueField R) L).comp e.symm.toRingHom).toAlgebra
  let : Algebra (ResidueField R) (ResidueField Rh) := e.toRingHom.toAlgebra
  have : IsScalarTower (ResidueField R) (ResidueField Rh) L :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  have : FiniteDimensional (ResidueField Rh) L :=
    .of_restrictScalars_finite (ResidueField R) (ResidueField Rh) L
  have : Algebra.IsSeparable (ResidueField Rh) L :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField R) (ResidueField Rh) L
  obtain ⟨B, _, _, _, _, _, _, ⟨ε⟩⟩ := FiniteEtaleLocalResidueLift.exists_residueField_algEquiv Rh L
  have := ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u}
    Rh).2.1 B inferInstance).1
  refine ⟨{ carrier := B, residueEquiv := ε.symm.toRingEquiv, residueEquiv_algebraMap := ?_ }⟩
  intro x
  have hx : algebraMap (ResidueField R) L x = algebraMap (ResidueField Rh) L (e x) := by
    simp [RingHom.algebraMap_toAlgebra]
  obtain ⟨r, hr⟩ := residue_surjective (e x)
  rw [hx, ← hr, AlgEquiv.coe_toRingEquiv, ε.symm.commutes, ResidueField.algebraMap_residue,
    ResidueField.map_residue]


section Union

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (G : I → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₐ[R] G j) [DirectedSystem G (fun i j h => (f i j h).toRingHom)]

/-- The structure map from `R` to the union of a directed system of `R`-algebras. -/
private noncomputable def unionAlgebraMap :
    R →+* Ring.DirectLimit G (fun i j h => (f i j h).toRingHom) :=
  (Ring.DirectLimit.of G _ (Classical.arbitrary I)).comp (algebraMap R _)

omit [DirectedSystem G (fun i j h => (f i j h).toRingHom)] in
/-- The stages of the union are compatible with the structure maps from `R`. -/
private theorem of_algebraMap (i : I) (r : R) :
    Ring.DirectLimit.of G (fun i j h => (f i j h).toRingHom) i (algebraMap R (G i) r) =
      unionAlgebraMap G f r := by
  obtain ⟨k, hik, h₀k⟩ := exists_ge_ge i (Classical.arbitrary I)
  rw [unionAlgebraMap, RingHom.comp_apply, ← Ring.DirectLimit.of_f hik,
    ← Ring.DirectLimit.of_f h₀k]
  simp

/-- The union of a directed system of `R`-algebras as an `R`-algebra. -/
private noncomputable abbrev unionAlgebra :
    Algebra R (Ring.DirectLimit G (fun i j h => (f i j h).toRingHom)) :=
  (unionAlgebraMap G f).toAlgebra

attribute [local instance] unionAlgebra

/-- The inclusion of a stage into the union, as an `R`-algebra map. -/
private noncomputable abbrev unionι (i : I) :
    G i →ₐ[R] Ring.DirectLimit G (fun i j h => (f i j h).toRingHom) :=
  { toRingHom := Ring.DirectLimit.of G _ i, commutes' := of_algebraMap G f i }

/-- The directed system as a diagram of `R`-algebras. -/
private noncomputable abbrev unionDiagram : I ⥤ CommAlgCat.{u} R where
  obj i := CommAlgCat.of R (G i)
  map h := CommAlgCat.ofHom (f _ _ (leOfHom h))
  map_id _ := CommAlgCat.hom_ext
    (AlgHom.ext fun a => DirectedSystem.map_self (f := fun i j h => f i j h) a)
  map_comp h h' := CommAlgCat.hom_ext (AlgHom.ext fun a =>
    (DirectedSystem.map_map (f := fun i j h => f i j h) (leOfHom h) (leOfHom h') a).symm)

/-- The union as a cocone over the diagram. -/
private noncomputable abbrev unionCocone : Cocone (unionDiagram G f) where
  pt := CommAlgCat.of R (Ring.DirectLimit G (fun i j h => (f i j h).toRingHom))
  ι.app i := CommAlgCat.ofHom (unionι G f i)
  ι.naturality _ _ h := CommAlgCat.hom_ext (AlgHom.ext fun a => Ring.DirectLimit.of_f (leOfHom h) a)

/-- The legs of the union cocone are the canonical maps into the direct limit. -/
private theorem unionCocone_ι_app_apply (i : I) (a : G i) :
    ((unionCocone G f).ι.app i).hom a =
      Ring.DirectLimit.of G (fun i j h => (f i j h).toRingHom) i a := rfl

/-- The map out of the union induced by a compatible family of `R`-algebra maps. -/
private noncomputable def unionLift {T : Type*} [CommRing T] [Algebra R T]
    (g : ∀ i, G i →ₐ[R] T) (hg : ∀ i j h a, g j (f i j h a) = g i a) :
    Ring.DirectLimit G (fun i j h => (f i j h).toRingHom) →ₐ[R] T :=
  { toRingHom := Ring.DirectLimit.lift G _ T (fun i => (g i).toRingHom) hg
    commutes' := fun r => by
      rw [RingHom.algebraMap_toAlgebra, unionAlgebraMap, RingHom.comp_apply]
      exact (Ring.DirectLimit.lift_of _ _ _ _ _).trans ((g _).commutes r) }

omit [IsDirected I (· ≤ ·)] [DirectedSystem G (fun i j h => (f i j h).toRingHom)] in
/-- The induced map out of the union restricts to the given maps on the stages. -/
private theorem unionLift_of {T : Type*} [CommRing T] [Algebra R T]
    (g : ∀ i, G i →ₐ[R] T) (hg : ∀ i j h a, g j (f i j h a) = g i a) (i : I) (a : G i) :
    unionLift G f g hg (Ring.DirectLimit.of G _ i a) = g i a :=
  Ring.DirectLimit.lift_of (G := G) (P := T) (g := fun i => (g i).toRingHom) (Hg := hg) i a

/-- The union is the colimit of the directed system of `R`-algebras. -/
private noncomputable def isColimitUnionCocone : IsColimit (unionCocone G f) := by
  refine IsColimit.ofExistsUnique fun d => ?_
  have hg (i j : I) (h : i ≤ j) (a : G i) : (d.ι.app j).hom (f i j h a) = (d.ι.app i).hom a :=
    AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (d.w (homOfLE h))) a
  refine ⟨CommAlgCat.ofHom (unionLift G f (fun i => (d.ι.app i).hom) hg), fun i => ?_,
    fun m hm => ?_⟩
  · ext a
    rw [CommAlgCat.hom_comp, AlgHom.comp_apply, unionCocone_ι_app_apply, CommAlgCat.hom_ofHom,
      unionLift_of]
  · ext x
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
    rw [CommAlgCat.hom_ofHom, unionLift_of, ← hm i, CommAlgCat.hom_comp, AlgHom.comp_apply,
      unionCocone_ι_app_apply]

/-- The union of a directed system of étale `R`-algebras is ind-étale. -/
private theorem ind_etale_union [∀ i, Algebra.Etale R (G i)] :
    (CommAlgCat.etale.{u} R).ind.{u}
      (CommAlgCat.of R (Ring.DirectLimit G (fun i j h => (f i j h).toRingHom))) :=
  ⟨I, inferInstance, inferInstance, ⟨unionDiagram G f, (unionCocone G f).ι,
    isColimitUnionCocone G f⟩, fun i => inferInstanceAs (Algebra.Etale R (G i))⟩

end Union

namespace IsLocalRing.FiniteEtaleLocalResidueLift

variable (R : Type u) [CommRing R] [IsLocalRing R] (Rh : Type u) [CommRing Rh]
  [HenselianLocalRing Rh] (Ω : Type u) [Field Ω] [Algebra (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω] (e : ResidueField R ≃+* ResidueField Rh)

/-- A chosen lift `R^h(κ')` of each finite subextension `κ'` of `Ω`. -/
noncomputable def lift (L : FiniteIntermediateField (ResidueField R) Ω) :
    FiniteEtaleLocalResidueLift.{u, u, u} R Rh Ω e L :=
  Classical.choice (nonempty Ω e L)

variable {R Rh Ω e}

/-- The transition map `R^h(κ') → R^h(κ'')` for `κ' ⊆ κ''`: the unique map inducing the inclusion
on residue fields. -/
noncomputable def liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω} (h : L ≤ L') :
    lift R Rh Ω e L →ₐ[Rh] lift R Rh Ω e L' :=
  (existsUnique_algHom _ _ (IntermediateField.inclusion h)).exists.choose

/-- The transition map induces the inclusion `κ' ⊆ κ''` on residue fields. -/
theorem residue_liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω} (h : L ≤ L')
    (a : lift R Rh Ω e L) :
    residue _ (liftMap h a) = residueMap _ _ (IntermediateField.inclusion h) (residue _ a) :=
  (existsUnique_algHom _ _ (IntermediateField.inclusion h)).exists.choose_spec a

/-- The transition map is the only map inducing the inclusion `κ' ⊆ κ''` on residue fields. -/
theorem eq_liftMap_iff {L L' : FiniteIntermediateField (ResidueField R) Ω} (h : L ≤ L')
    (f : lift R Rh Ω e L →ₐ[Rh] lift R Rh Ω e L') :
    f = liftMap h ↔
      ∀ a, residue _ (f a) = residueMap _ _ (IntermediateField.inclusion h) (residue _ a) :=
  ⟨fun hf => hf ▸ residue_liftMap h,
    fun hf => (existsUnique_algHom _ _ _).unique hf (residue_liftMap h)⟩

/-- The transition map for `κ' ⊆ κ'` is the identity. -/
theorem liftMap_refl (L : FiniteIntermediateField (ResidueField R) Ω) :
    liftMap (le_refl L) = AlgHom.id Rh (lift R Rh Ω e L) :=
  ((eq_liftMap_iff (le_refl L) _).mpr fun a => by simp [residueMap]).symm

/-- The transition maps compose. -/
theorem liftMap_comp {L₁ L₂ L₃ : FiniteIntermediateField (ResidueField R) Ω} (h₁₂ : L₁ ≤ L₂)
    (h₂₃ : L₂ ≤ L₃) :
    (liftMap (Rh := Rh) (e := e) h₂₃).comp (liftMap h₁₂) = liftMap (h₁₂.trans h₂₃) :=
  (eq_liftMap_iff (h₁₂.trans h₂₃) _).mpr fun a => by simp [residue_liftMap, residueMap]

/-- The chosen lifts and transition maps form a directed system. -/
instance : DirectedSystem (fun L => lift R Rh Ω e L)
    (fun _ _ h => (liftMap (e := e) h).toRingHom) where
  map_self _ a := AlgHom.congr_fun (liftMap_refl _) a
  map_map _ _ _ h h' a := AlgHom.congr_fun (liftMap_comp h h') a

/-- The transition maps are local. -/
theorem isLocalHom_liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω} (h : L ≤ L') :
    IsLocalHom (liftMap (Rh := Rh) (e := e) h).toRingHom :=
  isLocalHom_of_residue_eq _ _ (residue_liftMap h)

/-- The transition maps are injective. -/
theorem injective_liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω} (h : L ≤ L') :
    Function.Injective (liftMap (Rh := Rh) (e := e) h) :=
  injective_of_residue_eq _ _ _ _ (residue_liftMap h)

end IsLocalRing.FiniteEtaleLocalResidueLift

namespace IsLocalRing.FiniteEtaleLocalResidueLift

variable {R : Type u} [CommRing R] [IsLocalRing R] {Rh : Type u} [CommRing Rh]
  [HenselianLocalRing Rh] {Ω : Type u} [Field Ω] [Algebra (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω] {e : ResidueField R ≃+* ResidueField Rh}

variable (R Rh Ω e) in
/-- The union `⋃ R^h(κ')` of the chosen lifts of the finite subextensions `κ'` of `Ω`. -/
private abbrev union : Type u :=
  Ring.DirectLimit (fun L => lift R Rh Ω e L) (fun _ _ h => (liftMap (e := e) h).toRingHom)

attribute [local instance] unionAlgebra

/-- The union of the lifts is henselian (Lemma 04GI). -/
private theorem henselianLocalRing_union : HenselianLocalRing (union R Rh Ω e) :=
  part2_henselian (fun L => lift R Rh Ω e L) (fun _ _ h => (liftMap h).toRingHom)
    (fun _ _ h => isLocalHom_liftMap h) fun _ => inferInstance

attribute [local instance] henselianLocalRing_union

/-- The stage `R^h(κ')` of the union, as an `Rh`-algebra map. -/
private noncomputable abbrev unionStage (L : FiniteIntermediateField (ResidueField R) Ω) :
    lift R Rh Ω e L →ₐ[Rh] union R Rh Ω e :=
  unionι (fun L => lift R Rh Ω e L) (fun _ _ h => liftMap h) L

/-- The residue map of a stage, as a map to `Ω`. -/
private noncomputable def stageResidue (L : FiniteIntermediateField (ResidueField R) Ω) :
    lift R Rh Ω e L →+* Ω :=
  L.toIntermediateField.val.toRingHom.comp
    ((lift R Rh Ω e L).residueEquiv.symm.toRingHom.comp (residue _))

/-- Unfolding `stageResidue`. -/
private theorem stageResidue_apply (L : FiniteIntermediateField (ResidueField R) Ω)
    (a : lift R Rh Ω e L) :
    stageResidue L a = ((lift R Rh Ω e L).residueEquiv.symm (residue _ a) : Ω) := rfl

/-- The residue maps of the stages are compatible with the transition maps. -/
private theorem stageResidue_liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω}
    (h : L ≤ L') (a : lift R Rh Ω e L) : stageResidue L' (liftMap h a) = stageResidue L a := by
  rw [stageResidue_apply, stageResidue_apply, residue_liftMap, residueMap]
  simp

/-- The residue map of the union, as a surjection onto `Ω`. -/
private noncomputable def unionResidue : union R Rh Ω e →+* Ω :=
  Ring.DirectLimit.lift _ _ Ω stageResidue fun _ _ h a => stageResidue_liftMap h a

/-- The residue map of the union restricts to the residue maps of the stages. -/
private theorem unionResidue_of (L : FiniteIntermediateField (ResidueField R) Ω)
    (a : lift R Rh Ω e L) : unionResidue (unionStage L a) = stageResidue L a :=
  Ring.DirectLimit.lift_of (G := fun L => lift R Rh Ω e L) (P := Ω) (g := stageResidue)
    (Hg := fun _ _ h a => stageResidue_liftMap h a) L a

/-- The residue map of the union is surjective, since `Ω` is algebraic over `κ`. -/
private theorem unionResidue_surjective :
    Function.Surjective (unionResidue (R := R) (Rh := Rh) (Ω := Ω) (e := e)) := by
  intro x
  obtain ⟨L, hx⟩ := FiniteIntermediateField.exists_mem (κ := ResidueField R) x
  obtain ⟨a, ha⟩ := residue_surjective ((lift R Rh Ω e L).residueEquiv ⟨x, hx⟩)
  exact ⟨unionStage L a, by rw [unionResidue_of, stageResidue_apply, ha,
    RingEquiv.symm_apply_apply]⟩

/-- On `Rh`, the residue map of the union is the residue map of `Rh` followed by `e⁻¹`. -/
private theorem unionResidue_algebraMap (r : Rh) :
    unionResidue (algebraMap Rh (union R Rh Ω e) r) =
      algebraMap (ResidueField R) Ω (e.symm (residue Rh r)) := by
  let L₀ : FiniteIntermediateField (ResidueField R) Ω := ⟨⊥⟩
  rw [← (unionStage L₀).commutes r, unionResidue_of, stageResidue_apply]
  have h := (lift R Rh Ω e L₀).residueEquiv_algebraMap (e.symm (residue Rh r))
  rw [RingEquiv.apply_symm_apply, ResidueField.map_residue, ← RingEquiv.eq_symm_apply] at h
  rw [← h, IntermediateField.coe_algebraMap_apply]

/-- The residue map of the union is local, being a surjection onto a field. -/
private instance : IsLocalHom (unionResidue (R := R) (Rh := Rh) (Ω := Ω) (e := e)) :=
  unionResidue_surjective.isLocalHom _

/-- The residue map of the union induces a bijection on the residue field. -/
private theorem bijective_lift_unionResidue :
    Function.Bijective (ResidueField.lift (unionResidue (R := R) (Rh := Rh) (Ω := Ω) (e := e))) :=
  ⟨RingHom.injective _, .of_comp (g := residue _) (by
    simpa [Function.comp_def] using unionResidue_surjective (e := e))⟩

/-- The residue field of the union is `Ω`. -/
private noncomputable def unionResidueFieldEquiv : ResidueField (union R Rh Ω e) ≃+* Ω :=
  RingEquiv.ofBijective _ bijective_lift_unionResidue

/-- The identification of the residue field of the union with `Ω` on residues. -/
private theorem unionResidueFieldEquiv_residue (x : union R Rh Ω e) :
    unionResidueFieldEquiv (residue _ x) = unionResidue x := by
  rw [unionResidueFieldEquiv, RingEquiv.ofBijective_apply, ResidueField.lift_residue_apply]

/-- The stages of the union are compatible with the transition maps. -/
private theorem unionStage_liftMap {L L' : FiniteIntermediateField (ResidueField R) Ω}
    (h : L ≤ L') (a : lift R Rh Ω e L) : unionStage L' (liftMap h a) = unionStage L a :=
  Ring.DirectLimit.of_f (G := fun L => lift R Rh Ω e L)
    (f := fun _ _ h => (liftMap (e := e) h).toRingHom) h a

/-- The stages embed into the union. -/
private theorem stage_injective (L : FiniteIntermediateField (ResidueField R) Ω) :
    Function.Injective (unionStage (e := e) L) :=
  Ring.DirectLimit.of_injective (fun _ _ h => (liftMap h).toRingHom)
    (fun _ _ h => injective_liftMap h) L

/-- The union is ind-étale over `Rh`. -/
private theorem ind_etale_union :
    (CommAlgCat.etale.{u} Rh).ind.{u} (CommAlgCat.of Rh (union R Rh Ω e)) :=
  _root_.ind_etale_union (fun L => lift R Rh Ω e L) (fun _ _ h => liftMap h)

/-- The residue field of the union is separably closed. -/
private theorem isSepClosed_residueField_union [IsSepClosed Ω] :
    IsSepClosed (ResidueField (union R Rh Ω e)) :=
  IsSepClosed.of_ringEquiv unionResidueFieldEquiv

/-- The union is a henselization of `Rh` with residue field `Ω`, the extension `κ(Rh) ⊆ Ω`
being `κ(R) ⊆ Ω` transported along `e`. -/
private theorem isHenselization_union :
    letI : Algebra (ResidueField Rh) Ω :=
      ((algebraMap (ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
    IsHenselization Rh Ω (union R Rh Ω e) :=
  let : Algebra (ResidueField Rh) Ω :=
    ((algebraMap (ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
  IsHenselization.of_ind_etale inferInstance ind_etale_union
    ⟨unionResidueFieldEquiv.symm, fun r => by
      rw [RingEquiv.symm_apply_eq, unionResidueFieldEquiv_residue, unionResidue_algebraMap,
        RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]⟩

end IsLocalRing.FiniteEtaleLocalResidueLift

open CategoryTheory in
/-- A separable algebraic closure of `κ` is one of any field `κ'` identified with `κ`. -/
private theorem isSepClosure_of_ringEquiv {K K' Ω : Type*} [Field K] [Field K'] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] (e : K ≃+* K') :
    letI : Algebra K' Ω := ((algebraMap K Ω).comp e.symm.toRingHom).toAlgebra
    IsSepClosure K' Ω :=
  let : Algebra K' Ω := ((algebraMap K Ω).comp e.symm.toRingHom).toAlgebra
  ⟨IsSepClosure.sep_closed K, .of_equiv_equiv e (RingEquiv.refl Ω)
    (by ext; simp [RingHom.algebraMap_toAlgebra])⟩

attribute [local instance] unionAlgebra
  IsLocalRing.FiniteEtaleLocalResidueLift.henselianLocalRing_union

open CategoryTheory FiniteEtaleLocalResidueLift in
/-- **The strict henselization as a union of finite étale extensions of the henselization**
(Stacks 0BSL). Let `R → Rh` be a henselization of the local ring `R` and let `κsep` be a separable
algebraic closure of the residue field `κ` of `R`, identified with that of `Rh` by `e`. For every
finite subextension `κ ⊆ κ' ⊆ κsep` there is a finite étale local extension `Rh ⊆ Rh(κ')` with
residue field extension `κ ⊆ κ'`, unique up to unique isomorphism; for `κ' ⊆ κ''` there is exactly
one map `Rh(κ') → Rh(κ'')` compatible with `κ' ⊆ κ''`; and the union `Rsh` of the resulting
directed system is strictly henselian, and is a strict henselization of `Rh` and of `R`. -/
@[stacks 0BSL "The rings `R^h(κ')` are local `Rh`-algebras `A κ'` with injective embeddings `ι`
into `Rsh` exhausting it, which is the union of the source. The transition maps are pinned as the
unique maps compatible with the inclusions of residue fields, and each `A κ'` is unique up to a
unique isomorphism inducing the identity of `κ'`. That `Rsh` is the strict henselization is
`IsHenselization` over `Rh` and over `R` with residue field `κsep`."]
theorem IsLocalRing.IsHenselization.exists_strictHenselization_iUnion_finiteEtale
    (R : Type u) [CommRing R] [IsLocalRing R] (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] [IsHenselization R (ResidueField R) Rh] (κsep : Type u) [Field κsep]
    [Algebra (ResidueField R) κsep] [IsSepClosure (ResidueField R) κsep] :
    ∃ e : ResidueField R ≃+* ResidueField Rh,
      (∀ x : R, e (residue R x) = residue Rh (algebraMap R Rh x)) ∧
      letI : Algebra (ResidueField Rh) κsep :=
        ((algebraMap (ResidueField R) κsep).comp e.symm.toRingHom).toAlgebra
      IsSepClosure (ResidueField Rh) κsep ∧
      ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh)
        (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
        (A : ∀ L, FiniteEtaleLocalResidueLift.{u, u, u} R Rh κsep e L)
        (map : ∀ {L L'}, L ≤ L' → A L →ₐ[Rh] A L') (ι : ∀ L, A L →ₐ[Rh] Rsh),
        (∀ L L' (h : L ≤ L') (f : A L →ₐ[Rh] A L'), f = map h ↔
          ∀ a, residue _ (f a) = residueMap (A L) (A L') (IntermediateField.inclusion h)
            (residue _ a)) ∧
        (∀ L, map (le_refl L) = AlgHom.id Rh (A L)) ∧
        (∀ L₁ L₂ L₃ (h₁₂ : L₁ ≤ L₂) (h₂₃ : L₂ ≤ L₃),
          (map h₂₃).comp (map h₁₂) = map (h₁₂.trans h₂₃)) ∧
        (∀ L (B : FiniteEtaleLocalResidueLift.{u, u, t} R Rh κsep e L),
          ∃! f : A L ≃ₐ[Rh] B,
            ∀ a, residue B (f a) = residueMap (A L) B (RingHom.id L) (residue _ a)) ∧
        (∀ L L' (h : L ≤ L') a, ι L' (map h a) = ι L a) ∧
        (∀ L, Function.Injective (ι L)) ∧ (∀ x, ∃ L a, ι L a = x) ∧
        HenselianLocalRing Rsh ∧ IsSepClosed (ResidueField Rsh) ∧
        IsHenselization Rh κsep Rsh ∧ IsHenselization R κsep Rsh := by
  have := IsHenselization.henselian (R := R) (L := ResidueField R) (Rh := Rh)
  have := IsSepClosure.sep_closed (ResidueField R) (K := κsep)
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := ResidueField R)
    (Rh := Rh)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at he
  let : Algebra (ResidueField Rh) κsep :=
    ((algebraMap (ResidueField R) κsep).comp e.symm.toRingHom).toAlgebra
  let : Algebra R (union R Rh κsep e) :=
    ((algebraMap Rh (union R Rh κsep e)).comp (algebraMap R Rh)).toAlgebra
  have : IsScalarTower R Rh (union R Rh κsep e) := .of_algebraMap_eq' rfl
  have hRh := isHenselization_union (R := R) (Rh := Rh) (Ω := κsep) (e := e)
  refine ⟨e, he, isSepClosure_of_ringEquiv e, union R Rh κsep e, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, lift R Rh κsep e, fun h => liftMap h,
    unionStage, fun _ _ h f => eq_liftMap_iff h f, liftMap_refl, fun _ _ _ => liftMap_comp,
    fun L B => existsUnique_algEquiv _ B, fun _ _ h a => unionStage_liftMap h a,
    stage_injective, Ring.DirectLimit.exists_of, inferInstance,
    isSepClosed_residueField_union, hRh, ?_⟩
  refine IsHenselization.of_ind_etale inferInstance
    (CommAlgCat.ind_etale_comp
      (IsHenselization.ind_etale_of_universe_le (R := R) (L := ResidueField R)) ind_etale_union)
    ⟨unionResidueFieldEquiv.symm, fun r => ?_⟩
  rw [RingEquiv.symm_apply_eq, unionResidueFieldEquiv_residue,
    IsScalarTower.algebraMap_apply R Rh, unionResidue_algebraMap, ← he, RingEquiv.symm_apply_apply]
