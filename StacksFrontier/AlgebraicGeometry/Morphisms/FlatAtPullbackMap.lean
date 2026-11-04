module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StalkIdentityLocalCartier
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness at a point of a product map

Let `A` be a commutative ring, `P`, `B`, `C` schemes over `Spec A` and `h : B ⟶ C` a morphism
over `Spec A`.  The map `1 × h : P ×_A B ⟶ P ×_A C` is flat at a point `p` as soon as `h` is
flat at the second projection of `p`.

## Main results

* `AlgebraicGeometry.flat_stalkMap_pullbackMap_of_flat_stalkMap`.

## Implementation notes

Both local rings are localizations at primes of tensor products of local rings
(`AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct`), after moving
the second presentation along the equalities `pr₁ (m p) = pr₁ p`, `pr₂ (m p) = h (pr₂ p)` of
points (`AlgebraicGeometry.exists_tensor_stalk_transport₂`).  The composite of the presentation
of `𝒪_{P ×_A C, m p}` with the map on local rings is `ψ ∘ (1 ⊗ h^♯)`, which is flat (a base change
of `h^♯`, followed by a localization); flatness over the source then passes to its localization
(`Module.flat_iff_of_isLocalization`).
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- The `A`-algebra structure on a local ring of a scheme over `Spec A`, through the structure
morphism. -/
noncomputable abbrev stalkAlgebraOver {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    Algebra A (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- A ring map out of a tensor product of local rings of two schemes over `Spec A`, exhibiting its
target as a localization at a prime, may be moved along equalities of the two points. -/
lemma exists_tensor_stalk_transport₂ {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (g : Y ⟶ Spec (CommRingCat.of A)) {S : Type u} [CommRing S] [IsLocalRing S] (x₁ x₂ : X)
    (y₁ y₂ : Y) (hx : x₁ = x₂) (hy : y₁ = y₂)
    (ψ : letI := stalkAlgebraOver A f x₁; letI := stalkAlgebraOver A g y₁
      X.presheaf.stalk x₁ ⊗[A] Y.presheaf.stalk y₁ →+* S)
    (hloc : letI := stalkAlgebraOver A f x₁; letI := stalkAlgebraOver A g y₁; letI := ψ.toAlgebra
      IsLocalization.AtPrime S (Ideal.comap ψ (IsLocalRing.maximalIdeal S))) :
    letI := stalkAlgebraOver A f x₁; letI := stalkAlgebraOver A g y₁
    letI := stalkAlgebraOver A f x₂; letI := stalkAlgebraOver A g y₂
    ∃ ψ' : X.presheaf.stalk x₂ ⊗[A] Y.presheaf.stalk y₂ →+* S,
      (∀ a b, ψ' (a ⊗ₜ b) =
        (ψ.comp Algebra.TensorProduct.includeLeftRingHom)
            ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom.hom a) *
          (ψ.comp Algebra.TensorProduct.includeRight.toRingHom)
            ((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom.hom b)) ∧
      (letI := ψ'.toAlgebra;
        IsLocalization.AtPrime S (Ideal.comap ψ' (IsLocalRing.maximalIdeal S))) := by
  subst hx hy
  let := stalkAlgebraOver A f x₁
  let := stalkAlgebraOver A g y₁
  refine ⟨ψ, fun a b => ?_, hloc⟩
  rw [stalkCongr_hom_self, stalkCongr_hom_self]
  exact ringHom_tensorProduct_tmul ψ a b

/-- The map on local rings along the trivial equality of points is the map on local rings. -/
lemma Scheme.Hom.stalkMapOfEq_rfl {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) :
    g.stalkMapOfEq y (g y) rfl = g.stalkMap y := by
  rw [Scheme.Hom.stalkMapOfEq, stalkCongr_hom_self, Category.id_comp]

/-- The map on local rings of `h : B ⟶ C` over `Spec A`, as a map of `A`-algebras. -/
noncomputable def stalkMapAlgHom {B C : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of A))
    (c : C ⟶ Spec (CommRingCat.of A)) (h : B ⟶ C) (hb : h ≫ c = b) (y : B) :
    letI := stalkAlgebraOver A c (h y); letI := stalkAlgebraOver A b y
    C.presheaf.stalk (h y) →ₐ[A] B.presheaf.stalk y :=
  letI := stalkAlgebraOver A c (h y); letI := stalkAlgebraOver A b y
  { toRingHom := (h.stalkMap y).hom
    commutes' r := by
      change ((Scheme.ΓSpecIso (.of A)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (h y) trivial ≫
        h.stalkMap y).hom r = ((Scheme.ΓSpecIso (.of A)).inv ≫ b.appTop ≫
          B.presheaf.germ ⊤ y trivial).hom r
      rw [← Scheme.Hom.stalkMapOfEq_rfl, Scheme.Hom.germ_stalkMapOfEq,
        ← Scheme.Hom.comp_appTop_assoc, hb] }

/-- **A product map `1 × h` is flat at a point where `h` is flat.**  Let `P`, `B`, `C` be schemes
over `Spec A` and `h : B ⟶ C` a morphism over `Spec A`.  If `h` is flat at the second projection
of a point `p` of `P ×_A B`, then `1 × h : P ×_A B ⟶ P ×_A C` is flat at `p`. -/
theorem flat_stalkMap_pullbackMap_of_flat_stalkMap {P B C : Scheme.{u}}
    (a : P ⟶ Spec (CommRingCat.of A)) (b : B ⟶ Spec (CommRingCat.of A))
    (c : C ⟶ Spec (CommRingCat.of A)) (h : B ⟶ C) (hb : h ≫ c = b)
    (p : (pullback a b : Scheme.{u}))
    (hflat : (h.stalkMap (pullback.snd a b p)).hom.Flat) :
    ((pullback.map a b a c (𝟙 P) h (𝟙 _) (by simp) (by simp [hb])).stalkMap p).hom.Flat := by
  let m := pullback.map a b a c (𝟙 P) h (𝟙 _) (by simp) (by simp [hb])
  let q := m p
  let x := pullback.fst a b p
  let y := pullback.snd a b p
  have hmfst : m ≫ pullback.fst a c = pullback.fst a b :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hmsnd : m ≫ pullback.snd a c = pullback.snd a b ≫ h := pullback.lift_snd _ _ _
  have e1 : pullback.fst a c q = x := by
    show (m ≫ pullback.fst a c) p = _
    rw [hmfst]
  have e2 : pullback.snd a c q = h y := by
    show (m ≫ pullback.snd a c) p = _
    rw [hmsnd]
    rfl
  -- the two presentations
  obtain ⟨ψ₁, hψ₁l, hψ₁r, hloc₁⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct A a b p
  obtain ⟨ψ₂, hψ₂l, hψ₂r, hloc₂⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct A a c q
  obtain ⟨ψ₂', hψ₂', hloc₂'⟩ := exists_tensor_stalk_transport₂ A a c _ _ _ _ e1 e2 ψ₂ hloc₂
  let := stalkAlgebraOver A a x
  let := stalkAlgebraOver A b y
  let := stalkAlgebraOver A c (h y)
  let τ := Algebra.TensorProduct.map (AlgHom.id A (P.presheaf.stalk x))
    (stalkMapAlgHom A b c h hb y)
  have hτ : τ.toRingHom.Flat := RingHom.Flat.tensorProductMap (RingHom.Flat.id _) hflat
  -- the square
  have hfst : (pullback.fst a c).stalkMapOfEq q x e1 ≫ m.stalkMap p =
      (pullback.fst a b).stalkMap p := by
    rw [← Scheme.Hom.stalkMapOfEq_rfl m p,
      ← Scheme.Hom.stalkMapOfEq_comp m (pullback.fst a c) p q x rfl e1 e1,
      Scheme.Hom.stalkMapOfEq_congr hmfst p x e1 rfl, Scheme.Hom.stalkMapOfEq_rfl]
  have hsnd : (pullback.snd a c).stalkMapOfEq q (h y) e2 ≫ m.stalkMap p =
      h.stalkMap y ≫ (pullback.snd a b).stalkMap p := by
    have h2 : (pullback.snd a b ≫ h) p = h y := Scheme.Hom.comp_apply _ _ _
    rw [← Scheme.Hom.stalkMapOfEq_rfl m p,
      ← Scheme.Hom.stalkMapOfEq_comp m (pullback.snd a c) p q (h y) rfl e2 e2,
      Scheme.Hom.stalkMapOfEq_congr hmsnd p (h y) e2 h2,
      Scheme.Hom.stalkMapOfEq_comp (pullback.snd a b) h p y (h y) rfl rfl h2,
      Scheme.Hom.stalkMapOfEq_rfl, Scheme.Hom.stalkMapOfEq_rfl]
  have hsq : (m.stalkMap p).hom.comp ψ₂' = ψ₁.comp τ.toRingHom := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      let := stalkAlgebraOver A a (pullback.fst a c q)
      let := stalkAlgebraOver A c (pullback.snd a c q)
      show (m.stalkMap p).hom (ψ₂' (u ⊗ₜ v)) = ψ₁ (u ⊗ₜ (h.stalkMap y).hom v)
      rw [hψ₂', map_mul, ringHom_tensorProduct_tmul ψ₁, hψ₁l, hψ₁r, hψ₂l, hψ₂r]
      congr 1
      · exact congrArg (fun φ => CommRingCat.Hom.hom φ u) hfst
      · exact congrArg (fun φ => CommRingCat.Hom.hom φ v) hsnd
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  -- flatness of the composite, then over the localization
  let : Algebra (P.presheaf.stalk x ⊗[A] B.presheaf.stalk y)
    ((pullback a b : Scheme.{u}).presheaf.stalk p) := ψ₁.toAlgebra
  have hψ₁flat : ψ₁.Flat := IsLocalization.flat _
    (Ideal.comap ψ₁ (IsLocalRing.maximalIdeal _)).primeCompl
  have hcomp : ((m.stalkMap p).hom.comp ψ₂').Flat := hsq ▸ hτ.comp hψ₁flat
  let : Algebra (P.presheaf.stalk x ⊗[A] C.presheaf.stalk (h y))
    ((pullback a c : Scheme.{u}).presheaf.stalk q) := ψ₂'.toAlgebra
  let : Algebra ((pullback a c : Scheme.{u}).presheaf.stalk q)
    ((pullback a b : Scheme.{u}).presheaf.stalk p) := (m.stalkMap p).hom.toAlgebra
  let : Algebra (P.presheaf.stalk x ⊗[A] C.presheaf.stalk (h y))
    ((pullback a b : Scheme.{u}).presheaf.stalk p) := ((m.stalkMap p).hom.comp ψ₂').toAlgebra
  have : IsScalarTower (P.presheaf.stalk x ⊗[A] C.presheaf.stalk (h y))
      ((pullback a c : Scheme.{u}).presheaf.stalk q)
      ((pullback a b : Scheme.{u}).presheaf.stalk p) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Flat (P.presheaf.stalk x ⊗[A] C.presheaf.stalk (h y))
      ((pullback a b : Scheme.{u}).presheaf.stalk p) := hcomp
  exact (Module.flat_iff_of_isLocalization ((pullback a c : Scheme.{u}).presheaf.stalk q)
    (Ideal.comap ψ₂' (IsLocalRing.maximalIdeal _)).primeCompl _).mpr this

end AlgebraicGeometry
