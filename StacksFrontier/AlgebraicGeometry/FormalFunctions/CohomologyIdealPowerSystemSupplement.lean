module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPower.ReesSystemGeneration
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
public import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `CohomologyIdealPowerSystem`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem` that need imports beyond
those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules)

/-- **Multiplication commutes with the transition maps**: including `Iᵐℱ` into `Iᵐ'ℱ` and then
multiplying by `a ∈ Iᵏ` into `Iᵏ⁺ᵐ'ℱ` is multiplying `Iᵐℱ` into `Iᵏ⁺ᵐ'ℱ` directly. This is the
commutativity of the square `Iᵏ ⊗ Iᵐℱ → Iᵏ⁺ᵐℱ`, `Iᵏ ⊗ Iᵐ'ℱ → Iᵏ⁺ᵐ'ℱ` that
[Stacks, Tag 02OA] records before proving its parts (1), (2), (4) and (5). -/
theorem idealPowerMultipleMap_comp_idealPowerSmul_refl {k m m' : ℕ} (h : m' ≤ m)
    (hm : k + m' ≤ k + m) (a : A) (ha : a ∈ I ^ k) :
    idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫
        idealPowerSmul I X F (le_refl (k + m')) a ha =
      idealPowerSmul I X F hm a ha := by
  refine cancel_sheafSubmodule_ι _ _ _ ?_
  have s2 : idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫
        (idealPowerSmul I X F (le_refl (k + m')) a ha ≫ (idealPowerSub I X F (k + m')).ι) =
      idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫
        ((idealPowerSub I X F m').ι ≫ (a • 𝟙 F)) :=
    congrArg (fun ψ : idealPowerMod I X F m' ⟶ F ↦
        idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫ ψ)
      (idealPowerSmul_comp_ι I X F (le_refl (k + m')) a ha)
  have s4 : (idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫
        (idealPowerSub I X F m').ι) ≫ (a • 𝟙 F) =
      (idealPowerSub I X F m).ι ≫ (a • 𝟙 F) :=
    congrArg (fun ψ : idealPowerMod I X F m ⟶ F ↦ ψ ≫ (a • 𝟙 F))
      (idealPowerMultipleMap_comp_ι (baseIdealSheaf A I X.hom) F h)
  exact (Category.assoc _ _ _).trans (s2.trans ((Category.assoc _ _ _).symm.trans
    (s4.trans (idealPowerSmul_comp_ι I X F hm a ha).symm)))

variable (p : ℕ)

/-- If `f ≫ g = h` then `Hᵖ(g)` applied to `Hᵖ(f) y` is `Hᵖ(h) y`. -/
private theorem cohomologyFunctor_map_apply_map_eq {M N P : X.left.Modules} {f : M ⟶ N}
    {g : N ⟶ P} {h : M ⟶ P} (e : f ≫ g = h) (y : (cohomologyFunctor X p).obj M) :
    ((cohomologyFunctor X p).map g).hom (((cohomologyFunctor X p).map f).hom y) =
      ((cohomologyFunctor X p).map h).hom y := by
  rw [cohomologyFunctor_map_comp_apply, e]

/-- The transition map of `cohomologyIdealPowerSystem` is `Hᵖ` of the inclusion of one member of
the filtration into another. -/
theorem tr_cohomologyIdealPowerSystem {m n : ℕ} (h : m ≤ n)
    (y : cohomologyIdealPower I X F p n) :
    (cohomologyIdealPowerSystem I X F p).tr h y =
      ((cohomologyFunctor X p).map
        (idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h)).hom y :=
  rfl

/-- The multiplication map of `cohomologyIdealPowerSystem`, with its coefficient read in `Iᵏ`
itself, is `Hᵖ` of multiplication by that element. -/
theorem smulOf_cohomologyIdealPowerSystem {k n : ℕ} (a : ↥(I ^ k))
    (y : cohomologyIdealPower I X F p n) :
    (cohomologyIdealPowerSystem I X F p).smulOf k n a y =
      ((cohomologyFunctor X p).map
        (idealPowerSmul I X F (le_refl (k + n)) (a : A) a.2)).hom y :=
  rfl

/-- **The multiplication maps of `n ↦ Hᵖ(X, Iⁿℱ)` are compatible with its transition maps.**

Both laws are `Hᵖ` of an identity between morphisms of sheaves of modules: the first is
`idealPowerMultipleMap_comp_idealPowerSmul_refl` together with
`idealPowerSmul_comp_idealPowerMultipleMap`, the second is `idealPowerSmul_self` together with
the `A`-linearity of cohomology. They are what the remaining clauses of [Stacks, Tag 02OA] use
beyond the laws already carried by `cohomologyIdealPowerSystem`. -/
theorem isFiltrationCompatible_cohomologyIdealPowerSystem :
    Stacks.RingTheory.ReesSystem.IsFiltrationCompatible
      (cohomologyIdealPowerSystem I X F p) where
  tr_smulOf k m m' h a y := by
    have e1 : idealPowerSmul I X F (le_refl (k + m)) (a : A) a.2 ≫
        idealPowerMultipleMap (baseIdealSheaf A I X.hom) F (Nat.add_le_add_left h k) =
          idealPowerSmul I X F (Nat.add_le_add_left h k) (a : A) a.2 :=
      idealPowerSmul_comp_idealPowerMultipleMap I X F _ _ _ _ _
    have e2 : idealPowerMultipleMap (baseIdealSheaf A I X.hom) F h ≫
        idealPowerSmul I X F (le_refl (k + m')) (a : A) a.2 =
          idealPowerSmul I X F (Nat.add_le_add_left h k) (a : A) a.2 :=
      idealPowerMultipleMap_comp_idealPowerSmul_refl I X F h _ _ _
    exact (cohomologyFunctor_map_apply_map_eq X p e1 y).trans
      (cohomologyFunctor_map_apply_map_eq X p e2 y).symm
  tr_smulOf_self k n a y := by
    have e1 : idealPowerSmul I X F (le_refl (k + n)) (a : A) a.2 ≫
        idealPowerMultipleMap (baseIdealSheaf A I X.hom) F (Nat.le_add_left n k) =
          idealPowerSmul I X F (Nat.le_add_left n k) (a : A) a.2 :=
      idealPowerSmul_comp_idealPowerMultipleMap I X F _ _ _ _ _
    have e2 : idealPowerSmul I X F (Nat.le_add_left n k) (a : A) a.2 =
        (a : A) • 𝟙 (idealPowerMod I X F n) :=
      idealPowerSmul_self I X F _ _ _
    exact (cohomologyFunctor_map_apply_map_eq X p (e1.trans e2) y).trans
      (cohomologyFunctor_map_smul_id_apply X p (a : A) y)

/-- **`IⁿHᵖ(X, ℱ)` lies in the image of `Hᵖ(X, Iⁿℱ) → Hᵖ(X, ℱ)`**: a multiple `a · ξ` with
`a ∈ Iⁿ` is the image of `ξ` under `Hᵖ` of multiplication by `a`, read as a morphism
`ℱ ⟶ Iⁿℱ`. This is what makes the comparison maps of [Stacks, Tag 02OA] part (4) definable. -/
theorem pow_smul_le_range_cohomologyProj (n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomology X F p)) ≤
      LinearMap.range (cohomologyProj I X F p n) := by
  refine Submodule.smul_le.2 fun a ha ξ _ ↦ ?_
  refine ⟨((cohomologyFunctor X p).map (idealPowerSmulTop I X F (le_refl n) a ha)).hom ξ, ?_⟩
  have e : idealPowerSmulTop I X F (le_refl n) a ha ≫ (idealPowerSub I X F n).ι =
      a • 𝟙 F := idealPowerSmulTop_comp_ι I X F (le_refl n) a ha
  exact (cohomologyFunctor_map_apply_map_eq X p e ξ).trans
    (cohomologyFunctor_map_smul_id_apply X p a ξ)

/-- **[Stacks, Tag 02OA], parts (1), (2), (3) and (4).**

For `A` Noetherian, `f : X → Spec A` proper and `ℱ` coherent there is one integer `c ≥ 0` such
that

* the image of `Hᵖ(X, Iʳℱ) → Hᵖ(X, ℱ)` is contained in `Iʳ⁻ᶜHᵖ(X, ℱ)` for `r ≥ c` -- this is
  part (2) of the source at `n = 0`, where its `e = max(0, c - n)` is `c`;
* `Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, ℱ)) = Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, Iᵐℱ))` whenever `m + c ≤ k` -- this is
  part (3) of the source, which is the case `m = k - c`;
* the multiplication map `Iʳ ⊗_A Hᵖ(X, Iᶜℱ) → Hᵖ(X, Iʳ⁺ᶜℱ)` is surjective for every `r` -- this
  is part (1) of the source, whose `n ≥ c` is this `r = n - c`; and
* the image of `Hᵖ(X, Iᵐ⁺ⁿℱ) → Hᵖ(X, Iⁿℱ)` is contained in `Iᵐ⁻ᵉHᵖ(X, Iⁿℱ)` with
  `e = max(0, c - n)` whenever `m + n ≥ c` -- this is part (2) of the source in every degree
  `n`, the truncated difference `m - (c - n)` being its `m - e`; and
* for every `r` there is a map `ν : Iʳ⁺ᶜHᵖ(X, ℱ) → Hᵖ(X, Iʳℱ)` with `Hᵖ(X, Iʳℱ) → Hᵖ(X, ℱ)`
  carrying `ν η` back to `η`, and with `ν` applied to the image of a class of
  `Hᵖ(X, Iʳ⁺²ᶜℱ)` returning the image of that class in `Hᵖ(X, Iʳℱ)` -- this is part (4) of the
  source at `n = r + c`, its two displayed composites being exactly these two identities: the
  first says that `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ) → Iⁿ⁻²ᶜHᵖ(X, ℱ)` is the canonical inclusion, the
  second that `Hᵖ(X, Iⁿℱ) → Iⁿ⁻ᶜHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻²ᶜℱ)` is the canonical map.

Part (5) of the source -- the pro-isomorphism of the inverse systems `(Hᵖ(X, Iⁿℱ))` and
`(IⁿHᵖ(X, ℱ))` -- is the other registration of the tag,
`Stacks.Cohomology.FormalFunctions.proIso_cohomologyIdealPower`. It is deduced from the clauses
above exactly as the source deduces it: the two families of maps a pro-isomorphism asks for are
the projections of part (2) at degree `0` and the comparison maps of part (4), and its two
round trips are the two composites of part (4).

The clauses about the transition maps *between* the members of the filtration rest on
`isFiltrationCompatible_cohomologyIdealPowerSystem`, the compatibility of the multiplication
maps with those transition maps; `Stacks.RingTheory.IdealPowerSystem` deliberately does not
assume it, so it is supplied for this system and consumed by
`Stacks.RingTheory.ReesSystem.exists_uniform_bound_mul`. The comparison maps rest in addition
on `pow_smul_le_range_cohomologyProj`, which is the surjection `Iⁿ ⊗ Hᵖ(X, ℱ) → IⁿHᵖ(X, ℱ)`
of the source's diagram read as a statement about the image of `Hᵖ(X, Iⁿℱ) → Hᵖ(X, ℱ)`.

The hypothesis `h02O8` is [Stacks, Tag 02O8] -- a *different* Stacks tag, absent from this
branch -- carried in general form: it is quantified over every Noetherian base ring, every
ideal of it, every proper scheme over it, every coherent module and every degree, and is
instantiated inside the proof at the data of this statement. See `IsCohomologyReesFinite` for
why it is absent and what is new about its being statable.

Cf. Stacks Tag 02OA; not registered because it carries the hypothesis `h02O8`, the Rees finiteness
of Stacks Tag 02O8 for every coherent module on every proper scheme over a Noetherian ring. -/
theorem exists_uniform_bound_cohomology_surjective_range_le [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) (hF : SheafOfModules.IsCoherent F) (p : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    ∃ c : ℕ,
      (∀ r : ℕ, c ≤ r → LinearMap.range (cohomologyProj I X F p r) ≤
        I ^ (r - c) • (⊤ : Submodule A (cohomology X F p))) ∧
      (∀ (m k : ℕ) (hmk : m + c ≤ k),
        LinearMap.ker (cohomologyProj I X F p k) =
          LinearMap.ker (cohomologyTr I X F p
            (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) ∧
      (∀ r : ℕ, Function.Surjective
        (TensorProduct.lift ((cohomologyIdealPowerSystem I X F p).smulOf r c))) ∧
      (∀ n m : ℕ, c ≤ m + n →
        LinearMap.range (cohomologyTr I X F p (Nat.le_add_left n m)) ≤
          I ^ (m - (c - n)) • (⊤ : Submodule A (cohomologyIdealPower I X F p n))) ∧
      (∀ r : ℕ, ∃ ν : ↥(I ^ (r + c) • (⊤ : Submodule A (cohomology X F p))) →ₗ[A]
          cohomologyIdealPower I X F p r,
        (∀ η : ↥(I ^ (r + c) • (⊤ : Submodule A (cohomology X F p))),
          cohomologyProj I X F p r (ν η) = (η : cohomology X F p)) ∧
        (∀ (z : cohomologyIdealPower I X F p (r + c + c))
            (hz : cohomologyProj I X F p (r + c + c) z ∈
              I ^ (r + c) • (⊤ : Submodule A (cohomology X F p))),
          ν ⟨cohomologyProj I X F p (r + c + c) z, hz⟩ =
            cohomologyTr I X F p
              ((Nat.le_add_right r c).trans (Nat.le_add_right (r + c) c)) z)) := by
  have hfin : (cohomologyIdealPowerSystem I X F p).IsReesFinite := h02O8 A I X hX F hF p
  obtain ⟨c, hsurj, himage, hproj, hker, hcomparison⟩ :=
    (cohomologyIdealPowerSystem I X F p).exists_uniform_bound_mul
      (isFiltrationCompatible_cohomologyIdealPowerSystem I X F p)
      (pow_smul_le_range_cohomologyProj I X F p) hfin
  exact ⟨c, hproj, hker, hsurj, himage, hcomparison⟩

end Stacks.Cohomology.FormalFunctions

end
