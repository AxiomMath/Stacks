module

public import StacksFrontier.CategoryTheory.Preadditive.Injective.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ObjectwiseChaotic
public import StacksFrontier.RingTheory.Cech.PairCategory

/-!
# Evaluation at an object does not preserve injectives

The proof of [Stacks, Tag 099D] chooses an injective resolution `𝒪 → 𝒥•` of the structure
sheaf on the chaotically topologized category of pairs and asserts that, *because the topology
is chaotic*, the complex of sections `𝒥•(U)` is a resolution of `A` by **injective
`A`-modules** at every object `U = (A, I)`. This file shows that this step is not available:
evaluation at an object of a site does not preserve injective objects, and the failure is
already visible on the category of pairs.

## Where the asserted implication comes from, and why it fails

Evaluation `M ↦ M(U)` on presheaves of modules has a right adjoint, the "cofree" presheaf

```
X ↦ ∏_{p : X ⟶ U} (restriction of scalars of N along 𝒪(p))
```

which is `Stacks.ObjectwiseKFlat.extension` — this file constructs the unit of that adjunction
(`Stacks.ObjectwiseKFlat.extensionLift`) and deduces that the cofree presheaf of an injective
module is an injective presheaf of modules. What "evaluation preserves injectives" would need
is the opposite: a **left** adjoint of evaluation which is exact. The left adjoint exists, but
it is `N ↦ (X ↦ ⨁_{p : U ⟶ X} 𝒪(X) ⊗_{𝒪(U)} N)`: an extension of scalars occurs, so it is
exact only when the rings of sections are flat over `𝒪(U)`. Chaoticity of the topology removes
sheafification from the picture, which is what makes presheaves of modules the right category;
it does nothing about the ring maps.

The obstruction is therefore exactly [Stacks, Tag 03B8]: restriction of scalars along `φ`
preserves injectives if and only if `φ` is flat
(`ModuleCat.flat_iff_restrictScalars_preservesInjectiveObjects`). Evaluating the cofree
presheaf of an injective `𝒪(V)`-module at an object `U` admitting exactly one morphism to `V`
gives back that module, restricted along `𝒪(U) → 𝒪(V)`, so a site carrying a non-flat
restriction map has injective presheaves of modules with non-injective sections.

## Main definitions

* `Stacks.ObjectwiseKFlat.extensionLift` — the morphism `M ⟶ extension R U N` attached to a map
  `M(U) ⟶ N`, i.e. the unit of the adjunction `evaluation ⊣ extension`.

## Main results

* `Stacks.ObjectwiseKFlat.injective_extension` — **the cofree presheaf of an injective module
  is injective.** This is the source of injective objects with computable sections.
* `Stacks.PairSite.flat_of_injective_value` — **the obstruction.** If the values at a pair `P`
  of the injective pair-modules are injective `P.ring`-modules, then every morphism of pairs
  `f : P ⟶ Q` which is the only morphism `P ⟶ Q` has flat underlying ring map.

## Implementation notes

The adjunction `evaluation ⊣ extension` is not constructed as an
`CategoryTheory.Adjunction`: only the unit, its compatibility with morphisms of the source
and the splitting of the counit are needed, and those three are proved here directly. The
counit and its section are already in
`StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/ObjectwiseChaotic.lean`
(`Stacks.ObjectwiseKFlat.extensionProj`, `Stacks.ObjectwiseKFlat.extensionUnit`).

No `@[stacks]` attribute is attached: nothing here is a part of the statement of any tag. It
is a statement about what the proof of tag 099D cannot be formalized by, in the same spirit as
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean`.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 03B8](https://stacks.math.columbia.edu/tag/03B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u₁

namespace Stacks.ObjectwiseKFlat

variable {C : Type u₁} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : Cᵒᵖ)

/-- **The unit of the adjunction `evaluation ⊣ extension`.** A map `ψ : M(U) ⟶ N` of
`R.obj U`-modules extends to a morphism of presheaves of modules `M ⟶ extension R U N`, whose
component at `X` sends a section `m` to the family `(ψ (m|_p))_{p : X ⟶ U}`. -/
def extensionLift {M : PresheafOfModules.{v} R} {N : ModuleCat.{v} (R.obj U)}
    (ψ : M.obj U ⟶ N) : M ⟶ extension R U N where
  app X := ModuleCat.ofHom
    (X := (M.obj X : Type v)) (Y := ExtSections R U N X)
    { toFun := fun m p => ψ (M.restrictₛₗ p m)
      map_add' := fun m m' => funext fun p =>
        (congrArg (fun y : M.obj U => ψ y) (map_add (M.restrictₛₗ p) m m')).trans
          (map_add ψ.hom _ _)
      map_smul' := fun r m => funext fun p =>
        (congrArg (fun y : M.obj U => ψ y) (map_smulₛₗ (M.restrictₛₗ p) r m)).trans
          (ψ.hom.map_smul _ _) }
  naturality {X Y} f := by
    ext m
    exact funext fun q =>
      congrArg (fun y : M.obj U => ψ y) (M.map_comp_apply f q m).symm

/-- The component of `extensionLift R U ψ` at `X` sends a section `m` to the family
`p ↦ ψ (M.map p m)`. -/
@[simp]
theorem extensionLift_app_apply {M : PresheafOfModules.{v} R} {N : ModuleCat.{v} (R.obj U)}
    (ψ : M.obj U ⟶ N) (X : Cᵒᵖ) (m : M.obj X) (p : X ⟶ U) :
    (extensionLift R U ψ).app X m p = ψ (M.map p m) :=
  rfl

/-- **The unit is compatible with morphisms of the source.** -/
theorem comp_extensionLift {M M' : PresheafOfModules.{v} R} {N : ModuleCat.{v} (R.obj U)}
    (f : M ⟶ M') (χ : M'.obj U ⟶ N) :
    f ≫ extensionLift R U χ = extensionLift R U (f.app U ≫ χ) := by
  ext X m
  exact funext fun p =>
    congrArg (fun y : M'.obj U => χ y) (PresheafOfModules.naturality_apply f p m).symm

/-- **The unit splits the counit on the nose.** Every morphism into a cofree presheaf of modules
is the one attached to its own sections at `U`, so the unit of the adjunction is surjective on
morphisms. -/
theorem extensionLift_app_comp_extensionProj {M : PresheafOfModules.{v} R}
    {N : ModuleCat.{v} (R.obj U)} (β : M ⟶ extension R U N) :
    extensionLift R U (β.app U ≫ extensionProj R U N) = β := by
  ext X m
  refine funext fun p => ?_
  exact (congrFun (PresheafOfModules.naturality_apply β p m) (𝟙 U)).trans
    (congrArg (fun q : X ⟶ U => (β.app X m) q) (Category.comp_id p))

/-- **The cofree presheaf of modules on an injective module is injective.** Evaluation at `U` is
exact and is left adjoint to `Stacks.ObjectwiseKFlat.extension`, so the latter preserves
injective objects; only the unit and the counit of that adjunction are used. -/
theorem injective_extension (N : ModuleCat.{v} (R.obj U)) (hN : Injective N) :
    Injective (extension R U N) where
  factors {M M'} g f _ := by
    obtain ⟨χ, hχ⟩ := hN.factors (g.app U ≫ extensionProj R U N) (f.app U)
    refine ⟨extensionLift R U χ, ?_⟩
    rw [comp_extensionLift, hχ, extensionLift_app_comp_extensionProj]

end Stacks.ObjectwiseKFlat

namespace Stacks.PairSite

/-! ### The obstruction on the category of pairs -/

/-- The sections at `P` of the cofree pair-module on a `Q.ring`-module `N`, when `f` is the only
morphism of pairs `P ⟶ Q`: the family indexed by the morphisms `P ⟶ Q` has a single entry, so
evaluation at that entry identifies the sections with `N` read over `P.ring`. -/
def extensionValueEquiv {P Q : Pair.{u}} (f : P ⟶ Q) (hf : ∀ g : P ⟶ Q, g = f)
    (N : ModuleCat.{u} (structureRings.{u}.obj Q.ix)) :
    (ObjectwiseKFlat.extension structureRings.{u} Q.ix N).obj P.ix ≅
      (ModuleCat.restrictScalars (structureRings.{u}.map (Pair.Hom.ix f)).hom).obj N where
  hom := ModuleCat.ofHom
    (X := ObjectwiseKFlat.ExtSections structureRings.{u} Q.ix N P.ix)
    (Y := ((ModuleCat.restrictScalars
      (structureRings.{u}.map (Pair.Hom.ix f)).hom).obj N : Type u))
    { toFun := fun x => x (Pair.Hom.ix f)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  inv := ModuleCat.ofHom
    (X := ((ModuleCat.restrictScalars
      (structureRings.{u}.map (Pair.Hom.ix f)).hom).obj N : Type u))
    (Y := ObjectwiseKFlat.ExtSections structureRings.{u} Q.ix N P.ix)
    { toFun := fun n _ => n
      map_add' := fun _ _ => rfl
      map_smul' := fun r n => funext fun p => by
        obtain rfl : p = Pair.Hom.ix f := by
          obtain rfl := hf p.unop.unop
          rfl
        rfl }
  hom_inv_id := by
    ext x
    refine funext fun p => ?_
    obtain rfl : p = Pair.Hom.ix f := by
      obtain rfl := hf p.unop.unop
      rfl
    rfl
  inv_hom_id := by
    ext n
    rfl

/-- **The obstruction to the injectivity of the sections of an injective pair-module.** If every
injective pair-module has injective sections at `P`, then the underlying ring map of a morphism
of pairs `f : P ⟶ Q` which is the only morphism `P ⟶ Q` is flat.

This is [Stacks, Tag 03B8] applied to the cofree pair-modules: those are injective
(`Stacks.ObjectwiseKFlat.injective_extension`) and their sections at `P` are the restrictions
of scalars along `f`. -/
theorem flat_of_injective_value {P Q : Pair.{u}} (f : P ⟶ Q) (hf : ∀ g : P ⟶ Q, g = f)
    (h : ∀ M : PairModule.{u}, Injective M → Injective (M.value P)) :
    f.toRingHom.Flat := by
  refine (ModuleCat.flat_iff_restrictScalars_preservesInjectiveObjects f.toRingHom).2 ⟨?_⟩
  intro N hN
  exact Injective.of_iso (extensionValueEquiv f hf N)
    (h _ (ObjectwiseKFlat.injective_extension structureRings.{u} Q.ix N hN))

/-! ### The witness: the pairs `(ℤ, 0)` and `(ℤ/2, 0)` -/

/-- `ℤ[x₁, …, xₙ]` in no variables is `ℤ`. -/
def presentationRingZeroEquiv : presentationRing.{u} 0 ≃+* ℤ :=
  (MvPolynomial.isEmptyRingEquiv (ULift.{u} ℤ) (Fin 0)).trans ULift.ringEquiv

/-- **The pair `(ℤ, 0)`**, presented with no variables and no relations. -/
def intPair : Pair.{u} := ⟨0, ⊥, ⊥⟩

/-- **The pair `(ℤ/2, 0)`**, presented with no variables and the single relation `2 = 0`. -/
def twoPair : Pair.{u} := ⟨0, Ideal.span {(2 : presentationRing.{u} 0)}, ⊥⟩

/-- The ring of `intPair` is `ℤ`. -/
def intPairRingEquiv : (intPair.{u}).ring ≃+* ℤ :=
  (Ideal.quotEquivOfEq
      (RingHom.ker_coe_equiv (presentationRingZeroEquiv.{u})).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (presentationRingZeroEquiv.{u} : presentationRing.{u} 0 →+* ℤ))
      presentationRingZeroEquiv.{u}.surjective)

/-- Every element of the ring of `intPair` is an integer: the ring is generated by `1`. -/
theorem intCast_surjective_intPair :
    Function.Surjective ((Int.cast : ℤ → (intPair.{u}).ring)) := fun x => by
  refine ⟨intPairRingEquiv.{u} x, ?_⟩
  have h := map_intCast intPairRingEquiv.{u}.symm (intPairRingEquiv.{u} x)
  rw [Int.cast_id] at h
  rw [← h, RingEquiv.symm_apply_apply]

/-- `2` is a nonzerodivisor in the ring of `intPair`. -/
theorem two_mem_nonZeroDivisors_intPair :
    (2 : (intPair.{u}).ring) ∈ nonZeroDivisors (intPair.{u}).ring := by
  have key : ∀ x : (intPair.{u}).ring, x * 2 = 0 → x = 0 := by
    intro x hx
    have h : intPairRingEquiv.{u} x * 2 = 0 := by
      have := congrArg intPairRingEquiv.{u} hx
      rwa [map_mul, map_ofNat, map_zero] at this
    have hx0 : intPairRingEquiv.{u} x = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (by decide)
    rw [← intPairRingEquiv.{u}.symm_apply_apply x, hx0, map_zero]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rwa [mul_comm]), key⟩

/-- `2` is not invertible in `ℤ[x₁, …, xₙ]` in no variables. -/
theorem not_two_dvd_one_presentationRing : ¬ (2 : presentationRing.{u} 0) ∣ 1 := fun h => by
  have h' := map_dvd (presentationRingZeroEquiv.{u} : presentationRing.{u} 0 →+* ℤ) h
  rw [map_one, map_ofNat] at h'
  exact absurd h' (by decide)

/-- The ring of `twoPair` is not the zero ring: `ℤ/2 ≠ 0`. -/
instance nontrivial_twoPair_ring : Nontrivial (twoPair.{u}).ring := by
  refine Ideal.Quotient.nontrivial_iff.2 fun h => ?_
  rw [Ideal.eq_top_iff_one] at h
  replace h : (1 : presentationRing.{u} 0) ∈ Ideal.span {(2 : presentationRing.{u} 0)} := h
  rw [Ideal.mem_span_singleton] at h
  exact not_two_dvd_one_presentationRing.{u} h

/-- **The reduction `(ℤ, 0) ⟶ (ℤ/2, 0)`**, a morphism of pairs: both ideals are zero, so the
condition `J₀ = I₀ B₀` is `⊥ = ⊥`. -/
def intToTwo : intPair.{u} ⟶ twoPair.{u} where
  toRingHom :=
    Ideal.Quotient.lift (⊥ : Ideal (presentationRing.{u} 0))
      (Ideal.Quotient.mk (Ideal.span {(2 : presentationRing.{u} 0)}))
      (fun a ha => by
        obtain rfl : a = 0 := by simpa using ha
        exact map_zero _)
  map_ideal := (Ideal.map_bot).symm

/-- **The reduction is the only morphism of pairs `(ℤ, 0) ⟶ (ℤ/2, 0)`**: the source ring is
generated by `1`, so it admits exactly one ring map to any ring. -/
theorem eq_intToTwo (g : intPair.{u} ⟶ twoPair.{u}) : g = intToTwo.{u} :=
  Pair.Hom.ext' (RingHom.ext fun x => by
    obtain ⟨n, rfl⟩ := intCast_surjective_intPair.{u} x
    rw [map_intCast, map_intCast])

/-- **The reduction is not flat**: `2` is a nonzerodivisor on `ℤ` and kills `ℤ/2`. -/
theorem not_flat_intToTwo : ¬ (intToTwo.{u}).toRingHom.Flat := by
  intro hflat
  let : Algebra (intPair.{u}).ring (twoPair.{u}).ring := (intToTwo.{u}).toRingHom.toAlgebra
  have : Module.Flat (intPair.{u}).ring (twoPair.{u}).ring := hflat
  have h2 : IsSMulRegular (twoPair.{u}).ring (2 : (intPair.{u}).ring) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors two_mem_nonZeroDivisors_intPair.{u}
  have hmap : (intToTwo.{u}).toRingHom 2 = 0 := by
    rw [show (2 : (intPair.{u}).ring) =
      Ideal.Quotient.mk (⊥ : Ideal (presentationRing.{u} 0)) 2 from (map_ofNat _ 2).symm]
    change Ideal.Quotient.mk (Ideal.span {(2 : presentationRing.{u} 0)}) 2 = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hz : (2 : (intPair.{u}).ring) • (1 : (twoPair.{u}).ring) =
      (2 : (intPair.{u}).ring) • (0 : (twoPair.{u}).ring) := by
    rw [smul_zero, Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, hmap]
  exact one_ne_zero (h2 hz)

/-- **Evaluation at a pair does not preserve injective objects.** There are a presented pair and
an injective presheaf of modules on the category of pairs whose module of sections at that pair
is not injective.

This refutes the step of the proof of [Stacks, Tag 099D] that reads "since the topology in `𝒞₀`
is chaotic, the value `𝒥•(U)` is a resolution of `A` by injective `A`-modules": the terms of an
injective resolution `𝒪 → 𝒥•` of the structure presheaf need not have injective sections, so
the sections cannot be recognized as an injective resolution of `A` on those grounds. The
witness is the reduction `(ℤ, 0) ⟶ (ℤ/2, 0)`, which is the only morphism between those two
pairs and is not flat, together with [Stacks, Tag 03B8]. -/
theorem exists_injective_not_injective_value :
    ∃ (P : Pair.{u}) (M : PairModule.{u}), Injective M ∧ ¬ Injective (M.value P) := by
  by_contra h
  push Not at h
  exact not_flat_intToTwo.{u}
    (flat_of_injective_value intToTwo.{u} eq_intToTwo.{u} fun M hM => h intPair.{u} M hM)

end Stacks.PairSite

end
