module

public import StacksFrontier.AlgebraicGeometry.Thickenings.LineBundleLiftObstruction
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.YonedaNondegenerateExt
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.HodgeDuality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison

/-!
# A line bundle with nonzero first Chern class does not extend along every deformation

Let `X` be smooth and proper over a field `k`, equidimensional of dimension `d ≥ 1`, and let `L`
be a line bundle on `X` with nonzero Hodge first Chern class `c₁(L) ∈ H¹(X, Ω_{X/k})`. Then
there is a class `α ∈ Ext^{d-1}(Ω_{X/k}, ω_X)` such that `L` does not extend to any immersion
`X ⟶ X'` over `k` whose Kodaira–Spencer class, the class of the conormal sequence
`0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/k} ⟶ Ω_{X/k} ⟶ 0`, is `α` through an isomorphism
`𝒞_{X/X'} ≅ ω_X`.

For a K3 surface (`d = 2`, `ω_X ≅ 𝒪_X`) and a first-order deformation `X'` over `k[ε]`, the
conormal sheaf is `𝒪_X · ε ≅ 𝒪_X ≅ ω_X`. So `L` does not extend along a first-order
deformation whose Kodaira–Spencer class is `α`. This is the obstruction calculation of
[Stacks, Tag 0D1R].

## Main definitions

* `Stacks.Thickenings.LineBundleLift.firstChernExt`: `c₁(L)` as a class in
  `Ext¹_{𝒪_X}(𝒪_X, Ω_{X/S})`.
* `Stacks.Thickenings.LineBundleLift.kodairaSpencerClass`: the class of the conormal sequence.

## Main results

* `Stacks.Thickenings.LineBundleLift.firstChernExt_comp_kodairaSpencerClass_eq_zero`: a line
  bundle that extends along `i` has `c₁ ∪ KS = 0`.
* `Stacks.Thickenings.LineBundleLift.exists_firstChernExt_comp_ne_zero`: nondegeneracy, from
  Serre duality.
* `Stacks.Thickenings.LineBundleLift.not_extends_of_firstChern_ne_zero`: **the interface of the
  obstruction step of [Stacks, Tag 0D1R]**.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Picard (ofScheme schemePullbackClassHom)

universe u

namespace Stacks.Thickenings.LineBundleLift

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasExtAbelianSheaf

section Classes

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`c₁(L)` as a class of `Ext¹_{𝒪_X}(𝒪_X, Ω_{X/S})`**: the Hodge first Chern class read as an
`Ext` class of abelian sheaves and pulled back along the bijection
`Ext¹_{𝒪_X}(𝒪_X, Ω_{X/S}) ≃ Ext¹_{Ab(X)}(ℤ, Ω_{X/S})`. -/
def firstChernExt (c : ofScheme X) :
    Ext.{u} (Scheme.Modules.unitModule X) (Scheme.Hom.relativeDifferentials f) 1 :=
  (Equiv.ofBijective _
    (Scheme.Modules.extToAbelian_bijective X (Scheme.Hom.relativeDifferentials f) 1)).symm
    (toExt (Scheme.Hom.hodgeFirstChernClass f c))

theorem extToAbelian_firstChernExt (c : ofScheme X) :
    Scheme.Modules.extToAbelian X _ 1 (firstChernExt f c) =
      toExt (Scheme.Hom.hodgeFirstChernClass f c) :=
  (Equiv.ofBijective _ (Scheme.Modules.extToAbelian_bijective X _ 1)).apply_symm_apply _

/-- `firstChernExt f c` vanishes only when the Hodge first Chern class does. -/
theorem firstChernExt_ne_zero {c : ofScheme X} (hc : Scheme.Hom.hodgeFirstChernClass f c ≠ 0) :
    firstChernExt f c ≠ 0 := by
  intro h
  apply hc
  apply toExt_injective
  refine (extToAbelian_firstChernExt f c).symm.trans ?_
  refine (congrArg (Scheme.Modules.extToAbelian X _ 1) h).trans ?_
  exact (map_zero _).trans (map_zero ((extCohomologyOneIso X).hom.app _).hom).symm

end Classes

section Obstruction

variable {X X' S : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ S)

/-- The conormal sheaf `𝒞_{X/X'}` of an immersion, spelled as an object of `X.Modules`. -/
abbrev conormalModule {X X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] : X.Modules :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i

/-- **The Kodaira–Spencer class of an immersion**: the class in
`Ext¹_{𝒪_X}(Ω_{X/S}, 𝒞_{X/X'})` of the conormal sequence
`0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/S} ⟶ Ω_{X/S} ⟶ 0`, for `X` smooth over `S` ([Stacks, Tag 06AA]). -/
def kodairaSpencerClass (hsm : AlgebraicGeometry.Smooth (i ≫ q)) :
    Ext.{u} (Scheme.Hom.relativeDifferentials (i ≫ q))
      (conormalModule i) 1 :=
  (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i q hsm).extClass

/-- **A line bundle that extends along `i` has `c₁ ∪ KS = 0`** in `Ext²_{𝒪_X}(𝒪_X, 𝒞_{X/X'})`. -/
theorem firstChernExt_comp_kodairaSpencerClass_eq_zero (hsm : AlgebraicGeometry.Smooth (i ≫ q))
    (c' : ofScheme X') :
    (firstChernExt (i ≫ q) (schemePullbackClassHom i c')).comp
      (kodairaSpencerClass i q hsm) (show 1 + 1 = 2 from rfl) = 0 := by
  apply (Scheme.Modules.extToAbelian_bijective X _ 2).1
  rw [Scheme.Modules.extToAbelian_comp, extToAbelian_firstChernExt, map_zero]
  exact hodgeFirstChernClass_comp_extClass_eq_zero i q hsm c'

end Obstruction

section Nondegenerate

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [AlgebraicGeometry.Smooth f]

/-- **Nondegeneracy.** For `X` smooth and proper over a field, equidimensional of dimension
`d = e + 1`, and a line bundle with nonzero Hodge first Chern class, there is
`α ∈ Extᵉ(Ω_{X/k}, ω_X)` with `c₁ ∪ α ≠ 0`. -/
theorem exists_firstChernExt_comp_ne_zero (hequi : TopologicalSpace.Equidimensional X) (e : ℕ)
    (hd : topologicalKrullDim X = (e + 1 : ℕ)) (c : ofScheme X)
    (hc : Scheme.Hom.hodgeFirstChernClass f c ≠ 0) :
    ∃ α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (Stacks.Duality.dualizingModule f) e,
      (firstChernExt f c).comp α (add_comm 1 e) ≠ 0 := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials f
  exact Stacks.Duality.exists_ext_comp_ne_zero_of_ne_zero f
    (isCohenMacaulay_of_syntomic_over_field f (syntomic_of_smooth f)) hequi (e + 1) hd
    (Scheme.Hom.relativeDifferentials f) e 1 (add_comm 1 e) (firstChernExt f c)
    (firstChernExt_ne_zero f hc)

/-- The Kodaira–Spencer class of an immersion `i : X ⟶ X'` over `q`, read in
`Ext¹(Ω_{X/k}, 𝒞_{X/X'})` for a fixed structure morphism `f = i ≫ q`. -/
def kodairaSpencerClassOf {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ Spec (.of k))
    (hq : i ≫ q = f) :
    Ext.{u} (Scheme.Hom.relativeDifferentials f)
      (conormalModule i) 1 := by
  subst hq
  exact kodairaSpencerClass i q inferInstance

/-- **The obstruction step of [Stacks, Tag 0D1R].** Let `X` be a smooth proper surface over a
field `k` (equidimensional of dimension `2`), and let `c ∈ Pic(X)` have nonzero Hodge first
Chern class. There is `α ∈ Ext¹(Ω_{X/k}, ω_X)` such that `c` does not extend along any immersion
`i : X ⟶ X'` over `k` whose Kodaira–Spencer class is carried to `α` by an isomorphism
`ψ : 𝒞_{X/X'} ≅ ω_X`. That is, `c` is not the pullback of a Picard class of `X'`. -/
theorem not_extends_of_firstChern_ne_zero (hequi : TopologicalSpace.Equidimensional X)
    (hd : topologicalKrullDim X = (2 : ℕ)) (c : ofScheme X)
    (hc : Scheme.Hom.hodgeFirstChernClass f c ≠ 0) :
    ∃ α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (Stacks.Duality.dualizingModule f) 1,
      ∀ {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ Spec (.of k))
        (hq : i ≫ q = f)
        (ψ : conormalModule i ≅ Stacks.Duality.dualizingModule f),
        (kodairaSpencerClassOf f i q hq).comp (Ext.mk₀ ψ.hom) (add_zero 1) = α →
          ∀ c' : ofScheme X', schemePullbackClassHom i c' ≠ c := by
  obtain ⟨α, hα⟩ := exists_firstChernExt_comp_ne_zero f hequi 1 hd c hc
  refine ⟨α, fun {X'} i _ q hq ψ hKS c' hc' => hα ?_⟩
  subst hq
  subst hc'
  have h0 := firstChernExt_comp_kodairaSpencerClass_eq_zero i q inferInstance c'
  rw [← hKS, ← Ext.comp_assoc_of_third_deg_zero]
  have h1 : (firstChernExt (i ≫ q) (schemePullbackClassHom i c')).comp
      (kodairaSpencerClassOf (i ≫ q) i q rfl) (add_comm 1 1) = 0 := h0
  rw [h1, Ext.zero_comp]

end Nondegenerate

end Stacks.Thickenings.LineBundleLift

end
