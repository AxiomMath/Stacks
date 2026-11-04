module

public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Criterion

/-!
# Multiplicativity and the fixing hypothesis from a pointwise description

Let `α` be a family of endomorphisms of the twists `𝒪(n)` on an absolute `Proj` which acts on
sections by applying, at each point, one ring homomorphism of the fibre there, the same in every
degree and over every open. Then `α` satisfies
`Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative`, and it fixes the homogeneous global
sections as soon as its fibre homomorphisms fix the constant fractions `c / 1`. These are the two
hypotheses of `Stacks.AlgebraicGeometry.TwistRigidity.eq_id` and of its relative form
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMultiplicative.isMultiplicative_of_fibreHom`: a family described
  pointwise by ring homomorphisms of the fibres is multiplicative.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.fixesDegreeSections_of_fibreHom`: such a family
  fixes the homogeneous global sections as soon as its fibre homomorphisms fix `c / 1`.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.fixesResDegreeSections_of_fibreHom`: the relative
  form, with `c` ranging over the images of a graded ring homomorphism.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.eq_id_of_fibreHom`: a family described pointwise by
  ring homomorphisms of the fibres fixing the constant fractions coming from a generating graded
  ring homomorphism is the identity.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.absoluteTwistProduct_apply_comm`: the canonical
  product of two local sections of the twists is commutative on values.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistRigidity

namespace Stacks.AlgebraicGeometry.ThetaMultiplicative

universe u w u' w'

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Commutativity of the canonical product, on values -/

/-- The canonical product of two local sections of the twists is commutative on values: the
products `a * b` and `b * a`, sections of the twists indexed by `i + j` and by `j + i`, have the
same value at every point. -/
public theorem absoluteTwistProduct_apply_comm (i j : ℤ)
    (V : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 i).val.obj (op V))
    (b : (twistingSheaf 𝒜 j).val.obj (op V)) (x : V) :
    (absoluteTwistProduct 𝒜 i j V a b).1 x = (absoluteTwistProduct 𝒜 j i V b a).1 x :=
  ((absoluteTwistProduct_apply 𝒜 i j V a b x).trans (mul_comm (a.1 x) (b.1 x))).trans
    (absoluteTwistProduct_apply 𝒜 j i V b a x).symm

variable {𝒜}

/-- If the fibre homomorphisms fix the constant fraction `c / 1` at every point, the family fixes
the homogeneous global section `degreeSection 𝒜 k c`. -/
private theorem app_degreeSection_eq_of_fibreHom
    {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}
    (φ : ∀ x : ProjectiveSpectrum.top 𝒜, ModuleFiber (M := S) 𝒜 x →+* ModuleFiber (M := S) 𝒜 x)
    (hα : ∀ (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
      (s : (twistingSheaf 𝒜 n).val.obj (op V)) (x : V),
      ((α n).val.app (op V) s).1 x = φ x.1 (s.1 x))
    (k : ℕ) (c : 𝒜 k)
    (hc : ∀ x : ProjectiveSpectrum.top 𝒜,
      φ x (LocalizedModule.mk (c : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) =
        LocalizedModule.mk (c : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) :
    (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k c) = degreeSection 𝒜 k c := by
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans (hα (k : ℤ) ⊤ (degreeSection 𝒜 k c) x) ?_
  refine Eq.trans (congrArg (φ x.1) (degreeSection_apply 𝒜 k c x)) ?_
  exact (hc x.1).trans (degreeSection_apply 𝒜 k c x).symm

/-- A family of twist endomorphisms given pointwise by ring homomorphisms of the fibres is
multiplicative: if in every integer degree, over every open and on every section, the value of the
image at a point is the image of the value under one ring homomorphism of the localization at that
point, then the family is multiplicative. -/
public theorem isMultiplicative_of_fibreHom
    {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}
    (φ : ∀ x : ProjectiveSpectrum.top 𝒜, ModuleFiber (M := S) 𝒜 x →+* ModuleFiber (M := S) 𝒜 x)
    (hα : ∀ (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
      (s : (twistingSheaf 𝒜 n).val.obj (op V)) (x : V),
      ((α n).val.app (op V) s).1 x = φ x.1 (s.1 x)) :
    IsMultiplicative α := by
  intro i j V a b
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans (hα (i + j) V (absoluteTwistProduct 𝒜 i j V a b) x) ?_
  refine Eq.trans (congrArg (φ x.1) (absoluteTwistProduct_apply 𝒜 i j V a b x)) ?_
  refine Eq.trans (map_mul (φ x.1) (a.1 x) (b.1 x)) ?_
  refine Eq.trans (congrArg₂ (· * ·) (hα i V a x).symm (hα j V b x).symm) ?_
  exact (absoluteTwistProduct_apply 𝒜 i j V ((α i).val.app (op V) a)
    ((α j).val.app (op V) b) x).symm

/-- A family of twist endomorphisms given pointwise by ring homomorphisms of the fibres fixes the
homogeneous global sections as soon as its fibre homomorphisms fix the constant fractions `c / 1`.
-/
public theorem fixesDegreeSections_of_fibreHom
    {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}
    (φ : ∀ x : ProjectiveSpectrum.top 𝒜, ModuleFiber (M := S) 𝒜 x →+* ModuleFiber (M := S) 𝒜 x)
    (hα : ∀ (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
      (s : (twistingSheaf 𝒜 n).val.obj (op V)) (x : V),
      ((α n).val.app (op V) s).1 x = φ x.1 (s.1 x))
    (hfix : ∀ (k : ℕ) (c : 𝒜 k) (x : ProjectiveSpectrum.top 𝒜),
      φ x (LocalizedModule.mk (c : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) =
        LocalizedModule.mk (c : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) :
    FixesDegreeSections α :=
  fun k c => app_degreeSection_eq_of_fibreHom φ hα k c (hfix k c)

section Relative

variable {R' : Type u'} {σ' : Type w'} [CommRing R'] [SetLike σ' R'] [AddSubgroupClass σ' R']
  {ℬ : ℕ → σ'} [GradedRing ℬ]

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- A family of twist endomorphisms given pointwise by ring homomorphisms of the fibres fixes the
homogeneous global sections attached to the images of a graded ring homomorphism `ψ`, as soon as
its fibre homomorphisms fix the constant fractions `ψ c / 1`. -/
public theorem fixesResDegreeSections_of_fibreHom
    {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n} (ψ : ℬ →+*ᵍ 𝒜)
    (φ : ∀ x : ProjectiveSpectrum.top 𝒜, ModuleFiber (M := S) 𝒜 x →+* ModuleFiber (M := S) 𝒜 x)
    (hα : ∀ (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
      (s : (twistingSheaf 𝒜 n).val.obj (op V)) (x : V),
      ((α n).val.app (op V) s).1 x = φ x.1 (s.1 x))
    (hfix : ∀ (k : ℕ) (c : ℬ k) (x : ProjectiveSpectrum.top 𝒜),
      φ x (LocalizedModule.mk (ψ (c : R')) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) =
        LocalizedModule.mk (ψ (c : R')) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) :
    RelativeTwistRigidity.FixesResDegreeSections ψ α :=
  fun k c => app_degreeSection_eq_of_fibreHom φ hα k ⟨ψ c, ψ.map_mem c.2⟩ (hfix k c)

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- A family of twist endomorphisms given pointwise by ring homomorphisms of the fibres which fix
the constant fractions `ψ c / 1`, for a graded ring homomorphism `ψ` satisfying
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.Generates`, is the identity. -/
public theorem eq_id_of_fibreHom
    {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n} {ψ : ℬ →+*ᵍ 𝒜}
    (φ : ∀ x : ProjectiveSpectrum.top 𝒜, ModuleFiber (M := S) 𝒜 x →+* ModuleFiber (M := S) 𝒜 x)
    (hα : ∀ (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
      (s : (twistingSheaf 𝒜 n).val.obj (op V)) (x : V),
      ((α n).val.app (op V) s).1 x = φ x.1 (s.1 x))
    (hgen : RelativeTwistRigidity.Generates ψ)
    (hfix : ∀ (k : ℕ) (c : ℬ k) (x : ProjectiveSpectrum.top 𝒜),
      φ x (LocalizedModule.mk (ψ (c : R')) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) =
        LocalizedModule.mk (ψ (c : R')) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl))
    (n : ℤ) : α n = 𝟙 (twistingSheaf 𝒜 n) :=
  RelativeTwistRigidity.eq_id (isMultiplicative_of_fibreHom φ hα) hgen
    (fixesResDegreeSections_of_fibreHom ψ φ hα hfix) n

end Relative

end Stacks.AlgebraicGeometry.ThetaMultiplicative

end
