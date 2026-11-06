module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# Exterior powers of an extension by an invertible module

Let `X` be a scheme and let `0 ⟶ ℒ ⟶ ℰ ⟶ 𝒬 ⟶ 0` be a short exact sequence of `𝒪_X`-modules
with `ℒ` finite locally free of rank one and `𝒬` finite locally free of rank `m`. For every
`k ≥ 0` the exterior powers of degree `k + 2` then sit in a short exact sequence

  `0 ⟶ ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬 ⟶ 0`,

whose second arrow is `⋀^{k+2}` of `ℰ ⟶ 𝒬` and whose first arrow sends `l ⊗ (q₀ ∧ ⋯ ∧ q_k)` to
`l ∧ q̃₀ ∧ ⋯ ∧ q̃_k` for local lifts `q̃ᵢ` of the `qᵢ`. Locally `ℰ ≅ ℒ ⊕ 𝒬` and this is the
decomposition `⋀^{k+2}(ℒ ⊕ 𝒬) = (ℒ ⊗ ⋀^{k+1} 𝒬) ⊕ ⋀^{k+2} 𝒬`, the higher exterior powers of `ℒ`
vanishing.

## Main definitions

* `Stacks.SheafOfModules.TopWedge.lineWedge`: the first arrow `ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ`, for
  an exact sequence `ℒ ⟶ ℰ ⟶ 𝒬 ⟶ 0` of sheaves of modules on a ringed space with `ℒ` of rank
  one.
* `Stacks.SheafOfModules.TopWedge.lineWedgeComplex`: the sequence
  `ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬`.
* `AlgebraicGeometry.Scheme.Modules.ofSiteModules` and
  `AlgebraicGeometry.Scheme.Modules.ofSiteModulesEquivalence`: the identity functor, an
  equivalence, from sheaves of modules over the spelling `Sheaf.toRingCat` of the structure sheaf
  of a scheme, in which exterior algebras are developed, to `X.Modules`.

## Main results

* `Stacks.SheafOfModules.TopWedge.relComplex_f_eq_lineWedge`: the presentation of
  [Stacks, Tag 01CJ] in degree `k + 2` factors through the first arrow.
* `Stacks.SheafOfModules.TopWedge.lineWedgeComplex_exact` and
  `Stacks.SheafOfModules.TopWedge.epi_extHom_app`: exactness in the middle and on the right.
* `AlgebraicGeometry.Scheme.Modules.exists_shortExact_exteriorPower_of_rank_one`: **the
  sequence `0 ⟶ ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬 ⟶ 0` is short exact** on a scheme, for
  `𝒬` finite locally free of constant rank.

## Implementation notes

The first arrow is the descent of the wedge map `ℒ ⊗ ⋀^{k+1} ℰ ⟶ ⋀^{k+2} ℰ` along the
presentation `ℒ ⊗ ⋀^k ℰ ⟶ ⋀^{k+1} ℰ ⟶ ⋀^{k+1} 𝒬 ⟶ 0` of [Stacks, Tag 01CJ] tensored with `ℒ`,
`Stacks.SheafOfModules.TopWedge.detComparisonFrom`; it descends because `⋀² ℒ = 0`. The
presentation of Tag 01CJ in degree `k + 2` then factors through it, which gives exactness in the
middle and surjectivity on the right. Injectivity on the left is a count of ranks: the first
arrow maps onto the kernel of the second, a finite locally free module of rank
`binom(m + 1, k + 2) - binom(m, k + 2) = binom(m, k + 1)`, which is the rank of
`ℒ ⊗ ⋀^{k+1} 𝒬`, and an epimorphism between finite locally free modules of the same rank is an
isomorphism ([Stacks, Tag 089Q]).

The short exact sequence on a scheme is stated as an existence, with the three terms identified
up to isomorphism, because the sequence is built in the category of sheaves of modules over
`Sheaf.toRingCat` and carried to `X.Modules` along
`AlgebraicGeometry.Scheme.Modules.ofSiteModules`. The two categories are the same up to
unfolding, but comparing composites and zero morphisms across them is expensive for the kernel,
so the comparison is made once, by the functor.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {L E Q : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AL : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) L)
  (AE : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E)
  (AQ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) Q)
  (f : L ⟶ E) (g : E ⟶ Q) (w : f ≫ g = 0)

/-- The wedge map out of `ℒ` read through the degree-one generator is the multiplication by the
degree-one image of `ℒ` in `⋀ ℰ`, the first map of the presentation of [Stacks, Tag 01CJ]. -/
theorem wedgeHomFrom_exteriorGenerator (s : ℕ) :
    (wedgeHomFrom AL AE f (n := 1) AL.exteriorGenerator s :
        _ ⟶ AE.exterior.piece (1 + (s : ℤ))) =
      _root_.SheafOfModules.GradedAlgebra.generatorMul (f ≫ AE.exteriorGenerator) (s : ℤ) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (J := Opens.grothendieckTopology ↥X)
    fun U l y => ?_
  refine (wedgeHomFrom_unit AL AE f (n := 1) AL.exteriorGenerator s U l y).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.GradedAlgebra.generatorMul_unit _ _ U l y).symm
  exact congrArg (fun z => (AE.exterior.mul 1 (s : ℤ)).app U z y)
    (extHom_app_one AL AE f U l)

/-- The presentation of [Stacks, Tag 01CJ] in degree `k + 2` is exact and its last map is an
epimorphism. -/
private theorem relComplex_exact_and_epi (hS : (ShortComplex.mk f g w).Exact) [Epi g]
    (k : ℕ) :
    (relComplex AE AQ f g w (k + 1)).Exact ∧ Epi (relComplex AE AQ f g w (k + 1)).g :=
  _root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact AE.exteriorGenerator
    AQ.exteriorGenerator AE.exterior_isExteriorAlgebra AQ.exterior_isExteriorAlgebra g f w
    hS (k + 1)

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]

/-- The image in `⋀¹ ℰ` of a local section of a module `ℒ` of rank one, wedged with a degree-one
section coming from `ℒ`, vanishes: it is the image of a local section of `⋀² ℒ = 0`. -/
theorem mul_extHom_exteriorGenerator_eq_zero (V : (Opens ↥X)ᵒᵖ) (l a : L.val.obj V) :
    (AE.exterior.mul ((1 : ℕ) : ℤ) 1).app V
        (((extHom AL AE f).app ((1 : ℕ) : ℤ)).val.app V (AL.exteriorGenerator.val.app V l))
      (AE.exteriorGenerator.val.app V (f.val.app V a)) = 0 :=
  mul_extHom_generator_eq_zero AL AE f 1 V _ a

variable (hS : (ShortComplex.mk f g w).Exact) [Epi g]

/-- **The first arrow `ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ`** attached to an exact sequence
`ℒ ⟶ ℰ ⟶ 𝒬 ⟶ 0` with `ℒ` of rank one: `l ⊗ (q₀ ∧ ⋯ ∧ q_k) ↦ l ∧ q̃₀ ∧ ⋯ ∧ q̃_k` for local lifts
`q̃ᵢ` of the `qᵢ`. It is `Stacks.SheafOfModules.TopWedge.detComparisonFrom` for the degree-one
generator of `ℒ`, read in degree `k + 1 + 1`. -/
def lineWedge (k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj L).obj
        (AQ.exteriorPower (k + 1)) ⟶ AE.exteriorPower (k + 1 + 1) :=
  detComparisonFrom AL AE AQ f g w (n := 1) AL.exteriorGenerator
      (mul_extHom_exteriorGenerator_eq_zero AL AE f) hS k ≫
    eqToHom (by rw [show 1 + (k + 1) = k + 1 + 1 by omega])

/-- **The presentation of [Stacks, Tag 01CJ] in degree `k + 2` factors through the first
arrow**: its first map `ℒ ⊗ ⋀^{k+1} ℰ ⟶ ⋀^{k+2} ℰ` is `ℒ ⊗ ⋀^{k+1}(g)` followed by
`Stacks.SheafOfModules.TopWedge.lineWedge`. -/
theorem relComplex_f_eq_lineWedge (k : ℕ) :
    (relComplex AE AQ f g w (k + 1)).f =
      tensorLeftMapFrom (P := L) ((extHom AE AQ g).app ((k + 1 : ℕ) : ℤ)) ≫
        lineWedge AL AE AQ f g w hS k := by
  refine Eq.trans ?_ (Category.assoc
    (tensorLeftMapFrom (P := L) ((extHom AE AQ g).app ((k + 1 : ℕ) : ℤ)))
    (detComparisonFrom AL AE AQ f g w (n := 1) AL.exteriorGenerator
      (mul_extHom_exteriorGenerator_eq_zero AL AE f) hS k) (eqToHom _))
  refine Eq.trans ?_ (congrArg (· ≫ eqToHom _) (tensorLeftMap_comp_detComparisonFrom AL AE AQ
    f g w (n := 1) AL.exteriorGenerator (mul_extHom_exteriorGenerator_eq_zero AL AE f) hS k).symm)
  change _root_.SheafOfModules.GradedAlgebra.generatorMul (f ≫ AE.exteriorGenerator)
      ((k + 1 : ℕ) : ℤ) ≫ eqToHom _ = _
  exact congrArg (· ≫ eqToHom _) (wedgeHomFrom_exteriorGenerator AL AE f (k + 1)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
include w hS in
/-- Tensoring `⋀^{k+1}(g)` on the left with `ℒ` is an epimorphism: it is the cokernel of the
presentation of [Stacks, Tag 01CJ] tensored with `ℒ`. -/
theorem epi_tensorLeftMapFrom_extHom (k : ℕ) :
    Epi (tensorLeftMapFrom (P := L) ((extHom AE AQ g).app ((k + 1 : ℕ) : ℤ))) :=
  epi_of_isColimit_cofork (relCokernelIsColimitFrom AE AQ f g w (P := L) hS k)

/-- The first arrow followed by `⋀^{k+2}(g)` is zero. -/
theorem lineWedge_comp_extHom (k : ℕ) :
    lineWedge AL AE AQ f g w hS k ≫ (extHom AE AQ g).app ((k + 1 + 1 : ℕ) : ℤ) =
      (0 : (tensorLeftFunctorFrom (P := L)).obj (AQ.exteriorPower (k + 1)) ⟶ _) := by
  have := epi_tensorLeftMapFrom_extHom AE AQ f g w hS k
  refine (cancel_epi (tensorLeftMapFrom (P := L) ((extHom AE AQ g).app ((k + 1 : ℕ) : ℤ)))).1 ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (extHom AE AQ g).app ((k + 1 + 1 : ℕ) : ℤ))
    (relComplex_f_eq_lineWedge AL AE AQ f g w hS k).symm).trans ?_
  exact (relComplex AE AQ f g w (k + 1)).zero.trans comp_zero.symm

/-- The sequence `ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬` attached to an exact sequence
`ℒ ⟶ ℰ ⟶ 𝒬 ⟶ 0` with `ℒ` of rank one. -/
abbrev lineWedgeComplex (k : ℕ) :
    ShortComplex (_root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  ShortComplex.mk (lineWedge AL AE AQ f g w hS k) ((extHom AE AQ g).app ((k + 1 + 1 : ℕ) : ℤ))
    (lineWedge_comp_extHom AL AE AQ f g w hS k)

/-- **The sequence `ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬 ⟶ 0` is exact**: the presentation of
[Stacks, Tag 01CJ] in degree `k + 2` maps to it by an epimorphism on the first term and the
identity on the other two. -/
theorem lineWedgeComplex_exact (k : ℕ) : (lineWedgeComplex AL AE AQ f g w hS k).Exact := by
  have := epi_tensorLeftMapFrom_extHom AE AQ f g w hS k
  let φ : relComplex AE AQ f g w (k + 1) ⟶ lineWedgeComplex AL AE AQ f g w hS k :=
    { τ₁ := tensorLeftMapFrom (P := L) ((extHom AE AQ g).app ((k + 1 : ℕ) : ℤ))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (relComplex_f_eq_lineWedge AL AE AQ f g w hS k).symm.trans
        (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := ‹_›
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (relComplex_exact_and_epi AE AQ f g w hS k).1

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
include w hS in
/-- The second arrow `⋀^{k+2}(g)` is an epimorphism ([Stacks, Tag 01CJ]). -/
theorem epi_extHom_app (k : ℕ) : Epi ((extHom AE AQ g).app ((k + 1 + 1 : ℕ) : ℤ)) :=
  (relComplex_exact_and_epi AE AQ f g w hS k).2

end Stacks.SheafOfModules.TopWedge

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules.TopWedge

/-- The identity functor from the sheaves of modules over
`toRingCat (Opens.grothendieckTopology X) X.sheaf`, the spelling of the structure sheaf of rings in
which the exterior algebra of a sheaf of modules is developed, to `X.Modules`. -/
def ofSiteModules (X : Scheme.{u}) :
    _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) ⥤
      X.Modules where
  obj M := M
  map f := f

/-- `AlgebraicGeometry.Scheme.Modules.ofSiteModules` is an equivalence of categories, with
inverse the identity read the other way. -/
def ofSiteModulesEquivalence (X : Scheme.{u}) :
    _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) ≌
      X.Modules where
  functor := ofSiteModules X
  inverse := { obj M := M, map f := f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- `AlgebraicGeometry.Scheme.Modules.ofSiteModules` is an equivalence of categories. -/
instance (X : Scheme.{u}) : (ofSiteModules X).IsEquivalence :=
  (ofSiteModulesEquivalence X).isEquivalence_functor

/-- `AlgebraicGeometry.Scheme.Modules.ofSiteModules` preserves zero morphisms, being the
identity on morphisms. -/
instance (X : Scheme.{u}) : (ofSiteModules X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable {X : Scheme.{u}} {L E Q : X.Modules} (f : L ⟶ E) (g : E ⟶ Q) (w : f ≫ g = 0)
  (hS : (ShortComplex.mk f g w).ShortExact)
  [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]

include hS in
/-- **The exterior powers of an extension by a module of rank one**: for a short exact sequence
`0 ⟶ ℒ ⟶ ℰ ⟶ 𝒬 ⟶ 0` of `𝒪_X`-modules with `ℒ` finite locally free of rank one and `𝒬` finite
locally free of rank `m`, there is for every `k` a short exact sequence

  `0 ⟶ ℒ ⊗ ⋀^{k+1} 𝒬 ⟶ ⋀^{k+2} ℰ ⟶ ⋀^{k+2} 𝒬 ⟶ 0`.

Its arrows are `Stacks.SheafOfModules.TopWedge.lineWedge` and `⋀^{k+2}` of `ℰ ⟶ 𝒬`.
Exactness at the middle and on the right come from the presentation of [Stacks, Tag 01CJ]
(`Stacks.SheafOfModules.TopWedge.lineWedgeComplex_exact`). On the left, the first arrow maps by
an epimorphism onto the kernel of the second, which is finite locally free of rank
`binom(m + 1, k + 2) - binom(m, k + 2) = binom(m, k + 1)`, the rank of `ℒ ⊗ ⋀^{k+1} 𝒬`; an
epimorphism of finite locally free modules of the same rank is an isomorphism
([Stacks, Tag 089Q]). -/
theorem exists_shortExact_exteriorPower_of_rank_one (m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q m] (k : ℕ) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj
          (exteriorPower Q ((k + 1 : ℕ) : ℤ))) ∧
      Nonempty (S.X₂ ≅ exteriorPower E ((k + 1 + 1 : ℕ) : ℤ)) ∧
      Nonempty (S.X₃ ≅ exteriorPower Q ((k + 1 + 1 : ℕ) : ℤ)) := by
  let S' := @lineWedgeComplex _ X.sheaf L E Q (_root_.SheafOfModules.algebras _ L)
      (_root_.SheafOfModules.algebras _ E) (_root_.SheafOfModules.algebras _ Q) f g w hL
      hS.exact hS.epi_g k
  set T := S'.map (ofSiteModules X)
  have hex : T.Exact := (@lineWedgeComplex_exact _ X.sheaf L E Q
      (_root_.SheafOfModules.algebras _ L) (_root_.SheafOfModules.algebras _ E)
      (_root_.SheafOfModules.algebras _ Q) f g w hL hS.exact hS.epi_g k).map (ofSiteModules X)
  have hepi : Epi T.g := @Functor.map_epi _ _ _ _ (ofSiteModules X) _ _
    _ _ (@epi_extHom_app _ X.sheaf L E Q (_root_.SheafOfModules.algebras _ E)
      (_root_.SheafOfModules.algebras _ Q) f g w hS.exact hS.epi_g k)
  refine ⟨T, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  have hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (1 + m) :=
    Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS 1 m ‹_› ‹_›
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      ((1 + m).choose (k + 1 + 1)) :=
    isFiniteLocallyFreeOfRank_exteriorPower E (1 + m) (k + 1 + 1)
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃
      (m.choose (k + 1 + 1)) :=
    isFiniteLocallyFreeOfRank_exteriorPower Q m (k + 1 + 1)
  have hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    T.g hepi _ _ h₂ h₃
  have hrk : (1 + m).choose (k + 1 + 1) - m.choose (k + 1 + 1) = 1 * m.choose (k + 1) := by
    have h := Nat.choose_succ_succ' m (k + 1)
    rw [Nat.add_comm 1 m, h]
    omega
  rw [hrk] at hK
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁
      (1 * m.choose (k + 1)) :=
    Stacks.Chow.isFiniteLocallyFreeOfRank_tensor ‹_›
      (isFiniteLocallyFreeOfRank_exteriorPower Q m (k + 1))
  have : IsIso (kernel.lift T.g T.f T.zero) :=
    (@Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank
      X.toLocallyRingedSpace.toRingedSpace inferInstance inferInstance _ _ _ h₁ hK _).2
      hex.epi_kernelLift
  have : Mono T.f := by
    rw [← kernel.lift_ι T.g T.f T.zero]
    exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ equalizer.ι_mono
  exact { exact := hex }

end AlgebraicGeometry.Scheme.Modules

end
