module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Bijective
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Local

/-!
# Locality and functoriality of the module comparison on sections

`Stacks.ProjModuleComparison.bijective_sectionsMap` decides bijectivity of the comparison on
sections only for a degreewise localization, and only over an open where the element localized
away from does not vanish. To descend the comparison of the sheaves attached to a graded module
from standard opens of the base to an arbitrary affine open, bijectivity has to be assembled from
such local pieces. This file provides the two tools for that, for an arbitrary graded module; they
are the module companions of the locality statements for the twist comparison in
`Stacks.ProjTwistComparison`.

The first is the observation that `Stacks.ProjModuleComparison.sectionsMap` is *pointwise*: a
section is a dependent function into the module fibres subject to a local condition, and the
comparison applies `Stacks.ProjModuleComparison.fibreMap` at each point. So injectivity needs
nothing but injectivity of the fibre comparison together with the fact that every point of the
open is hit by the comparison of points.

The second is that surjectivity is local on the open. The local-fraction predicate
`AlgebraicGeometry.ProjectiveSpectrum.Proj.locallyModuleFraction` is a
`TopCat.PrelocalPredicate.sheafify`, so it is by definition checked in a neighbourhood of each
point; and the preimages produced over the members of a covering agree on overlaps because the
fibre comparison is injective. Hence they glue.

Combining the two with the functoriality of the comparison lets the hypotheses be discharged on a
factor of a composite: this is how the descent reasons, since the restriction to a standard open
factors through the restriction to the intervening affine open.

## Main definitions

* `Stacks.ProjModuleComparison.restrictModuleSections`: restriction of a family of local
  homogeneous fractions to a smaller open.

## Main results

* `Stacks.ProjModuleComparison.injective_sectionsMap_of_pointwise`: the comparison on sections is
  injective as soon as the fibre comparison is injective and the comparison of points is onto.
* `Stacks.ProjModuleComparison.bijective_sectionsMap_of_cover`: **bijectivity of the comparison
  on sections is local**: it holds over an open covered by opens over which it holds, given the
  pointwise hypotheses.
* `Stacks.ProjModuleComparison.fibreMap_comp`: **the fibre comparison is functorial**.
* `Stacks.ProjModuleComparison.bijective_fibreMap_of_eq_comp` and
  `Stacks.ProjModuleComparison.surjective_sectionsMap_of_eq_comp`: a factor of a composite
  inherits bijectivity of the fibre comparison, and surjectivity on sections, from the composite
  together with injectivity of the other factor.

## Implementation notes

A factorization is presented by *two* equations here, one for the graded ring homomorphism and one
for the semilinear map: `hcomp : χ = ψ.comp φ` and `hfcomp : ∀ m, fχ m = f' (f m)`. The second is
pointwise rather than an equality of semilinear maps because the composite of a `φ`-semilinear and
a `ψ`-semilinear map is `ψ.comp φ`-semilinear only through a `RingHomCompTriple`, so the composite
`f' ∘ₛₗ f` and a given `χ`-semilinear `fχ` do not have the same type before `hcomp` is
substituted away. Pointwise, the two equations are exactly what a restriction map of graded
section modules supplies, through its functoriality.

The comparison of *points* is not module-theoretic at all, so it is not redone here: the
surjectivity of the comparison of points onto an open and the two-step description of a preimage
are taken from `Stacks.ProjTwistComparison`, where they are stated for an arbitrary homomorphism
of graded rings with no reference to a module or to a twist.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. Nothing is glued here, and nothing is proved about a relative `Proj`
situation: these are statements about an arbitrary homomorphism of graded rings and an arbitrary
semilinear map of graded modules over it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open scoped Stacks.GradedLocalization

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

variable {A B M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  (f : M →ₛₗ[φ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)

/-! ### Restriction of sections -/

/-- Restriction of a family of local homogeneous fractions to a smaller open. -/
public def restrictModuleSections {V U : Opens (ProjectiveSpectrum.top ℬ)} (hVU : V ≤ U)
    (a : moduleSections ℬ 𝒩 U) : moduleSections ℬ 𝒩 V :=
  ⟨fun x => a.1 ⟨x.1, hVU x.2⟩, (locallyModuleFraction ℬ 𝒩).res (homOfLE hVU) a.1 a.2⟩

/-! ### Pointwise criteria -/

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
include hf in
/-- **The comparison on sections is injective as soon as the fibre comparison is**, provided
every point of the open is the image of a point of `Proj ℬ`. -/
public theorem injective_sectionsMap_of_pointwise (U : Opens (ProjectiveSpectrum.top 𝒜))
    (hpt : ∀ x : U, ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comapFun φ hφ y = x.1)
    (hfib : ∀ y : ProjectiveSpectrum ℬ, Function.Injective (fibreMap φ hφ f y)) :
    Function.Injective (sectionsMap φ hφ f hf U) := by
  intro a a' hyp
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨y, hy⟩ := hpt x
  have hyU : y ∈ U.comap (ProjectiveSpectrum.comap φ hφ) := by
    change ProjectiveSpectrum.comapFun φ hφ y ∈ U
    rw [hy]
    exact x.2
  have hval := congrFun (congrArg Subtype.val hyp) ⟨y, hyU⟩
  rw [sectionsMap_apply, sectionsMap_apply] at hval
  have hx : (⟨ProjectiveSpectrum.comapFun φ hφ y, hyU⟩ : U) = x := Subtype.ext hy
  rw [← hx]
  exact hfib y hval

/-! ### Locality of bijectivity -/

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
include hf in
/-- **Bijectivity of the comparison on sections is local on the open.** Given a covering of `U`
by opens over which the comparison on sections is surjective, together with injectivity of the
fibre comparison and surjectivity of the comparison of points onto `U`, the comparison on
sections is bijective over `U`. -/
public theorem bijective_sectionsMap_of_cover (U : Opens (ProjectiveSpectrum.top 𝒜))
    {ι : Type*} (V : ι → Opens (ProjectiveSpectrum.top 𝒜))
    (hVU : ∀ i, V i ≤ U) (hcov : ∀ x : U, ∃ i, x.1 ∈ V i)
    (hpt : ∀ x : U, ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comapFun φ hφ y = x.1)
    (hfib : ∀ y : ProjectiveSpectrum ℬ, Function.Injective (fibreMap φ hφ f y))
    (hsurj : ∀ i, Function.Surjective (sectionsMap φ hφ f hf (V i))) :
    Function.Bijective (sectionsMap φ hφ f hf U) := by
  refine ⟨injective_sectionsMap_of_pointwise φ hφ f hf U hpt hfib, fun b => ?_⟩
  have hleB : ∀ i, (V i).comap (ProjectiveSpectrum.comap φ hφ) ≤
      U.comap (ProjectiveSpectrum.comap φ hφ) := fun i _ hz => hVU i hz
  choose a ha using fun i => hsurj i (restrictModuleSections (hleB i) b)
  have key : ∀ (i : ι) (y : ProjectiveSpectrum ℬ)
      (hyi : ProjectiveSpectrum.comapFun φ hφ y ∈ V i)
      (hyU : ProjectiveSpectrum.comapFun φ hφ y ∈ U),
      fibreMap φ hφ f y ((a i).1 ⟨ProjectiveSpectrum.comapFun φ hφ y, hyi⟩) = b.1 ⟨y, hyU⟩ :=
    fun i y hyi _ => congrFun (congrArg Subtype.val (ha i)) ⟨y, hyi⟩
  have hagree : ∀ (i j : ι) (p : ProjectiveSpectrum.top 𝒜) (hpU : p ∈ U)
      (hpi : p ∈ V i) (hpj : p ∈ V j), (a i).1 ⟨p, hpi⟩ = (a j).1 ⟨p, hpj⟩ := by
    intro i j p hpU hpi hpj
    obtain ⟨y, hy⟩ := hpt ⟨p, hpU⟩
    subst hy
    exact hfib y ((key i y hpi hpU).trans (key j y hpj hpU).symm)
  choose idx hidx using hcov
  have hval : ∀ (p : ProjectiveSpectrum.top 𝒜) (hpU : p ∈ U) (i : ι) (hpi : p ∈ V i),
      (a (idx ⟨p, hpU⟩)).1 ⟨p, hidx ⟨p, hpU⟩⟩ = (a i).1 ⟨p, hpi⟩ :=
    fun p hpU i hpi => hagree _ i p hpU _ hpi
  refine ⟨⟨fun x => (a (idx x)).1 ⟨x.1, hidx x⟩, fun x => ?_⟩, ?_⟩
  · obtain ⟨W, hxW, iW, hfrac⟩ := (a (idx x)).2 ⟨x.1, hidx x⟩
    refine ⟨W, hxW, iW ≫ homOfLE (hVU (idx x)), ?_⟩
    have heq : (fun w : W => (a (idx ((iW ≫ homOfLE (hVU (idx x))) w))).1
          ⟨((iW ≫ homOfLE (hVU (idx x))) w).1, hidx _⟩)
        = fun w : W => (a (idx x)).1 (iW w) :=
      funext fun w => hval w.1 _ (idx x) (iW w).2
    rw [heq]
    exact hfrac
  · exact Subtype.ext (funext fun y =>
      key (idx ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩) y.1
        (hidx ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩) y.2)

/-! ### Transfer along a factorization -/

section Factor

variable {C P : Type u} {ρ π : Type u} [CommRing C] [AddCommGroup P] [Module C P]
  [SetLike ρ C] [AddSubgroupClass ρ C] [SetLike π P] [AddSubgroupClass π P]
  {𝒞 : ℕ → ρ} [GradedRing 𝒞] {𝒬 : ℤ → π} [DirectSum.Decomposition 𝒬]
  [SetLike.GradedSMul 𝒞 𝒬]
  (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  (f' : N →ₛₗ[ψ.toRingHom] P) (hf' : ∀ (i : ℤ) {y : N}, y ∈ 𝒩 i → f' y ∈ 𝒬 i)

/-- **The fibre comparison is functorial.** At a point of `Proj 𝒞` the comparison attached to a
composite of homomorphisms of graded rings, together with a semilinear map presented as a
composite, is the composite of the two comparisons. -/
public theorem fibreMap_comp (hψφ : 𝒞₊ ≤ 𝒜₊.map (ψ.comp φ))
    (fψφ : M →ₛₗ[(ψ.comp φ).toRingHom] P) (hfcomp : ∀ m : M, fψφ m = f' (f m))
    (y : ProjectiveSpectrum 𝒞)
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun (ψ.comp φ) hψφ y)) :
    fibreMap (ψ.comp φ) hψφ fψφ y z
      = fibreMap ψ hψ f' y (fibreMap φ hφ f (ProjectiveSpectrum.comapFun ψ hψ y) z) := by
  induction z using LocalizedModule.induction_on with
  | h m t =>
    simp only [fibreMap_mk]
    exact congrArg₂ LocalizedModule.mk (hfcomp m) (Subtype.ext rfl)

/-- **A factor inherits bijectivity of the fibre comparison from the composite.** If the fibre
comparison of the composite at a point `y` is bijective and that of the second factor at `y` is
injective, then that of the first factor at the point below `y` is bijective. -/
public theorem bijective_fibreMap_of_eq_comp {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
    (hcomp : χ = ψ.comp φ) (fχ : M →ₛₗ[χ.toRingHom] P) (hfcomp : ∀ m : M, fχ m = f' (f m))
    (y : ProjectiveSpectrum 𝒞)
    (h₁ : Function.Bijective (fibreMap χ hχ fχ y))
    (h₂ : Function.Injective (fibreMap ψ hψ f' y)) :
    Function.Bijective (fibreMap φ hφ f (ProjectiveSpectrum.comapFun ψ hψ y)) := by
  subst hcomp
  have hfun : fibreMap (ψ.comp φ) hχ fχ y =
      fibreMap ψ hψ f' y ∘ fibreMap φ hφ f (ProjectiveSpectrum.comapFun ψ hψ y) :=
    funext fun z => fibreMap_comp φ hφ f ψ hψ f' hχ fχ hfcomp y z
  rw [hfun] at h₁
  refine ⟨fun u v huv => h₁.1 (congrArg (fibreMap ψ hψ f' y) huv), fun t => ?_⟩
  obtain ⟨w, hw⟩ := h₁.2 (fibreMap ψ hψ f' y t)
  exact ⟨w, h₂ hw⟩

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition 𝒬] in
include hf hf' in
/-- **A factor inherits surjectivity on sections from the composite**, given injectivity of the
other factor on the sections it reads. -/
public theorem surjective_sectionsMap_of_eq_comp {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
    (hcomp : χ = ψ.comp φ) (fχ : M →ₛₗ[χ.toRingHom] P)
    (hfχ : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → fχ m ∈ 𝒬 i)
    (hfcomp : ∀ m : M, fχ m = f' (f m)) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h₁ : Function.Surjective (sectionsMap χ hχ fχ hfχ U))
    (h₂ : Function.Injective
      (sectionsMap ψ hψ f' hf' (U.comap (ProjectiveSpectrum.comap φ hφ)))) :
    Function.Surjective (sectionsMap φ hφ f hf U) := by
  subst hcomp
  intro b
  obtain ⟨a, ha⟩ := h₁ (sectionsMap ψ hψ f' hf' (U.comap (ProjectiveSpectrum.comap φ hφ)) b)
  refine ⟨a, h₂ (Eq.trans (Subtype.ext (funext fun y => ?_)) ha)⟩
  exact (fibreMap_comp φ hφ f ψ hψ f' hχ fχ hfcomp y.1 _).symm

end Factor

end Stacks.ProjModuleComparison

end
