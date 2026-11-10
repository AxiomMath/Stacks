module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Functorial

/-!
# Locality of the twist comparison on sections

`Stacks.ProjTwistComparison.bijective_sectionsMap` decides bijectivity of the comparison on
sections only for a degreewise localization, and only over an open where the element localized
away from does not vanish. To descend the twist comparison of
`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Comparison.lean` from standard opens of the
base to an arbitrary affine open, bijectivity has to be assembled from such local pieces. This
file provides the two tools for that.

The first is the observation that `Stacks.ProjTwistComparison.sectionsMap` is *pointwise*: a
section is a dependent function into the module fibres subject to a local condition, and the
comparison applies `Stacks.ProjTwistComparison.fibreMap` at each point. So injectivity needs
nothing but injectivity of the fibre comparison together with the fact that every point of the
open is hit by the comparison of points.

The second is that surjectivity is local on the open. The local-fraction predicate
`AlgebraicGeometry.ProjectiveSpectrum.Proj.locallyModuleFraction` is a
`TopCat.PrelocalPredicate.sheafify`, so it is by definition checked in a neighbourhood of each
point; and the preimages produced over the members of a covering agree on overlaps because the
fibre comparison is injective. Hence they glue.

Combining the two with `Stacks.ProjTwistComparison.sectionsMap_comp` — functoriality of the
comparison — lets the hypotheses be discharged on a factor of a composite: this is how the
descent reasons, since the restriction to a standard open factors through the restriction to the
intervening affine open.

## Main results

* `Stacks.ProjTwistComparison.injective_sectionsMap_of_pointwise`: the comparison on sections is
  injective as soon as the fibre comparison is injective and the comparison of points is onto.
* `Stacks.ProjTwistComparison.bijective_sectionsMap_of_cover`: **bijectivity of the comparison on
  sections is local**: it holds over an open covered by opens over which it holds, given the
  pointwise hypotheses.
* `Stacks.ProjTwistComparison.bijective_fibreMap_of_eq_comp` and
  `Stacks.ProjTwistComparison.surjective_sectionsMap_of_eq_comp`: a factor of a composite
  inherits bijectivity of the fibre comparison, and surjectivity on sections, from the composite
  together with injectivity of the other factor.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B C : Type u} {σ τ ρ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-! ### Restriction of sections -/

section Restrict

variable {R : Type u} {ν : Type u} [CommRing R] [SetLike ν R] [AddSubgroupClass ν R]
  (ℛ : ℕ → ν) [GradedRing ℛ] (n : ℤ)

/-- Restriction of a family of degree-`n` module fractions to a smaller open. -/
def restrictTwistSections {U V : Opens (ProjectiveSpectrum.top ℛ)} (hVU : V ≤ U)
    (a : moduleSections ℛ (twistGrading (S := R) ℛ n) U) :
    moduleSections ℛ (twistGrading (S := R) ℛ n) V :=
  ⟨fun x => a.1 ⟨x.1, hVU x.2⟩,
    (locallyModuleFraction ℛ (twistGrading (S := R) ℛ n)).res (homOfLE hVU) a.1 a.2⟩

end Restrict

/-! ### Pointwise criteria -/

variable (n : ℤ)

/-- **The comparison on sections is injective as soon as the fibre comparison is.** A section is
a dependent function into the module fibres, and the comparison applies the fibre comparison at
each point; so if every point of the open is the image of a point of `Proj ℬ` and the fibre
comparison is injective there, two sections with the same image agree pointwise. -/
theorem injective_sectionsMap_of_pointwise (U : Opens (ProjectiveSpectrum.top 𝒜))
    (hpt : ∀ x : U, ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comapFun φ hφ y = x.1)
    (hfib : ∀ y : ProjectiveSpectrum ℬ, Function.Injective (fibreMap φ hφ y)) :
    Function.Injective (sectionsMap φ hφ n U) := by
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

/-- **Bijectivity of the comparison on sections is local on the open.** Given a covering of `U`
by opens over which the comparison on sections is surjective, together with injectivity of the
fibre comparison and surjectivity of the comparison of points onto `U`, the comparison on
sections is bijective over `U`.

Injectivity is pointwise. For surjectivity, the preimages over the members of the covering agree
wherever two members meet, because their values have the same image under the injective fibre
comparison; the resulting function satisfies the local-fraction predicate because that predicate
is by definition checked in a neighbourhood of each point, and near each point the function
agrees with one of the preimages. -/
theorem bijective_sectionsMap_of_cover (U : Opens (ProjectiveSpectrum.top 𝒜))
    {ι : Type*} (V : ι → Opens (ProjectiveSpectrum.top 𝒜))
    (hVU : ∀ i, V i ≤ U) (hcov : ∀ x : U, ∃ i, x.1 ∈ V i)
    (hpt : ∀ x : U, ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comapFun φ hφ y = x.1)
    (hfib : ∀ y : ProjectiveSpectrum ℬ, Function.Injective (fibreMap φ hφ y))
    (hsurj : ∀ i, Function.Surjective (sectionsMap φ hφ n (V i))) :
    Function.Bijective (sectionsMap φ hφ n U) := by
  refine ⟨injective_sectionsMap_of_pointwise φ hφ n U hpt hfib, fun b => ?_⟩
  have hleB : ∀ i, (V i).comap (ProjectiveSpectrum.comap φ hφ) ≤
      U.comap (ProjectiveSpectrum.comap φ hφ) := fun i _ hz => hVU i hz
  choose a ha using fun i => hsurj i (restrictTwistSections ℬ n (hleB i) b)
  -- the defining identity of the local preimages, read at a point
  have key : ∀ (i : ι) (y : ProjectiveSpectrum ℬ)
      (hyi : ProjectiveSpectrum.comapFun φ hφ y ∈ V i)
      (hyU : ProjectiveSpectrum.comapFun φ hφ y ∈ U),
      fibreMap φ hφ y ((a i).1 ⟨ProjectiveSpectrum.comapFun φ hφ y, hyi⟩) = b.1 ⟨y, hyU⟩ :=
    fun i y hyi _ => congrFun (congrArg Subtype.val (ha i)) ⟨y, hyi⟩
  -- the local preimages agree wherever two members of the covering meet
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

variable (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)

/-- **A factor inherits bijectivity of the fibre comparison from the composite.** If the fibre
comparison of `ψ ∘ φ` at a point `z` is bijective and that of `ψ` at `z` is injective, then that
of `φ` at the point below `z` is bijective. -/
theorem bijective_fibreMap_of_comp (hψφ : 𝒞₊ ≤ 𝒜₊.map (ψ.comp φ)) (z : ProjectiveSpectrum 𝒞)
    (h₁ : Function.Bijective (fibreMap (ψ.comp φ) hψφ z))
    (h₂ : Function.Injective (fibreMap ψ hψ z)) :
    Function.Bijective (fibreMap φ hφ (ProjectiveSpectrum.comapFun ψ hψ z)) := by
  have hfun : fibreMap (ψ.comp φ) hψφ z =
      fibreMap ψ hψ z ∘ fibreMap φ hφ (ProjectiveSpectrum.comapFun ψ hψ z) :=
    funext (fibreMap_comp φ hφ ψ hψ hψφ z)
  rw [hfun] at h₁
  exact ⟨h₁.1.of_comp, h₁.2.of_comp_left h₂⟩

/-- `Stacks.ProjTwistComparison.bijective_fibreMap_of_comp` with the composite presented as an
equation, which is how a restriction map of graded section rings factors. -/
theorem bijective_fibreMap_of_eq_comp {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
    (hcomp : χ = ψ.comp φ) (z : ProjectiveSpectrum 𝒞)
    (h₁ : Function.Bijective (fibreMap χ hχ z))
    (h₂ : Function.Injective (fibreMap ψ hψ z)) :
    Function.Bijective (fibreMap φ hφ (ProjectiveSpectrum.comapFun ψ hψ z)) := by
  subst hcomp
  exact bijective_fibreMap_of_comp φ hφ ψ hψ hχ z h₁ h₂

/-- **A factor inherits surjectivity on sections from the composite**, given injectivity of the
other factor on the sections it reads. -/
theorem surjective_sectionsMap_of_comp (hψφ : 𝒞₊ ≤ 𝒜₊.map (ψ.comp φ))
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h₁ : Function.Surjective (sectionsMap (ψ.comp φ) hψφ n U))
    (h₂ : Function.Injective
      (sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ)))) :
    Function.Surjective (sectionsMap φ hφ n U) := by
  rw [sectionsMap_comp' φ hφ ψ hψ hψφ n U] at h₁
  exact h₁.of_comp_left h₂

/-- `Stacks.ProjTwistComparison.surjective_sectionsMap_of_comp` with the composite presented as
an equation. -/
theorem surjective_sectionsMap_of_eq_comp {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ)
    (hcomp : χ = ψ.comp φ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h₁ : Function.Surjective (sectionsMap χ hχ n U))
    (h₂ : Function.Injective
      (sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ)))) :
    Function.Surjective (sectionsMap φ hφ n U) := by
  subst hcomp
  exact surjective_sectionsMap_of_comp φ hφ n ψ hψ hχ U h₁ h₂

end Factor

end Stacks.ProjTwistComparison

end
