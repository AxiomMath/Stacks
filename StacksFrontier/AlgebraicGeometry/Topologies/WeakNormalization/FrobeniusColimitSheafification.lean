module

public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitHSheaf

/-!
# The Frobenius colimit computes the h sheafification of the structure sheaf

Let `p` be a prime number.  Stacks 0EVW has two parts.  Part (1) says that for an algebra `A`
over `𝔽_p` the colimit `colim_F A` of the Frobenius tower `A →^F A →^F ⋯` is the absolute weak
normalization of `A`; it is
`AlgebraicGeometry.Algebra.existsUnique_frobeniusColimit_iso_absoluteWeakNormalization`.  Part
(2) says that for a scheme `S` over `𝔽_p` the h sheafification of the structure sheaf `𝒪` on
`(Sch/S)_h` has `colim_F Γ(X, 𝒪_X)` as its sections over a quasi-compact quasi-separated object
`X`.  This file proves part (2) and records the two parts together.

## Main results

* `AlgebraicGeometry.BigHOver.exists_bijective_hom_frobeniusColimitSections_of_isSheafification`:
  part (2) of Stacks 0EVW.
* `AlgebraicGeometry.BigHOver.exists_bijective_hom_frobeniusColimitSections_awnSections`: the same
  conclusion with no hypothesis about a sheafification, at the one exhibited by Stacks 0EVU.
* `AlgebraicGeometry.frobeniusColimit_absoluteWeakNormalization_and_hSheafificationSections`: the
  whole of Stacks 0EVW, both parts together.

## Implementation notes

The h sheafification of `𝒪` is not a constructed object here: on the big h site the canonical
sheafification functor of Mathlib is unavailable, because the site is large and `CommRingCat.{u}`
has no colimits of that size.  As in Stacks 0EVU, which this development states for a sheaf
together with the universal property of its unit, the sheafification is therefore taken as given
data: a sheaf of rings `G` on `(Sch/S)_h` and a map `α : 𝒪 ⟶ G` initial among maps from `𝒪` to
sheaves of rings.  That property determines `(G, α)` up to a unique isomorphism, so the statement
proved is about the h sheafification of `𝒪` and about nothing else.

That hypothesis is inhabited, so the general statement is not vacuous: the rule
`X ↦ Γ(Xᵃʷⁿ, 𝒪)` satisfies it, being a sheaf of rings by
`AlgebraicGeometry.BigHOver.isSheaf_absoluteWeakNormalizationSections` with initial unit by
`AlgebraicGeometry.BigHOver.existsUnique_hom_absoluteWeakNormalizationSections`, both of Stacks
0EVU.  The instantiation is
`AlgebraicGeometry.BigHOver.exists_bijective_hom_frobeniusColimitSections_awnSections`, which
concludes `colim_F Γ(X, 𝒪_X)` on quasi-compact quasi-separated objects with no hypothesis about
a sheafification.

The conclusion `G(X) = colim_F Γ(X, 𝒪_X)` is read, as in Stacks 0EVK, as a map of presheaves
`colim_F Γ(-, 𝒪) ⟶ G` bijective on quasi-compact quasi-separated objects: naturality in `X` is
the compatibility with restriction, and the stated agreement with `α` on the stage `0` of the
Frobenius tower is what makes the identification the canonical one rather than some bijection.

The proof is the one of the source.  By Stacks 0EVU the rule `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is a sheaf of
rings and its unit is initial, so it is identified with `(G, α)` by a unique isomorphism of
presheaves of rings.  By Stacks 0EVW (1), read affine locally, the comparison
`colim_F Γ(X, 𝒪_X) ⟶ Γ(Xᵃʷⁿ, 𝒪)` of
`AlgebraicGeometry.BigHOver.bijective_awnComparison_app` is bijective for quasi-compact
quasi-separated `X`.  Composing the two gives the identification.

## References

* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
* [Stacks Project, Tag 0EVU](https://stacks.math.columbia.edu/tag/0EVU)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Part (2) of Stacks Project, Tag 0EVW.** Let `p` be a prime number and let `S` be a scheme
over `𝔽_p`, that is, a scheme in which `p` vanishes on global functions.  Let `(Sch/S)_h` be a
big h site over `S` as in Stacks 0EU1.  Let `G` be the h sheafification of the structure sheaf
`𝒪`: a sheaf of rings together with a map `α : 𝒪 ⟶ G` initial among the maps from `𝒪` to sheaves
of rings.  Then the sections of `G` over a quasi-compact quasi-separated object `X` are
`colim_F Γ(X, 𝒪_X)`.

The identification is given by a map of presheaves `colim_F Γ(-, 𝒪) ⟶ G` which agrees with `α`
on the stage `0` of the Frobenius tower and is bijective over every quasi-compact quasi-separated
object; naturality is compatibility with restriction. -/
@[stacks 0EVW "the h sheafification of the structure sheaf on qcqs objects"]
public theorem exists_bijective_hom_frobeniusColimitSections_of_isSheafification (p : ℕ)
    (hp : p.Prime) (hSp : Stacks.Frobenius.IsInCharacteristic S p)
    (G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u})
    (hG : Presheaf.IsSheaf (BigHOver.topology B S hS) G)
    (α : (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⟶ G)
    (hα : ∀ H : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u},
      Presheaf.IsSheaf (BigHOver.topology B S hS) H →
      ∀ β : (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⟶ H, ∃! χ : G ⟶ H, α ≫ χ = β) :
    ∃ φ : frobeniusColimitSections B S hS p ⟶ G ⋙ CategoryTheory.forget CommRingCat.{u},
      (∀ (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
        φ.app (op X) (colimitStage B S hS p 0 X a) = α.app (op X) a) ∧
      ∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
        QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
          Function.Bijective (φ.app (op X)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hQ : Presheaf.IsSheaf (BigHOver.topology B S hS)
      (absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS)) :=
    isSheaf_absoluteWeakNormalizationSections B S hS
  obtain ⟨χ, hχ, -⟩ := hα _ hQ (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))
  obtain ⟨χ', hχ', -⟩ := existsUnique_hom_absoluteWeakNormalizationSections B S hS G hG α
  have hGG : χ ≫ χ' = 𝟙 G :=
    (hα G hG α).unique (by rw [← Category.assoc, hχ, hχ']) (Category.comp_id α)
  have hQQ : χ' ≫ χ = 𝟙 (absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS)) :=
    (existsUnique_hom_absoluteWeakNormalizationSections B S hS _ hQ _).unique
      (by rw [← Category.assoc, hχ', hχ]) (Category.comp_id _)
  have : IsIso χ' := ⟨χ, hQQ, hGG⟩
  refine ⟨awnComparison B S hS p hSp ≫
    Functor.whiskerRight χ' (CategoryTheory.forget CommRingCat.{u}), ?_, ?_⟩
  · intro X a
    have h0 : (awnComparison B S hS p hSp).app (op X) (colimitStage B S hS p 0 X a) =
        (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)).app (op X) a :=
      awnComparison_colimitStage B S hS p hSp 0 X a
    have h1 : χ'.app (op X)
        ((absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)).app (op X) a) =
        α.app (op X) a :=
      ConcreteCategory.congr_hom (congr_app hχ' (op X)) a
    show χ'.app (op X) ((awnComparison B S hS p hSp).app (op X)
      (colimitStage B S hS p 0 X a)) = _
    rw [h0, h1]
  · intro X hc hq
    have := hc
    have := hq
    have h1 : Function.Bijective ((awnComparison B S hS p hSp).app (op X)) :=
      bijective_awnComparison_app B S hS p hSp X
    have h2 : Function.Bijective (fun x :
        ToType ((absoluteWeakNormalizationSectionsOver
          (BigHOver.toScheme B S hS)).obj (op X)) => χ'.app (op X) x) :=
      ConcreteCategory.bijective_of_isIso (χ'.app (op X))
    exact h2.comp h1

/-- Part (2) of Stacks Project, Tag 0EVW at the h sheafification exhibited by Stacks 0EVU.
Let `p` be a prime number and let `S` be a scheme over `𝔽_p`.  The sections of the presheaf of
rings `X ↦ Γ(Xᵃʷⁿ, 𝒪)` over a quasi-compact quasi-separated object `X` of a big h site over `S`
are `colim_F Γ(X, 𝒪_X)`, by an identification agreeing with pullback along the absolute weak
normalization on the stage `0` of the Frobenius tower.

This instantiates
`AlgebraicGeometry.BigHOver.exists_bijective_hom_frobeniusColimitSections_of_isSheafification`
at the h sheafification of the structure sheaf constructed for Stacks 0EVU, so it carries no
hypothesis about a sheafification at all.  In particular that general statement is not vacuous:
its hypotheses are inhabited on this site. -/
public theorem exists_bijective_hom_frobeniusColimitSections_awnSections (p : ℕ) (hp : p.Prime)
    (hSp : Stacks.Frobenius.IsInCharacteristic S p) :
    ∃ φ : frobeniusColimitSections B S hS p ⟶ awnSections B S hS,
      (∀ (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
        φ.app (op X) (colimitStage B S hS p 0 X a) =
          (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)).app (op X) a) ∧
      ∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
        QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
          Function.Bijective (φ.app (op X)) :=
  exists_bijective_hom_frobeniusColimitSections_of_isSheafification B S hS p hp hSp
    (absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS))
    (isSheaf_absoluteWeakNormalizationSections B S hS)
    (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))
    fun H hH β => existsUnique_hom_absoluteWeakNormalizationSections B S hS H hH β

end BigHOver

/-- **Stacks Project, Tag 0EVW.** Let `p` be a prime number.

(1) If `A` is an algebra over `𝔽_p`, then `colim_F A = A^{awn}`: the colimit of the Frobenius
tower of `A` is the absolute weak normalization of `A`, by a unique isomorphism compatible with
the canonical maps out of `A`.

(2) If `S` is a scheme over `𝔽_p` and `(Sch/S)_h` is a big h site over `S` as in Stacks 0EU1,
then the h sheafification of the structure sheaf `𝒪` — a sheaf of rings `G` with a map
`α : 𝒪 ⟶ G` initial among the maps from `𝒪` to sheaves of rings — sends a quasi-compact
quasi-separated object `X` to `colim_F Γ(X, 𝒪_X)`, by an identification agreeing with `α` on the
stage `0` of the Frobenius tower. -/
@[stacks 0EVW]
public theorem frobeniusColimit_absoluteWeakNormalization_and_hSheafificationSections (p : ℕ)
    (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    (∀ (A : Type u) [CommRing A] [Algebra (ZMod p) A],
      ∃! e : colimit (Algebra.frobeniusDiagram p A) ≅
          CommRingCat.of (Algebra.AbsoluteWeakNormalization A),
        colimit.ι (Algebra.frobeniusDiagram p A) 0 ≫ e.hom =
          CommRingCat.ofHom (algebraMap A (Algebra.AbsoluteWeakNormalization A))) ∧
    (∀ (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S),
      Stacks.Frobenius.IsInCharacteristic S p →
      ∀ (G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u}),
        Presheaf.IsSheaf (BigHOver.topology B S hS) G →
      ∀ α : (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⟶ G,
        (∀ H : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u},
          Presheaf.IsSheaf (BigHOver.topology B S hS) H →
          ∀ β : (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⟶ H, ∃! χ : G ⟶ H, α ≫ χ = β) →
        ∃ φ : BigHOver.frobeniusColimitSections B S hS p ⟶
            G ⋙ CategoryTheory.forget CommRingCat.{u},
          (∀ (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
            φ.app (op X) (BigHOver.colimitStage B S hS p 0 X a) = α.app (op X) a) ∧
          ∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
            QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
              Function.Bijective (φ.app (op X))) :=
  ⟨fun A _ _ => Algebra.existsUnique_frobeniusColimit_iso_absoluteWeakNormalization p hp A,
    fun B S hS hSp G hG α hα =>
      BigHOver.exists_bijective_hom_frobeniusColimitSections_of_isSheafification B S hS p hp hSp
        G hG α hα⟩

end AlgebraicGeometry

end
