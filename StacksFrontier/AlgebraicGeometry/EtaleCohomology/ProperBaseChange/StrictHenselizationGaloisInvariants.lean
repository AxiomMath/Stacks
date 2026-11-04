module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationPuncturedStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.MathlibSiteGlobalSections

/-!
# The stalk of a direct image as Galois invariants

Let `φ : A ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S`, and suppose
the base change `A ×_S Spec 𝒪^{sh}_{S,s}` is the spectrum of a field `K` (for `φ = j` the
inclusion of the complement of a closed point `x` of a regular curve, `K = K^{sh}` is the fraction
field of the strict henselization at `x`,
`Stacks.EtaleCohomology.exists_directImageStalkIso_localizationAway`). Then for a sheaf of sets
`F` on `A` and any geometric point `t` of `Spec K`,
```
(φ_* F)_s ≃ (stalk at t of F|_{Spec K})^{Gal(K^sep/K)}.
```
For a boundary point of a curve this is the description of the local invariants `H⁰_loc` of
Weil II 1.8 as the invariants of `Gal(K^sep/K^{sh})`, the inertia group.

## Main results

* `Stacks.EtaleCohomology.nonempty_directImageStalkEquivGaloisFixedPoints` — the displayed
  bijection.
* `Stacks.EtaleCohomology.exists_directImageStalkEquivGaloisFixedPoints_localizationAway` — the
  case of a boundary point of a curve: `K^{sh} = 𝒪^{sh}[1/ϖ]`.

## References

* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme IsLocalRing

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The stalk of a direct image is a set of Galois invariants.** If `A ×_S Spec 𝒪^{sh}_{S,s}`
is the spectrum of a field `K`, the stalk at `s` of `φ_* F` is the set of elements of the stalk
of `F|_{Spec K}` at a geometric point `t` fixed by the absolute Galois group at `t`. -/
theorem nonempty_directImageStalkEquivGaloisFixedPoints {A : Scheme.{u}} (φ : A ⟶ S)
    [QuasiCompact φ] [QuasiSeparated φ] (F : Sheaf A.smallEtaleTopology (Type (u + 1)))
    (K : Type u) [Field K] (e : pullback φ (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
    (B' : BigEtaleSite.{u}) (hK : B'.Contains (Spec (.of K))) (t : GeometricPoint (Spec (.of K))) :
    Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
        (((smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology A)).obj F) ≃
      etaleStalkGaloisFixedPoints.{u, u + 1} B' K hK t
        ((SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).inverse.obj
          (((smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (u + 1))
              (smallEtaleTopology (Spec (.of K)))
              (smallEtaleTopology (pullback φ (strictHenselizationToBase B S hS s)))).obj
            ((smallEtaleInverseImage.{u, 0}
              (pullback.fst φ (strictHenselizationToBase B S hS s))).obj F)))) := by
  obtain ⟨i⟩ := nonempty_directImageStalkIsoStrictHenselizationGamma B S hS s φ F
  exact ⟨(i ≪≫ ((smallEtalePushforwardGammaIso.{u, 0} e.hom).app _).symm).toEquiv.trans
    (sheafΓEquivGaloisFixedPoints B' K hK t _)⟩

/-- **The stalk of `j_* F` at a boundary point of a curve as Galois invariants.** With the
hypotheses of `Stacks.EtaleCohomology.exists_directImageStalkIso_localizationAway`, the base
change `U ×_S Spec 𝒪^{sh}` is the spectrum of the field `K^{sh} = 𝒪^{sh}[1/ϖ]`, and the stalk of
`j_* F` at `s` is the set of Galois-fixed elements of the stalk of `F|_{Spec K^{sh}}` at any
geometric point. -/
theorem exists_directImageStalkEquivGaloisFixedPoints_localizationAway [IrreducibleSpace S]
    [IsNoetherianRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDomain ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDiscreteValuationRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    {U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U]
    (hx : s.hom (closedPoint s.residueField) ∉ Set.range j)
    (F : Sheaf U.smallEtaleTopology (Type (u + 1))) :
    ∃ (ϖ : ↥(etaleLocalRing B S hS s)) (_ : Irreducible ϖ) (hK : IsField (Localization.Away ϖ)),
      letI : Field (Localization.Away ϖ) := hK.toField
      ∃ (e : pullback j (strictHenselizationToBase B S hS s) ≅
          Spec (.of (Localization.Away ϖ))),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ϖ))) =
            pullback.snd j (strictHenselizationToBase B S hS s) ∧
          ∀ (B' : BigEtaleSite.{u}) (hK' : B'.Contains (Spec (.of (Localization.Away ϖ))))
            (t : GeometricPoint (Spec (.of (Localization.Away ϖ)))),
            Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
                (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
                  (smallEtaleTopology S) (smallEtaleTopology U)).obj F) ≃
              etaleStalkGaloisFixedPoints.{u, u + 1} B' (Localization.Away ϖ) hK' t
                ((SmallEtale.sheafEquiv B' (Spec (.of (Localization.Away ϖ))) hK'
                    (Type (u + 1))).inverse.obj
                  (((smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (u + 1))
                      (smallEtaleTopology (Spec (.of (Localization.Away ϖ))))
                      (smallEtaleTopology (pullback j (strictHenselizationToBase B S hS s)))).obj
                    ((smallEtaleInverseImage.{u, 0}
                      (pullback.fst j (strictHenselizationToBase B S hS s))).obj F)))) := by
  obtain ⟨hdom, hdvr⟩ := isDomain_and_isDiscreteValuationRing_etaleLocalRing B S hS s
  obtain ⟨ϖ, hϖ, e, he, -⟩ := exists_directImageStalkIso_localizationAway B S hS s j hx F
  have hfr := isFractionRing_localizationAway_of_irreducible ↥(etaleLocalRing B S hS s) hϖ
  have hK : IsField (Localization.Away ϖ) :=
    (IsFractionRing.toField ↥(etaleLocalRing B S hS s) (K := Localization.Away ϖ)).toIsField
  let : Field (Localization.Away ϖ) := hK.toField
  exact ⟨ϖ, hϖ, hK, e, he, fun B' hK' t ↦
    nonempty_directImageStalkEquivGaloisFixedPoints B S hS s j F _ e B' hK' t⟩

end Stacks.EtaleCohomology
