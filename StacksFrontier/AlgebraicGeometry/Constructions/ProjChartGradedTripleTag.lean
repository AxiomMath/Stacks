module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTriple
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaMoreover

/-!
# Stacks Tag 01NK

The whole statement of [Stacks, Tag 01NK] in one declaration, `tag01NK`.

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj A`, `T` a scheme, `L` an invertible
`𝒪_T`-module and `ψ : A → Γ_*(T, L)` a graded map, in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. The tag's objects are:

* `U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`: `GradedSections.coveringOpen`;
* `r_{L, ψ} : U(ψ) ⟶ X`: `GradedSections.glued`;
* `θ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`:
  `Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta`, a homomorphism of sheaves of
  `ℤ`-graded algebras, which preserves the unit.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intValue)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild
open Stacks.AlgebraicGeometry.ProjChartGradedTriple
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (veroneseAt
  iSup_nonvanishingOpen_le_coveringOpen)
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (IsCompatible)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedTripleTag

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- Let `A` be a graded ring, `X = Proj A`, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a homomorphism of graded rings. Put
`U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`. Then `ψ` induces the canonical morphism
`r_{L, ψ} = ψ.glued : U(ψ) ⟶ X` and the map of `ℤ`-graded algebras
`θ = theta 𝒜 ψ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`, and:

1. `U(ψ)` is the union of the `T_{ψ(f)}` (by definition);
2. `θ` preserves the unit;
3. **property (1)**: `r_{L, ψ}^{-1}(D₊(f)) = T_{ψ(f)}` for `f ∈ A_+` homogeneous;
4. **property (2)**: for every `d ≥ 0` and `a ∈ A_d`, `θ` carries the pullback of the global
   section of `𝒪_X(d)` attached to `a` (the map of [Stacks, Tag 01MP]) to `ψ(a)|_{U(ψ)}` — the
   commutativity of the square of the tag;
5. **the characterization**: every triple `(U', r', θ')` — an open of `T`, a morphism
   `U' ⟶ X` and a map of graded algebras `r'^*(⨁ 𝒪_X(d)) ⟶ ⨁ L^{⊗ d}|_{U'}` — with properties
   (1) and (2) is `(U(ψ), r_{L, ψ}, θ)`;
6. **the final assertion**: for `d ≥ 1` and an open `V ⊆ T` on which the sections `ψ(A_d)`
   generate `L^{⊗ d}|_V`, the pair `(φ, α)` of [Stacks, Tag 01N8] for
   `ψ|_{A^{(d)}} : A^{(d)} → Γ_*(V, L^{⊗ d})` exists and is unique, and for it
   `r_{L, ψ}|_V = φ` and the restriction of the degree-`d` part of `θ` to `V`, read through the
   canonical identifications `(r_{L, ψ}|_V)^*𝒪_X(d) = φ^*𝒪_X(d)` and
   `L^{⊗ d}|_{U(ψ)}|_V = L|_V^{⊗ d}`, is `α`.

The value `ψ(a)` is read in the tensor powers of [Stacks, Tag 01CU] that the Laurent algebra is
made of, through the canonical comparison
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue`.
The sections `ψ(A_d)` generate `L^{⊗ d}|_V` exactly when their nonvanishing opens cover `V`. -/
@[stacks 01NK "the open U(psi), the morphism r_{L,psi} : U(psi) -> Proj A and the unital map of \
Z-graded algebras theta : r^*(sum_d O_X(d)) -> sum_d L^{tensor d}|_{U(psi)}; properties (1) and \
(2); every triple (U', r', theta') with (1) and (2) equals (U(psi), r, theta); and for d >= 1 and \
an open V on which psi(A_d) generates L^{tensor d}, the pair (phi, alpha) attached to the Veronese \
restriction of psi to V exists uniquely, r|_V = phi, and theta|_V in degree d equals alpha"]
theorem tag01NK :
    ψ.coveringOpen
        = ⨆ p : (e : ℕ) × 𝒜 (e + 1),
            nonvanishingOpen T (natTensorPow L (p.1 + 1)) (ψ.toFun (p.1 + 1) p.2)
      ∧ SheafOfModules.sectionsMap ((theta 𝒜 ψ).app 0)
          (Stacks.Conormal.gradedPullback ψ.glued
            (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).one
        = (laurentRestrict 𝒜 ψ).one
      ∧ (∀ {e : ℕ} {f : A} (hf : f ∈ 𝒜 e), 0 < e →
          ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
            = nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
      ∧ (∀ (d : ℕ) {a : A} (ha : a ∈ 𝒜 d),
          ((theta 𝒜 ψ).app (d : ℤ)).val.app (op ⊤)
              (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 (d : ℤ)) ⊤ ⊤
                (fun _ _ => trivial) (degreeSection 𝒜 d ⟨a, ha⟩))
            = resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩)
                (ψ.coveringOpen.ι ''ᵁ ⊤))
      ∧ (∀ t : Triple 𝒜 L, IsTriple ψ t → t = canonicalTriple ψ)
      ∧ (∀ {d : ℕ} (hd : 0 < d) {V : T.Opens}
          (hVgen : V ≤ ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)),
          (∃! p : Pair 𝒜 (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d) d,
              IsCompatible 𝒜 (veroneseAt 𝒜 (GradedSections.pullback V.ι ψ) d) p) ∧
          ∀ p : Pair 𝒜 (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d) d,
            IsCompatible 𝒜 (veroneseAt 𝒜 (GradedSections.pullback V.ι ψ) d) p →
            ∃ h : T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd))
                ≫ ψ.glued = toProj 𝒜 p.1,
              (Scheme.Modules.pullbackCongr h.symm).hom.app (twistM 𝒜 (d : ℤ))
                ≫ (Scheme.Modules.pullbackComp
                    (T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)))
                    ψ.glued).inv.app (twistM 𝒜 (d : ℤ))
                ≫ (Scheme.Modules.pullback
                    (T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)))).map
                    ((theta 𝒜 ψ).app (d : ℤ))
                ≫ (Scheme.Modules.pullback
                    (T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)))).map
                    ((Scheme.Modules.restrictFunctorIsoPullback ψ.coveringOpen.ι).hom.app
                      (tensorPowerModule T L (d : ℤ)))
                ≫ (Scheme.Modules.pullbackComp
                    (T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)))
                    ψ.coveringOpen.ι).hom.app (tensorPowerModule T L (d : ℤ))
                ≫ (Scheme.Modules.pullbackCongr (T.homOfLE_ι _)).hom.app
                    (tensorPowerModule T L (d : ℤ))
                ≫ (Scheme.Modules.pullback V.ι).map (powCompare L d).inv
                ≫ (pullbackNatTensorPowIso V.ι L d).inv
                = p.2.hom) :=
  ⟨rfl, theta_map_one ψ, isClauseOne_glued ψ, isClauseTwo_theta ψ,
    fun _ h => eq_canonicalTriple h,
    fun hd _ hVgen => Stacks.AlgebraicGeometry.ProjChartGradedThetaMoreover.moreover 𝒜 ψ hd hVgen⟩

end Stacks.AlgebraicGeometry.ProjChartGradedTripleTag

end
