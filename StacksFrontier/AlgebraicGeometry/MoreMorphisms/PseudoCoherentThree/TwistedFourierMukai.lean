module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukaiQCoh
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing

/-!
# The twisted Fourier–Mukai computation in the proof of Stacks 0CSL

Let `A` be a ring and `f : X ⟶ Spec A` quasi-compact and quasi-separated, and let `p`, `q` be the
two projections of `X ×_A ℙᵐ_A`. For `K ∈ D_QCoh(𝒪_X)`, `E ∈ D_QCoh(𝒪_{X ×_A ℙᵐ_A})` and
`i ∈ ℤ`, the proof of [Stacks, Tag 0CSL] computes

`RΓ(ℙᵐ_A, Rq_*(Lp^*K ⊗^𝐋 E) ⊗^𝐋 𝒪(i)) = RΓ(X, K ⊗^𝐋 Rp_*(E ⊗^𝐋 Lq^*𝒪(i)))`

in `D(A)`, by the projection formula of [Stacks, Tag 08EU] twice and Leray.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOverCompIso`: `A`-linear Leray for a composite,
  `RΓ_A(Y, -) ≅ RΓ_A(Z, Rg_* -)` for `g : Y ⟶ Z` over `Spec A`.
* `AlgebraicGeometry.nonempty_derivedGlobalSectionsOver_fourierMukai_iso`: the comparison for
  any commutative square of quasi-compact quasi-separated morphisms over `Spec A`.
* `AlgebraicGeometry.nonempty_derivedGlobalSectionsOver_chowTwist_iso`: the comparison of the
  source, at `X ×_A ℙᵐ_A` and the twists `𝒪(i)`.

## Implementation notes

The derived tensor product is `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`,
the one [Stacks, Tag 0CSK] (`DerivedChowFourierMukaiQCoh`) and the projection formula are stated
with; the standard model of the derived categories is seated at a raised priority, as there.

## References

* [Stacks Project, Tag 0CSL](https://stacks.math.columbia.edu/tag/0CSL)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow

/-- **Leray over the base ring, for a composite.** For `g : Y ⟶ Z` and `h : Z ⟶ Spec A`,
`RΓ_A(Y, -) ≅ RΓ_A(Z, Rg_* -)`, the `A`-linear derived global sections of `Y` being formed along
`g ≫ h`. Both sides are `RΓ(Spec A, -)` of the derived direct image along `g ≫ h`
(`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`, [Stacks, Tag 0D5W]), and derived
direct image is compatible with composition. -/
def derivedGlobalSectionsOverCompIso {A : Type u} [CommRing A] {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (h : Z ⟶ Spec (CommRingCat.of A)) :
    derivedGlobalSectionsOver (g ≫ h) ≅
      derivedPushforward (ofScheme g) ⋙ derivedGlobalSectionsOver h :=
  derivedGlobalSectionsOverPushforwardIso (g ≫ h) ≪≫
    Functor.isoWhiskerRight (derivedPushforwardCompIso (ofScheme g) (ofScheme h)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverPushforwardIso h).symm

/-- Shorthand for the derived tensor product of the 0CSK development. -/
local notation "𝐓" X => Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (Scheme.sheaf X)

/-- **The twisted Fourier–Mukai comparison of global sections.** Let `p : Y ⟶ X` and
`q : Y ⟶ P` be quasi-compact quasi-separated morphisms of schemes with `q ≫ π = p ≫ f` for
structure morphisms `f : X ⟶ Spec A` and `π : P ⟶ Spec A`. For `K ∈ D_QCoh(𝒪_X)`,
`E ∈ D_QCoh(𝒪_Y)` and `O ∈ D_QCoh(𝒪_P)` there is an isomorphism in `D(A)`

`RΓ(P, Rq_*(Lp^*K ⊗^𝐋 E) ⊗^𝐋 O) ≅ RΓ(X, K ⊗^𝐋 Rp_*(E ⊗^𝐋 Lq^*O))`.

This is the computation in the proof of [Stacks, Tag 0CSL]: the projection formula of
[Stacks, Tag 08EU] along `q`, Leray along `q` and along `p` over `A`
(`AlgebraicGeometry.derivedGlobalSectionsOverCompIso`), associativity and commutativity of the
derived tensor product ([Stacks, Tag 0FPT]), and the projection formula along `p`. -/
theorem nonempty_derivedGlobalSectionsOver_fourierMukai_iso {A : Type u} [CommRing A]
    {X P Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (π : P ⟶ Spec (CommRingCat.of A)) (p : Y ⟶ X) (q : Y ⟶ P) (hcond : q ≫ π = p ≫ f)
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact q] [QuasiSeparated q]
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (E : DerivedCategory Y.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent)
    (O : DerivedCategory P.Modules)
    (hO : ∀ n : ℤ, ((DerivedCategory.homologyFunctor P.Modules n).obj O).IsQuasicoherent) :
    Nonempty ((derivedGlobalSectionsOver π).obj
      (((𝐓 P).obj ((derivedPushforward (ofScheme q)).obj
          (((𝐓 Y).obj ((derivedPullback (ofScheme p)).obj K)).obj E))).obj O) ≅
      (derivedGlobalSectionsOver f).obj
        (((𝐓 X).obj K).obj ((derivedPushforward (ofScheme p)).obj
            (((𝐓 Y).obj E).obj ((derivedPullback (ofScheme q)).obj O))))) := by
  have hpK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj
      ((derivedPullback (ofScheme p)).obj K)).IsQuasicoherent := fun n =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel p K hK n
  have hqO : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj
      ((derivedPullback (ofScheme q)).obj O)).IsQuasicoherent := fun n =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel q O hO n
  have h1 :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      q inferInstance inferInstance _ O
      (TorFormula.isQuasicoherent_homology_derivedTensor Y _ E hpK hE) hO
  have h2 :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      p inferInstance inferInstance _ K
      (TorFormula.isQuasicoherent_homology_derivedTensor Y _ _ hE hqO) hK
  let TY := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf
  let TX := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf
  exact ⟨(derivedGlobalSectionsOver π).mapIso (@asIso _ _ _ _ _ h1) ≪≫
    ((derivedGlobalSectionsOverCompIso q π).app _).symm ≪≫
    eqToIso (congrArg (fun g => (derivedGlobalSectionsOver g).obj
      (((𝐓 Y).obj (((𝐓 Y).obj ((derivedPullback (ofScheme p)).obj K)).obj E)).obj
        ((derivedPullback (ofScheme q)).obj O))) hcond) ≪≫
    (derivedGlobalSectionsOverCompIso p f).app _ ≪≫
    (derivedGlobalSectionsOver f).mapIso ((derivedPushforward (ofScheme p)).mapIso
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator Y.sheaf TY _ _ _ ≪≫
        TY.braidingIso (Stacks.RingedSpace.toRingedSite Y.toRingedSpace) _ _) ≪≫
      (@asIso _ _ _ _ _ h2).symm ≪≫
      TX.braidingIso (Stacks.RingedSpace.toRingedSite X.toRingedSpace) _ _)⟩

open Stacks.AlgebraicGeometry.ProjTwistTensorPow in
/-- **The displayed computation of [Stacks, Tag 0CSL].** In the setting of [Stacks, Tag 0CSJ],
with `p` and `q` the two projections of `X ×_A ℙᵐ_A`, for `K ∈ D_QCoh(𝒪_X)`,
`E ∈ D_QCoh(𝒪_{X ×_A ℙᵐ_A})` and every `i ∈ ℤ`,

`RΓ(ℙᵐ_A, Rq_*(Lp^*K ⊗^𝐋 E) ⊗^𝐋 𝒪(i)) ≅ RΓ(X, K ⊗^𝐋 Rp_*(E ⊗^𝐋 Lq^*𝒪(i)))`

in `D(A)`. The source has `Rq_*` in its last line where `Rp_*` is meant. -/
theorem nonempty_derivedGlobalSectionsOver_chowTwist_iso {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f] (m : ℕ)
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (E : DerivedCategory
      (pullback f (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘
        Spec (CommRingCat.of A))).Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor _ n).obj E).IsQuasicoherent) (i : ℤ) :
    Nonempty ((derivedGlobalSectionsOver
        (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))).obj
      (((𝐓 (projectiveSpaceOver m (Spec (CommRingCat.of A)))).obj
        ((derivedPushforward (ofScheme (pullback.snd f
          (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))))).obj
          (((𝐓 (pullback f (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘
              Spec (CommRingCat.of A)))).obj
            ((derivedPullback (ofScheme (pullback.fst f
              (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))))).obj
                K)).obj E))).obj
        ((DerivedCategory.singleFunctor
          (projectiveSpaceOver m (Spec (CommRingCat.of A))).Modules 0).obj
          (twistOver m (Spec (CommRingCat.of A)) i))) ≅
      (derivedGlobalSectionsOver f).obj
        (((𝐓 X).obj K).obj
          ((derivedPushforward (ofScheme (pullback.fst f
              (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))))).obj
            (((𝐓 (pullback f (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘
              Spec (CommRingCat.of A)))).obj E).obj
              ((derivedPullback (ofScheme (pullback.snd f
                (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))))).obj
                ((DerivedCategory.singleFunctor
                  (projectiveSpaceOver m (Spec (CommRingCat.of A))).Modules 0).obj
                  (twistOver m (Spec (CommRingCat.of A)) i))))))) := by
  have : IsProper (projectiveSpaceOver m (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) :=
    isProper_projectiveSpaceOver m _
  exact nonempty_derivedGlobalSectionsOver_fourierMukai_iso f _ _ _ pullback.condition.symm K hK E
    hE _
    (fun n => isQuasicoherent_homology_singleFunctor_obj _ _ inferInstance n)

end AlgebraicGeometry

end
