module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitGamma
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationLevelMatching

/-!
# Stalks of higher direct images

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, `s` a geometric point
of `S` and `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection. [Stacks, Tag 03Q9] asserts

* `(R^n f_* F)_s = H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` for an abelian sheaf `F` on `X_étale`;
* `(R^n f_* K)_s = H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)` for `K` in `D⁺(X_étale)`, `n ∈ ℤ`;
* `(Rf_* K)_s = RΓ_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)` in `D⁺(Ab)`.

The isomorphisms hold given two statements about the directed system of affine étale
neighbourhoods of `s` over an affine open neighbourhood `U` of the image of `s`, both instances
of [Stacks, Tag 03Q6]: the restrictions `F(X ×_S V) ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` exhibit
their target as a colimit, and cohomology of the limit vanishes when it vanishes on every level.

## Main definitions

* `AlgebraicGeometry.stalkHigherDirectImageIso` — the first isomorphism, for an abelian sheaf.
  Its `stacks 03Q9` registration is made by `add_to_stacks` in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/StrictlyHenselianDirectImageStalk.lean`, beside
  the case of a strictly henselian local base.
* `AlgebraicGeometry.stalkDerivedPushforwardHomologyIso` — the second, for `K ∈ D⁺(X_étale)`.
* `AlgebraicGeometry.stalkDerivedPushforwardIso` — the third, in `D⁺(Ab)`.
* `AlgebraicGeometry.affineNeighborhoodOfGeometricPoint` — a chosen affine open neighbourhood of
  the image of `s`.

## Main results

* `AlgebraicGeometry.stalkSectionsColimitInput` — the sections over `X ×_S Spec(𝒪^{sh}_{S,s})`
  are the colimit of the sections over the levels.
* `AlgebraicGeometry.stalkVanishingInput` — cohomology of `X ×_S Spec(𝒪^{sh}_{S,s})` vanishes in a
  degree when it vanishes on every level.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- A chosen affine open neighbourhood of the image of a geometric point. -/
def affineNeighborhoodOfGeometricPoint : S.Opens :=
  (exists_isAffineOpen_mem_and_subset (x := s.hom (closedPoint s.residueField))
    (U := ⊤) trivial).choose

/-- The chosen neighbourhood `affineNeighborhoodOfGeometricPoint s` is an affine open. -/
theorem isAffineOpen_affineNeighborhoodOfGeometricPoint :
    IsAffineOpen (affineNeighborhoodOfGeometricPoint s) :=
  (exists_isAffineOpen_mem_and_subset (x := s.hom (closedPoint s.residueField))
    (U := ⊤) trivial).choose_spec.1

/-- The image of `s` lies in `affineNeighborhoodOfGeometricPoint s`. -/
theorem mem_affineNeighborhoodOfGeometricPoint :
    s.hom (closedPoint s.residueField) ∈ affineNeighborhoodOfGeometricPoint s :=
  (exists_isAffineOpen_mem_and_subset (x := s.hom (closedPoint s.residueField))
    (U := ⊤) trivial).choose_spec.2.1

/-- The chosen neighbourhood `affineNeighborhoodOfGeometricPoint s` is an affine scheme. -/
private instance isAffine_affineNeighborhoodOfGeometricPoint :
    IsAffine (affineNeighborhoodOfGeometricPoint s : Scheme.{u}) :=
  isAffineOpen_affineNeighborhoodOfGeometricPoint s

variable (B : BigEtaleSite.{u}) (hS : B.Contains S) {X : Scheme.{u}} (f : X ⟶ S)

/-- For every abelian sheaf `F` on `X_étale`, the restrictions
`F(X ×_S V) ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, over the directed system of affine étale
neighbourhoods `V` of `s` over `affineNeighborhoodOfGeometricPoint s`, exhibit their target as
the colimit. -/
def StalkSectionsColimitInput : Prop :=
  ∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
    Nonempty (IsColimit (strictHenselizationSectionsCocone B S hS s
      (affineNeighborhoodOfGeometricPoint s) (mem_affineNeighborhoodOfGeometricPoint s) f F))

/-- Over the directed system of affine étale neighbourhoods `Z_a` of `s` over
`U = affineNeighborhoodOfGeometricPoint s`, étale cohomology of `X ×_S Spec(𝒪^{sh}_{S,s})` with
coefficients in the pullback of a sheaf on `X_U` vanishes in a degree as soon as it vanishes on
every level `Z_a ×_U X_U`. -/
def StalkVanishingInput : Prop :=
  ∀ (F : Sheaf (smallEtaleTopology (sourceOverOpen S (affineNeighborhoodOfGeometricPoint s)
      f).left) Ab.{u + 1}) (p : ℕ),
    (∀ a, IsZero (((Sheaf.Γ (smallEtaleTopology
        ((etaleNeighborhoodDirectedBaseChange B S hS s (affineNeighborhoodOfGeometricPoint s)
          (mem_affineNeighborhoodOfGeometricPoint s) f).obj a)) Ab.{u + 1}).rightDerived p).obj
          ((smallEtalePullbackAb (pullback.snd
            ((etaleNeighborhoodDirectedSystem B S hS s (affineNeighborhoodOfGeometricPoint s)
              (mem_affineNeighborhoodOfGeometricPoint s)).obj a).hom
            (sourceOverOpen S (affineNeighborhoodOfGeometricPoint s) f).hom)).obj F))) →
      IsZero (((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).rightDerived p).obj
          ((smallEtalePullbackAb (strictHenselizationToSourceOverOpen B S hS s
            (affineNeighborhoodOfGeometricPoint s) (mem_affineNeighborhoodOfGeometricPoint s)
              f)).obj F))

variable {B hS f s}

/-- The comparison `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an isomorphism, given the
degree-zero input. -/
theorem isIso_strictHenselizationSectionsMap_of_input
    (h0 : StalkSectionsColimitInput s B hS f) :
    IsIso (strictHenselizationSectionsMap B S hS s f) :=
  isIso_pushforwardStalkToSectionsAb_of_isColimit B S hS s _
    (mem_affineNeighborhoodOfGeometricPoint s) f fun F => (h0 F).some

/-- `p⁻¹` carries injective sheaves to `Γ`-acyclic ones, given the vanishing input. -/
theorem rightAcyclic_strictHenselizationPullback_of_input (hv : StalkVanishingInput s B hS f)
    (I : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (hI : Injective I) :
    (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
      Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj I) :=
  rightAcyclic_strictHenselizationPullback_of_isZero B S hS s _
    (mem_affineNeighborhoodOfGeometricPoint s) f hv I hI

/-- Given `StalkSectionsColimitInput` and `StalkVanishingInput`,
`(Rf_*K)_s ≅ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, naturally in `K ∈ D⁺(X_étale)`. -/
def stalkDerivedPushforwardIsoOfInputs (h0 : StalkSectionsColimitInput s B hS f)
    (hv : StalkVanishingInput s B hS f) :
    (smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus ≅
      (smallEtalePushforwardAb f).rightDerivedFunctorPlus ⋙
        (smallEtaleStalkAb s.hom).mapDerivedCategoryPlus :=
  have := isIso_strictHenselizationSectionsMap_of_input h0
  strictHenselizationStalkPlusIsoOfRightAcyclic B hS f s
    (strictHenselizationSectionsMap B S hS s f)
    (rightAcyclic_strictHenselizationPullback_of_input hv)

/-- Given `StalkSectionsColimitInput` and `StalkVanishingInput`,
`(Rⁿf_*K)_s ≅ Hⁿ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)` for `K ∈ D⁺(X_étale)` and `n ∈ ℤ`. -/
def stalkDerivedPushforwardHomologyIsoOfInputs (h0 : StalkSectionsColimitInput s B hS f)
    (hv : StalkVanishingInput s B hS f)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((smallEtalePushforwardAb f).rightDerivedFunctorPlus.obj K)) ≅
      (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} n).obj
        ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus.obj
          ((smallEtalePullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus.obj K)) :=
  have := isIso_strictHenselizationSectionsMap_of_input h0
  strictHenselizationStalkHomologyIsoOfRightAcyclic B hS f s
    (strictHenselizationSectionsMap B S hS s f)
    (rightAcyclic_strictHenselizationPullback_of_input hv) K n

/-- Given `StalkSectionsColimitInput` and `StalkVanishingInput`,
`(Rⁿf_*F)_s ≅ Hⁿ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` for an abelian sheaf `F` on `X_étale`. -/
def stalkHigherDirectImageIsoOfInputs (h0 : StalkSectionsColimitInput s B hS f)
    (hv : StalkVanishingInput s B hS f) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb f).rightDerivedPlus n).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedPlus n).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  have := isIso_strictHenselizationSectionsMap_of_input h0
  strictHenselizationStalkRightDerivedIsoOfRightAcyclic B hS f s
    (strictHenselizationSectionsMap B S hS s f)
    (rightAcyclic_strictHenselizationPullback_of_input hv) F n

/-- Given `StalkSectionsColimitInput` and `StalkVanishingInput`,
`(Rⁿf_*F)_s ≅ Hⁿ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` for `n : ℕ`, with Mathlib's right derived
functors. -/
def stalkHigherDirectImageRightDerivedIsoOfInputs (h0 : StalkSectionsColimitInput s B hS f)
    (hv : StalkVanishingInput s B hS f) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (n : ℕ) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb f).rightDerived n).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerived n).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  (smallEtaleStalkAb s.hom).mapIso (rightDerivedPlusObjIso _ F n).symm ≪≫
    stalkHigherDirectImageIsoOfInputs h0 hv F n ≪≫ rightDerivedPlusObjIso _ _ n

variable (B hS f s) in
/-- For `f` quasi-compact and quasi-separated, `StalkVanishingInput s B hS f` holds. -/
theorem stalkVanishingInput [QuasiCompact f] [QuasiSeparated f] : StalkVanishingInput s B hS f := by
  intro F p h
  exact Stacks.EtaleCohomology.ColimitBaseChange.isZero_rightDerivedΓ_limit_of_levels
    (affineNeighborhoodOfGeometricPoint s : Scheme.{u})
    (sourceOverOpen S (affineNeighborhoodOfGeometricPoint s) f)
    (etaleNeighborhoodDirectedSystem B S hS s (affineNeighborhoodOfGeometricPoint s)
      (mem_affineNeighborhoodOfGeometricPoint s)) F
    (strictHenselizationDirectedLimitCone B S hS s (affineNeighborhoodOfGeometricPoint s)
      (mem_affineNeighborhoodOfGeometricPoint s) f)
    (isLimitStrictHenselizationDirectedLimitCone B S hS s (affineNeighborhoodOfGeometricPoint s)
      (mem_affineNeighborhoodOfGeometricPoint s) f)
    (strictHenselizationToSourceOverOpen B S hS s (affineNeighborhoodOfGeometricPoint s)
      (mem_affineNeighborhoodOfGeometricPoint s) f)
    (fun a => (strictHenselizationDirectedLimitCone_π_snd B S hS s
      (affineNeighborhoodOfGeometricPoint s) (mem_affineNeighborhoodOfGeometricPoint s) f a).symm)
    p h

section DegreeZero

open Stacks.EtaleCohomology.ColimitBaseChange

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U) {X : Scheme.{u}} (f : X ⟶ S)
  (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})

/-- The degree-zero diagram of the neighbourhood system is the Γ-diagram of [Stacks, Tag 03Q6]
at the system of base changes `Z_a ×_U X_U` and the restriction of `F` to `X_U`. -/
def levelGammaDiagramIso :
    levelGammaDiagram B S hS s U hU f F ≅
      gammaDiagram (U : Scheme.{u}) (sourceOverOpen S U f)
        (etaleNeighborhoodDirectedSystem B S hS s U hU)
        ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The degree-zero cocone of the neighbourhood system, precomposed with
`levelGammaDiagramIso`, is the cocone `gammaCocone` at the limit cone with vertex
`X ×_S Spec(𝒪^{sh}_{S,s})`. -/
def levelGammaCoconeIso :
    (Cocone.precompose (levelGammaDiagramIso B S hS s U hU f F).inv).obj
        (gammaCocone (U : Scheme.{u}) (sourceOverOpen S U f)
          (etaleNeighborhoodDirectedSystem B S hS s U hU)
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)
          (strictHenselizationDirectedLimitCone B S hS s U hU f)
          (strictHenselizationToSourceOverOpen B S hS s U hU f)
          (fun a => (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a).symm)) ≅
      levelGammaCocone B S hS s U hU f F :=
  Cocone.ext (Iso.refl _) (fun a => by
    simp only [levelGammaCocone_ι_app, levelGammaDiagramIso, Iso.refl_hom]
    rfl)

/-- For `f` quasi-compact and quasi-separated and `U` affine, the cocone of restrictions
`F(X ×_S N_a) ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` over the neighbourhood system is a colimit
cocone. -/
def isColimitStrictHenselizationSectionsCocone [QuasiCompact f] [QuasiSeparated f]
    [IsAffine (U : Scheme.{u})] :
    IsColimit (strictHenselizationSectionsCocone B S hS s U hU f F) :=
  isColimitStrictHenselizationSectionsCoconeOfLevelGamma B S hS s U hU f F
    (IsColimit.ofIsoColimit
      ((IsColimit.precomposeInvEquiv (levelGammaDiagramIso B S hS s U hU f F) _).symm
        (isColimitGammaCocone (T := (U : Scheme.{u})) (X := sourceOverOpen S U f)
          (Z := etaleNeighborhoodDirectedSystem B S hS s U hU)
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)
          (strictHenselizationDirectedLimitCone B S hS s U hU f)
          (strictHenselizationToSourceOverOpen B S hS s U hU f)
          (fun a => (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a).symm)
          (isLimitStrictHenselizationDirectedLimitCone B S hS s U hU f)))
      (levelGammaCoconeIso B S hS s U hU f F))

end DegreeZero

variable (B hS f s) in
/-- For `f` quasi-compact and quasi-separated, `StalkSectionsColimitInput s B hS f` holds. -/
@[sga "4 VIII 5.1" "special case"]
theorem stalkSectionsColimitInput [QuasiCompact f] [QuasiSeparated f] :
    StalkSectionsColimitInput s B hS f := fun F =>
  ⟨isColimitStrictHenselizationSectionsCocone B S hS s _ (mem_affineNeighborhoodOfGeometricPoint s)
    f F⟩

/-! ### Stacks 03Q9 -/

section Tag03Q9

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) {X : Scheme.{u}} (f : X ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] (s : GeometricPoint S)

/-- For `f : X ⟶ S` quasi-compact and quasi-separated, `s` a geometric point of `S` and
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection,
`(R^n f_* F)_s ≅ H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` for every abelian sheaf `F` on `X_étale`
and every `n`. -/
@[sga "4 IX 4.1.1" "more general"]
def stalkHigherDirectImageIso (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (n : ℕ) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb f).rightDerived n).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerived n).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  stalkHigherDirectImageRightDerivedIsoOfInputs (stalkSectionsColimitInput s B hS f)
    (stalkVanishingInput s B hS f) F n

/-- For `f : X ⟶ S` quasi-compact and quasi-separated, `K` in `D⁺(X_étale)` and `n : ℤ`,
`(R^n f_* K)_s ≅ H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`. -/
@[stacks 03Q9 "second assertion, for `K` in `D^+(X_étale)` and `n` in `ℤ`: `(R^n f_* K)_s = \
H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}K)`, the cohomology objects of the right derived functors \
on the bounded below derived categories"]
def stalkDerivedPushforwardHomologyIso
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((smallEtalePushforwardAb f).rightDerivedFunctorPlus.obj K)) ≅
      (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} n).obj
        ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus.obj
          ((smallEtalePullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus.obj K)) :=
  stalkDerivedPushforwardHomologyIsoOfInputs (stalkSectionsColimitInput s B hS f)
    (stalkVanishingInput s B hS f) K n

/-- For `f : X ⟶ S` quasi-compact and quasi-separated,
`(Rf_* K)_s ≅ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)` in `D⁺(Ab)`, naturally in `K ∈ D⁺(X_étale)`. -/
@[stacks 03Q9 "third assertion: `(Rf_* K)_s = RΓ_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}K)` in \
`D^+(Ab)`, as an isomorphism of functors on `D^+(X_étale)`, the stalk and `p^{-1}` acting \
degreewise"]
def stalkDerivedPushforwardIso :
    (smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus ≅
      (smallEtalePushforwardAb f).rightDerivedFunctorPlus ⋙
        (smallEtaleStalkAb s.hom).mapDerivedCategoryPlus :=
  stalkDerivedPushforwardIsoOfInputs (stalkSectionsColimitInput s B hS f)
    (stalkVanishingInput s B hS f)

end Tag03Q9

end AlgebraicGeometry

end
