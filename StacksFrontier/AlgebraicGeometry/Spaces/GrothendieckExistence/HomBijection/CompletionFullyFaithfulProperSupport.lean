module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealAdicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.InternalHomSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# Completion is fully faithful on modules with proper support

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `X` be an algebraic
space locally of finite type over `Spec A`, and let `F`, `G` be coherent
`𝒪_X`-modules the intersection of whose supports is proper over `Spec A`.  Then completion
along `I 𝒪_X` (Stacks 08B4) is bijective on morphisms `F ⟶ G`; in particular the completion
functor between the categories of coherent modules and of coherent adic systems with support
proper over `Spec A` (Stacks 08B8) is fully faithful.

## Main results

* `AlgebraicGeometry.Space.C1573.bijective_completionFunctor_map_of_isProperOver`: completion is
  bijective on morphisms of coherent modules whose supports meet in a set proper over `Spec A`.
* `AlgebraicGeometry.Space.C1573.completionFunctorProperOverFullyFaithful`: the completion functor
  on coherent modules with support proper over `Spec A` is fully faithful.

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] pointTopology

section Systems

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The transition maps of the two spellings of the completion agree. -/
theorem smallEtaleAdicQuotientTransition_eq (M : Modules.{u, u} B S hS F hF) (n : ℕ) :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M =
      idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.le_succ (n + 1)) M := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1 + 1) M)).1 ?_
  rw [smallEtaleAdicQuotientProjection_comp_transition]
  exact (π_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘 _ M).symm

/-- The maps `n + 1 ⟶ n` of the two spellings of the adic system of quotients agree. -/
theorem smallEtaleAdicQuotientSystem_map_eq (M : Modules.{u, u} B S hS F hF) (n : ℕ) :
    (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE (Nat.le_add_right n 1)).op =
      (adicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE (Nat.le_add_right n 1)).op := by
  rw [smallEtaleAdicQuotientSystem_map_succ, adicQuotientSystem_map,
    smallEtaleAdicQuotientTransition_eq]

/-- Morphisms between the two spellings of the completions agree. -/
def smallSystemHomEquiv (M N : Modules.{u, u} B S hS F hF) :
    (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶ smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) ≃
      (adicQuotientSystem B S hS F hF 𝓘 M ⟶ adicQuotientSystem B S hS F hF 𝓘 N) where
  toFun ψ := NatTrans.ofOpSequence (fun n => ψ.app (op n)) fun n => by
    rw [← smallEtaleAdicQuotientSystem_map_eq, ← smallEtaleAdicQuotientSystem_map_eq]
    exact ψ.naturality _
  invFun θ := NatTrans.ofOpSequence (fun n => θ.app (op n)) fun n => by
    rw [smallEtaleAdicQuotientSystem_map_eq, smallEtaleAdicQuotientSystem_map_eq]
    exact θ.naturality _
  left_inv ψ := NatTrans.ext (funext fun n => rfl)
  right_inv θ := NatTrans.ext (funext fun n => rfl)

/-- The equivalence of Stacks 08B6, granted chartwise bijectivity, evaluated on a family whose
image is known. -/
theorem smallEtaleInternalHomSmallAdicEquivOfBijective_apply_eq (M N : Modules.{u, u} B S hS F hF)
    (hb : ∀ U, Function.Bijective (adicSectionsMapAt B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
      (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N)
      (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) U))
    (x : adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N)))
    (γ : { γ : ∀ n : ℕ, smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M ⟶
          smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N //
        ∀ n : ℕ, smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M ≫ γ n =
          γ (n + 1) ≫ smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N })
    (h : smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N γ =
      smallEtaleInternalHomSmallAdicSectionsShrink B S hS F hF 𝓘 M N
        (adicSectionsMap B S hS F hF _ _ _ _ _
          (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) x)) :
    smallEtaleInternalHomSmallAdicEquivOfBijective B S hS F hF 𝓘 M N hb x =
      (systemHomEquiv B S hS F hF _ _ _ _).symm γ := by
  show (systemHomEquiv B S hS F hF _ _ _ _).symm
      ((Equiv.ofBijective _ (bijective_smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N)).symm
        (smallEtaleInternalHomSmallAdicSectionsShrink B S hS F hF 𝓘 M N
          (adicSectionsMap B S hS F hF _ _ _ _ _
            (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) x))) = _
  congr 1
  exact (Equiv.symm_apply_eq _).2 h.symm

/-- The map `M / 𝓘 ^ k M ⟶ N / 𝓘 ^ k N` induced by `M ⟶ N`. -/
def smallEtaleAdicQuotientMapOfHom (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 k M ⟶ smallEtaleAdicQuotient B S hS F hF 𝓘 k N :=
  cokernel.desc _ (φ ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k N)
    ((idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 k _).2 fun U r hr x =>
      (map_smul ((φ ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k N).val.app (op U)).hom
        r x).trans
        (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓘 k N U r hr _))

/-- The projection `M ⟶ M / 𝓘 ^ k M` followed by the induced map of quotients is `φ` followed by
the projection `N ⟶ N / 𝓘 ^ k N`. -/
@[reassoc (attr := simp)]
theorem smallEtaleAdicQuotientProjection_mapOfHom (k : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 k φ =
      φ ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k N :=
  cokernel.π_desc _ _ _

/-- The maps of quotients induced by `φ` commute with the transition maps. -/
theorem smallEtaleAdicQuotientMapOfHom_compat (n : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 (n + 1) φ =
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 (n + 1 + 1) φ ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1 + 1) M)).1 ?_
  rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
    smallEtaleAdicQuotientProjection_mapOfHom, smallEtaleAdicQuotientProjection_mapOfHom_assoc,
    smallEtaleAdicQuotientProjection_comp_transition]

/-- The map of quotients induced by `φ` agrees with `idealPowerQuotientMapOfHom`. -/
theorem smallEtaleAdicQuotientMapOfHom_eq (k : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) :
    smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 k φ =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 k φ :=
  (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M)).1 <|
    (smallEtaleAdicQuotientProjection_mapOfHom B S hS F hF 𝓘 k φ).trans
      (π_comp_idealPowerQuotientMapOfHom B S hS F hF 𝓘 k φ).symm

end Systems

section Main

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- Morphisms are the global sections of the small internal hom. -/
def internalHomSmallSectionsEquiv (M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    (M ⟶ N) ≃ (smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 M N).sections :=
  ((smallEtaleInternalHomSmallSectionsShrink B (Spec (.of A)) hA X.1 X.2 M N).trans
    (smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M N)).symm

variable [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]

/-- Sending a morphism `φ : M ⟶ N` to a global section of the internal hom, then to its system
of reductions modulo the powers of `I`, and then to a morphism of adic systems, gives the
completion of `φ`. -/
theorem smallSystemHomEquiv_adicEquiv_eq (M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    [IsCoherent B (Spec (.of A)) hA X.1 X.2 M] [IsCoherent B (Spec (.of A)) hA X.1 X.2 N]
    (φ : M ⟶ N) :
    smallSystemHomEquiv B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) M N
        (smallEtaleInternalHomSmallAdicEquiv B (Spec (.of A)) hA X.1 X.2
          (baseIdealSubmodule X.1 X.2 I)
          (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) M N
          (adicSectionsOfSection X I _ (internalHomSmallSectionsEquiv X M N φ))) =
      adicQuotientSystemMap B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) φ := by
  set 𝓘 := baseIdealSubmodule X.1 X.2 I
  let γ : { γ : ∀ n : ℕ, smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) M ⟶
          smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N //
        ∀ n : ℕ, smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) M ≫ γ n =
          γ (n + 1) ≫ smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N } :=
    ⟨fun n => smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) φ,
      fun n => smallEtaleAdicQuotientMapOfHom_compat B (Spec (.of A)) hA X.1 X.2 𝓘 n φ⟩
  have hσ : smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M N
      (smallEtaleInternalHomSmallSectionsShrink B (Spec (.of A)) hA X.1 X.2 M N
        (internalHomSmallSectionsEquiv X M N φ)) = φ :=
    ((smallEtaleInternalHomSmallSectionsShrink B (Spec (.of A)) hA X.1 X.2 M N).trans
      (smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M N)).apply_symm_apply φ
  have hh : smallEtaleInternalHomAdicSection B (Spec (.of A)) hA X.1 X.2 𝓘 M N γ =
      smallEtaleInternalHomSmallAdicSectionsShrink B (Spec (.of A)) hA X.1 X.2 𝓘 M N
        (adicSectionsMap B (Spec (.of A)) hA X.1 X.2 _ _ _ _ _
          (smallEtaleInternalHomSmallAdicComparison_compat B (Spec (.of A)) hA X.1 X.2 𝓘 M N)
          (adicSectionsOfSection X I _ (internalHomSmallSectionsEquiv X M N φ))) := by
    refine Subtype.ext (funext fun n => ?_)
    apply (smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M
      (smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N)).injective
    show smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M _
        ((smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M _).symm
          (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) M ≫
            smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) φ)) =
      smallEtaleInternalHomSectionsEquiv B (Spec (.of A)) hA X.1 X.2 M _
        (smallEtaleInternalHomSmallSectionsShrink B (Spec (.of A)) hA X.1 X.2 M _
          (SheafOfModules.sectionsMap
            (smallEtaleInternalHomSmallAdicComparisonApp B (Spec (.of A)) hA X.1 X.2 𝓘 M N n)
            (SheafOfModules.sectionsMap (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA
              X.1 X.2 𝓘 (n + 1) (smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 M N))
              (internalHomSmallSectionsEquiv X M N φ))))
    rw [Equiv.apply_symm_apply, ← SheafOfModules.sectionsMap_comp,
      smallEtaleAdicQuotientProjection_comp_smallComparisonApp,
      smallEtaleInternalHomSmallSectionsShrink_map, smallEtaleInternalHomSectionsEquiv_map, hσ,
      smallEtaleAdicQuotientProjection_mapOfHom]
  have hE := smallEtaleInternalHomSmallAdicEquivOfBijective_apply_eq B (Spec (.of A)) hA X.1 X.2 𝓘
    M N (bijective_smallAdicSectionsMapAt B (Spec (.of A)) hA X.1 X.2 𝓘
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) M N)
    (adicSectionsOfSection X I _ (internalHomSmallSectionsEquiv X M N φ)) γ hh
  refine NatTrans.ext (funext fun n => ?_)
  obtain ⟨n⟩ := n
  show (smallEtaleInternalHomSmallAdicEquivOfBijective B (Spec (.of A)) hA X.1 X.2 𝓘 M N
    (bijective_smallAdicSectionsMapAt B (Spec (.of A)) hA X.1 X.2 𝓘
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) M N)
    (adicSectionsOfSection X I _ (internalHomSmallSectionsEquiv X M N φ))).app (op n) = _
  rw [hE]
  exact smallEtaleAdicQuotientMapOfHom_eq B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) φ

end Main

section Registered

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- An algebraic space locally of finite type over a Noetherian base is locally Noetherian. -/
theorem fact_isLocallyNoetherian_of_baseObject [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA X.2
    (schemeSpace (baseObject A B hA)).2 f.hom hf
    (hasEtaleLocalProperty_isLocallyNoetherian_baseObject A B hA)⟩

/-- Morphisms in a full subcategory are in bijection with morphisms of the underlying objects. -/
private theorem bijective_fullSubcategory_hom {C : Type*} [Category C] {P : ObjectProperty C}
    (X Y : P.FullSubcategory) : Function.Bijective fun a : X ⟶ Y => a.hom :=
  ⟨fun _ _ h => ObjectProperty.hom_ext _ h, fun φ => ⟨ObjectProperty.homMk φ, rfl⟩⟩

/-- Let `A` be a Noetherian ring complete with
respect to an ideal `I`, let `X` be an algebraic space with a morphism
`f : X ⟶ Spec A` locally of finite type, and let `F`, `G` be coherent `𝒪_X`-modules such that the
intersection of their supports is proper over `Spec A`.  Then completion along `I 𝒪_X`
(Stacks 08B4) is a bijection
`Mor_{Coh(𝒪_X)}(F, G) ⟶ Mor_{Coh(X, I 𝒪_X)}(F^∧, G^∧)`. -/
theorem bijective_completionFunctor_map_of_isProperOver [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (F G : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hcl : IsClosed (supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj F.obj) ∩
      supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj G.obj)))
    (hp : IsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf _ hcl) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf
    Function.Bijective ((completionFunctor B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map
        (X := F) (Y := G)) := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf
  have hHc := isCoherent_smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 F.obj G.obj
  have hFft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X F.obj
  have hGft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X G.obj
  have hHft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X
    (smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 F.obj G.obj)
  have hHcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA X.1 X.2
    (smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 F.obj G.obj)
  have hsupp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        (smallEtaleInternalHomSmall B (Spec (.of A)) hA X.1 X.2 F.obj G.obj)) :=
    ⟨hHcl, isProperOver_of_subset B (Spec (.of A)) hA X.2 _ f.hom hf _ _ hHcl hcl
      (supportOfSheaf_smallEtaleInternalHomSmall_subset B (Spec (.of A)) hA X F.obj G.obj
        (IsCoherent.toIsQuasicoherentOnSite) hFft (IsCoherent.toIsQuasicoherentOnSite) hGft
        (IsCoherent.toIsQuasicoherentOnSite) hHft) hp⟩
  have hSF := sectionsFormal_of_hasProperSupport X Fact.out f hf _ hsupp I
  have hb := bijective_adicSectionsOfSection X I _ hSF
  refine (Function.Bijective.of_comp_iff' (bijective_fullSubcategory_hom _ _) _).1 ?_
  have key : (fun a : (completionFunctor B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).obj F ⟶
        (completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
          (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).obj G => a.hom) ∘
      (completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map (X := F) (Y := G) =
      (smallSystemHomEquiv B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) F.obj G.obj) ∘
        (smallEtaleInternalHomSmallAdicEquiv B (Spec (.of A)) hA X.1 X.2
          (baseIdealSubmodule X.1 X.2 I)
          (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) F.obj G.obj) ∘
        (adicSectionsOfSection X I _) ∘ (internalHomSmallSectionsEquiv X F.obj G.obj) ∘
          fun a : F ⟶ G => a.hom := by
    funext a
    exact (smallSystemHomEquiv_adicEquiv_eq X I F.obj G.obj a.hom).symm
  rw [key]
  exact (smallSystemHomEquiv _ _ _ _ _ _ _ _).bijective.comp
    ((Equiv.bijective _).comp
      (hb.comp ((Equiv.bijective _).comp (bijective_fullSubcategory_hom F G))))

/-- The completion functor of Stacks 08B8 is bijective on morphisms. -/
theorem bijective_completionFunctorProperOver_map [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (G H : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf
    Function.Bijective ((completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map
        (X := G) (Y := H)) := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf
  obtain ⟨hGcl, hGp⟩ := G.property
  obtain ⟨hHcl, -⟩ := H.property
  have hcl := hGcl.inter hHcl
  have hb := bijective_completionFunctor_map_of_isProperOver X I f hf G.obj H.obj hcl
    (isProperOver_of_subset B (Spec (.of A)) hA X.2 _ f.hom hf _ _ hcl hGcl
      Set.inter_subset_left hGp)
  exact (Function.Bijective.of_comp_iff' (bijective_fullSubcategory_hom _ _) _).1
    (hb.comp (bijective_fullSubcategory_hom G H))

/-- In the situation of
`AlgebraicGeometry.Space.C1573.bijective_completionFunctor_map_of_isProperOver`, the completion
functor `Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, I 𝒪_X)` of
Stacks 08B8 is fully faithful. -/
def completionFunctorProperOverFullyFaithful [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf
    (completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).FullyFaithful :=
  letI := fact_isLocallyNoetherian_of_baseObject X f hf
  haveI : (completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).Full :=
    ⟨fun {G H} => (bijective_completionFunctorProperOver_map X I f hf G H).2⟩
  haveI : (completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).Faithful :=
    ⟨fun {G H} => (bijective_completionFunctorProperOver_map X I f hf G H).1⟩
  Functor.FullyFaithful.ofFullyFaithful _

end Registered


end AlgebraicGeometry.Space.C1573

end
