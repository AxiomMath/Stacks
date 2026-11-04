module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.ComplementUnitCompletion
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections

/-!
# The chain (1) implies (4) of Stacks 0EKP on the complement of a closed subset

Let `B` be a Noetherian ring, let `𝔟 ⊆ B` be an ideal, let `g ∈ B` and let
`U = Spec(B) ∖ V(𝔟)`. Condition (1) of [Stacks, Tag 0EKP], in the shape the proof of Stacks 0EKS
quotes it, says that `U` is quasi-affine and that

`Γ(U, 𝒪_U) ⟶ lim_n Γ(U, (B / gⁿB)~)`

is bijective — the comparison Stacks 0EII produces,
`Stacks.Algebraization.ComplementTower.sectionsToLimit`. Condition (4) says that the completion
functor `Coh(𝒪_U) ⟶ Coh(U, g 𝒪_U)` of Stacks 0880 is fully faithful on the finite locally free
objects. This file proves the implication between them, and so discharges the hypothesis `hEKP`
carried by Stacks 0EKS and by the purity material above it.

## The argument

The termwise comparison of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.ComplementUnitCompletion`
identifies the completion of `𝒪_U` with the tower of Stacks 0EII, compatibly with the quotient
projections and with the transition maps. Read on global sections, that comparison turns
`Stacks.Algebraization.ComplementTower.sectionsToLimit` into the comparison of the theorem on
formal functions in degree zero, `Stacks.Algebraization.globalSectionsToLimit`, at the structure
sheaf — which is condition (3) of Stacks 0EKP there. From condition (3) at the structure sheaf,
`Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_isIso_globalSectionsToLimit`
gives condition (4).

Only the index shift has to be absorbed: the `n`-th term of the completion is the quotient by
the `(n+1)`-st power, while the tower of Stacks 0EII is indexed by the exponent itself. It is
absorbed on the side of Stacks 0EII, without comparing the two limits as objects. A compatible
family for Stacks 0EII is produced from a point of the limit of the completion by taking its
zeroth entry to be the image of the first under one transition map, which makes the
compatibility at index zero hold by construction; and two compatible families that agree from
index one on agree at index zero too, because there each is the image of its first entry.

## Main definitions

* `Stacks.Algebraization.complementUnitSections` and
  `Stacks.Algebraization.complementTermSections` — global sections on `U` of the structure sheaf
  and of the `n`-th term of its completion, read as sections of `B̃` and of `(B/gⁿ⁺¹B)~` over
  `Spec(B) ∖ V(𝔟)`.

## Main results

* `Stacks.Algebraization.complementTermSections_completionProjection` and
  `Stacks.Algebraization.complementTermSections_transition` — the identification of the sections
  carries the projections and the transition maps of the completion to those of Stacks 0EII.
* `Stacks.Algebraization.isIso_globalSectionsToLimit_unitCoherentModule` — **condition (1) of
  Stacks 0EKP, in the shape Stacks 0EII produces it, gives condition (3) at the structure
  sheaf.**
* `Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit`
  — **the chain (1) ⇒ (4) of Stacks 0EKP**, in exactly the shape in which it is carried as the
  hypothesis `hEKP` of Stacks 0EKS.

## Implementation notes

The sections of the restriction of a module along an open immersion over the whole of the open
subscheme are *the same module* as the sections of the module over the image open: Mathlib's
comparison `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity. What is not an
identity is the passage between `U.ι ''ᵁ ⊤` and `U` itself, which is
`AlgebraicGeometry.Scheme.Opens.ι_image_top`; the two restriction maps between them are mutually
inverse, so no `CategoryTheory.eqToHom` is needed, exactly as in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/RestrictSections.lean`.

`Stacks.Algebraization.bijective_app_top_presheaf_map` is stated for an arbitrary module rather
than applied inline at `(B/gⁿB)~`: with the module a variable its instances stay opaque, and the
elaborator reaches the answer at once, whereas inline at the associated sheaf of a quotient
module the search through the localization instances exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- Restriction along mutually inverse inclusions of opens is a bijection on sections. -/
public theorem bijective_presheaf_map_homOfLE {X : Scheme.{u}} (M : X.Modules)
    {V V' : X.Opens} (h₁ : V ≤ V') (h₂ : V' ≤ V) :
    Function.Bijective (M.presheaf.map (homOfLE h₁).op) :=
  Function.bijective_iff_has_inverse.2
    ⟨M.presheaf.map (homOfLE h₂).op,
      fun m => Stacks.AlgebraicGeometry.ModuleLimits.modules_presheaf_map_homOfLE_self h₁ h₂ m,
      fun m => Stacks.AlgebraicGeometry.ModuleLimits.modules_presheaf_map_homOfLE_self h₂ h₁ m⟩

/-- **Global sections of a module isomorphic to the restriction of `N` along an open immersion
are the sections of `N` over an open equal to the image.** The identification is the isomorphism
on global sections followed by restriction, and it is a bijection: the first factor is a
bijection because the morphism is an isomorphism, and the second because restriction along two
mutually inverse inclusions of opens does nothing. -/
public theorem bijective_app_top_presheaf_map {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M : X.Modules} {N : Y.Modules} (e : M ≅ (Scheme.Modules.restrictFunctor f).obj N)
    {V : Y.Opens} (h₁ : V ≤ f ''ᵁ (⊤ : X.Opens)) (h₂ : f ''ᵁ (⊤ : X.Opens) ≤ V) :
    Function.Bijective (fun x : Γ(M, (⊤ : X.Opens)) =>
      N.presheaf.map (homOfLE h₁).op (e.hom.app (⊤ : X.Opens) x)) :=
  (bijective_presheaf_map_homOfLE N h₁ h₂).comp
    (sectionsEquivOfIso e (⊤ : X.Opens)).bijective

/-- Restricting a section over `U` of the restriction of `M` and applying `φ` commute with
applying `φ` to the restriction of sections. -/
private theorem presheaf_map_restrictFunctor_map_app (B : Type u) [CommRing B] (b : Ideal B)
    {M N : (Spec (CommRingCat.of B)).Modules} (φ : M ⟶ N)
    (s : Γ(M, (complementZeroLocus B b).ι ''ᵁ
      (⊤ : (complementZeroLocus B b : Scheme).Opens))) :
    N.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op
        (φ.app _ s) =
      φ.app (complementZeroLocus B b)
        (M.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op s) :=
  (PresheafOfModules.naturality_apply φ.val
    (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op s).symm

variable (B : Type u) [CommRing B] (b : Ideal B) (g : B) (n : ℕ) [IsNoetherianRing B]

/-- Global sections of `𝒪_U` on `U = Spec(B) ∖ V(𝔟)`, read as sections of `B̃` over
`Spec(B) ∖ V(𝔟)`. -/
public def complementUnitSections :
    Γ((unitCoherentModule (complementZeroLocus B b : Scheme)).obj,
        (⊤ : (complementZeroLocus B b : Scheme).Opens)) →
      Γ((Spec (CommRingCat.of B)).unitModule, complementZeroLocus B b) :=
  fun x => (Spec (CommRingCat.of B)).unitModule.presheaf.map
    (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op
      ((complementUnitModuleIso B b).inv.app ⊤ x)

/-- The reading `Stacks.Algebraization.complementUnitSections` of global sections of `𝒪_U` as
sections of `B̃` over `Spec(B) ∖ V(𝔟)` is a bijection. -/
public theorem bijective_complementUnitSections :
    Function.Bijective (complementUnitSections B b) :=
  bijective_app_top_presheaf_map (complementZeroLocus B b).ι
    (complementUnitModuleIso B b).symm
    (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge
    (Scheme.Opens.ι_image_top (complementZeroLocus B b)).le

/-- Global sections of the `n`-th term of the completion of `𝒪_U`, read as sections of
`(B / gⁿ⁺¹B)~` over `Spec(B) ∖ V(𝔟)`. -/
public def complementTermSections :
    Γ(((completionFunctor (complementZeroLocus B b : Scheme)
            (complementPrincipalIdealSheaf B b g)).obj
          (unitCoherentModule (complementZeroLocus B b : Scheme))).obj.obj (op n),
        (⊤ : (complementZeroLocus B b : Scheme).Opens)) →
      Γ(tilde (ComplementTower.quotientModule B g (ModuleCat.of B B) (n + 1)),
        complementZeroLocus B b) :=
  fun x => (tilde (ComplementTower.quotientModule B g (ModuleCat.of B B) (n + 1))).presheaf.map
    (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op
      ((complementCompletionTermIso B b g n).hom.app ⊤ x)

/-- The reading `Stacks.Algebraization.complementTermSections` of global sections of the `n`-th
term of the completion of `𝒪_U` as sections of `(B / gⁿ⁺¹B)~` over `Spec(B) ∖ V(𝔟)` is
injective. -/
public theorem injective_complementTermSections :
    Function.Injective (complementTermSections B b g n) :=
  (bijective_app_top_presheaf_map (complementZeroLocus B b).ι
    (complementCompletionTermIso B b g n)
    (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge
    (Scheme.Opens.ι_image_top (complementZeroLocus B b)).le).1

/-- **The identification of the sections carries the projection of the completion to the
quotient projection of Stacks 0EII.** -/
public theorem complementTermSections_completionProjection
    (x : Γ((unitCoherentModule (complementZeroLocus B b : Scheme)).obj,
      (⊤ : (complementZeroLocus B b : Scheme).Opens))) :
    complementTermSections B b g n
        (Scheme.Modules.Hom.app (completionProjection (complementZeroLocus B b : Scheme)
          (complementPrincipalIdealSheaf B b g)
          (unitCoherentModule (complementZeroLocus B b : Scheme)) n) ⊤ x) =
      ComplementTower.sectionQuotientMap B b g (ModuleCat.of B B) (n + 1)
        (complementUnitSections B b x) := by
  refine (congrArg (fun t =>
      (tilde (ComplementTower.quotientModule B g (ModuleCat.of B B) (n + 1))).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op t) ?_).trans
    (presheaf_map_restrictFunctor_map_app B b _ _)
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ
        (⊤ : (complementZeroLocus B b : Scheme).Opens) x)
      (completionProjection_comp_complementCompletionTermIso B b g n)

/-- **The identification of the sections carries the transition maps of the completion to the
transition maps of the tower of Stacks 0EII.** -/
public theorem complementTermSections_transition
    (y : Γ(((completionFunctor (complementZeroLocus B b : Scheme)
            (complementPrincipalIdealSheaf B b g)).obj
          (unitCoherentModule (complementZeroLocus B b : Scheme))).obj.obj (op (n + 1)),
      (⊤ : (complementZeroLocus B b : Scheme).Opens))) :
    complementTermSections B b g n
        ((((completionFunctor (complementZeroLocus B b : Scheme)
              (complementPrincipalIdealSheaf B b g)).obj
            (unitCoherentModule (complementZeroLocus B b : Scheme))).obj.map
          (homOfLE (Nat.le_succ n)).op).app ⊤ y) =
      ComplementTower.sectionsTransition B b g (ModuleCat.of B B) (n + 1)
        (complementTermSections B b g (n + 1) y) := by
  refine (congrArg (fun t =>
      (tilde (ComplementTower.quotientModule B g (ModuleCat.of B B) (n + 1))).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_top (complementZeroLocus B b)).ge).op t) ?_).trans
    (presheaf_map_restrictFunctor_map_app B b _ _)
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ
        (⊤ : (complementZeroLocus B b : Scheme).Opens) y)
      (complementCompletionTermIso_transition B b g n)

/-- The comparison of the theorem on formal functions is normalized by the projections of the
completion on global sections. -/
public theorem globalSectionsToLimit_unit_apply
    (x : Γ((unitCoherentModule (complementZeroLocus B b : Scheme)).obj,
      (⊤ : (complementZeroLocus B b : Scheme).Opens))) :
    ConcreteCategory.hom (limit.π (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor (complementZeroLocus B b : Scheme)
              (complementPrincipalIdealSheaf B b g)).obj
            (unitCoherentModule (complementZeroLocus B b : Scheme)))) (op n))
        (ConcreteCategory.hom (globalSectionsToLimit (complementPrincipalIdealSheaf B b g)
          (unitCoherentModule (complementZeroLocus B b : Scheme))) x) =
      Scheme.Modules.Hom.app (completionProjection (complementZeroLocus B b : Scheme)
        (complementPrincipalIdealSheaf B b g)
        (unitCoherentModule (complementZeroLocus B b : Scheme)) n) ⊤ x :=
  ConcreteCategory.congr_hom (globalSectionsToLimit_π
    (complementPrincipalIdealSheaf B b g)
    (unitCoherentModule (complementZeroLocus B b : Scheme)) (op n)) x

/-- **Condition (1) of [Stacks, Tag 0EKP] in the shape Stacks 0EII produces it gives condition
(3) at the structure sheaf.** If `Γ(U, 𝒪_U) ⟶ lim_n Γ(U, (B/gⁿB)~)` is bijective, then the
comparison of the theorem on formal functions `Γ(U, 𝒪_U) ⟶ lim_n Γ(U, 𝒪_U / (g 𝒪_U)ⁿ 𝒪_U)` is
an isomorphism.

The two towers are identified termwise by
`Stacks.Algebraization.complementCompletionTermIso`, compatibly with the projections and with the
transition maps; the identification is read on global sections by
`Stacks.Algebraization.complementTermSections`. Only the index shift has to be absorbed, and it
is absorbed on the side of the tower of Stacks 0EII: its zeroth term is reached from its first
by one transition map, so a compatible family on the completion's indexing extends uniquely to
one on the indexing of Stacks 0EII, and two of the latter which agree from the first index on
agree everywhere. -/
public theorem isIso_globalSectionsToLimit_unitCoherentModule
    (h : Function.Bijective (ComplementTower.sectionsToLimit B b g (ModuleCat.of B B))) :
    IsIso (globalSectionsToLimit (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme))) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · intro x y hxy
    have key : ∀ m : ℕ,
        ComplementTower.sectionQuotientMap B b g (ModuleCat.of B B) (m + 1)
            (complementUnitSections B b x) =
          ComplementTower.sectionQuotientMap B b g (ModuleCat.of B B) (m + 1)
            (complementUnitSections B b y) := fun m =>
      (complementTermSections_completionProjection B b g m x).symm.trans
        ((congrArg (complementTermSections B b g m)
            ((globalSectionsToLimit_unit_apply B b g m x).symm.trans
              ((congrArg (fun t => ConcreteCategory.hom
                    (limit.π (Stacks.Coherent.globalSectionsSystem
                      ((completionFunctor (complementZeroLocus B b : Scheme)
                          (complementPrincipalIdealSheaf B b g)).obj
                        (unitCoherentModule (complementZeroLocus B b : Scheme)))) (op m)) t)
                  hxy).trans (globalSectionsToLimit_unit_apply B b g m y)))).trans
          (complementTermSections_completionProjection B b g m y))
    refine (bijective_complementUnitSections B b).1 (h.1 (Subtype.ext (funext fun m => ?_)))
    cases m with
    | zero =>
      exact ((ComplementTower.sectionsToLimit B b g (ModuleCat.of B B)
            (complementUnitSections B b x)).2 0).symm.trans
        ((congrArg (ComplementTower.sectionsTransition B b g (ModuleCat.of B B) 0)
            (key 0)).trans
          ((ComplementTower.sectionsToLimit B b g (ModuleCat.of B B)
            (complementUnitSections B b y)).2 0))
    | succ k => exact key k
  · intro z
    have hmem : (fun m => Nat.casesOn (motive := fun k =>
          ToType (ComplementTower.sectionsModPower B b g (ModuleCat.of B B) k)) m
        (ComplementTower.sectionsTransition B b g (ModuleCat.of B B) 0
          (complementTermSections B b g 0
            (ConcreteCategory.hom (limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor (complementZeroLocus B b : Scheme)
                  (complementPrincipalIdealSheaf B b g)).obj
                (unitCoherentModule (complementZeroLocus B b : Scheme)))) (op 0)) z)))
        (fun k => complementTermSections B b g k
          (ConcreteCategory.hom (limit.π (Stacks.Coherent.globalSectionsSystem
            ((completionFunctor (complementZeroLocus B b : Scheme)
                (complementPrincipalIdealSheaf B b g)).obj
              (unitCoherentModule (complementZeroLocus B b : Scheme)))) (op k)) z))) ∈
        ComplementTower.compatibleSections B b g (ModuleCat.of B B) := by
      intro m
      cases m with
      | zero => rfl
      | succ k =>
        exact (complementTermSections_transition B b g k
            (ConcreteCategory.hom (limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor (complementZeroLocus B b : Scheme)
                  (complementPrincipalIdealSheaf B b g)).obj
                (unitCoherentModule (complementZeroLocus B b : Scheme)))) (op (k + 1)))
              z)).symm.trans
          (congrArg (complementTermSections B b g k)
            (ConcreteCategory.congr_hom (limit.w (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor (complementZeroLocus B b : Scheme)
                  (complementPrincipalIdealSheaf B b g)).obj
                (unitCoherentModule (complementZeroLocus B b : Scheme))))
              (homOfLE (Nat.le_succ k)).op) z))
    obtain ⟨w, hw⟩ := h.2 ⟨_, hmem⟩
    obtain ⟨x, hx⟩ := (bijective_complementUnitSections B b).2 w
    exact ⟨x, Concrete.limit_ext _ _ _ fun j =>
      injective_complementTermSections B b g j.unop
        ((congrArg (complementTermSections B b g j.unop)
            (globalSectionsToLimit_unit_apply B b g j.unop x)).trans
          ((complementTermSections_completionProjection B b g j.unop x).trans
            ((congrArg (ComplementTower.sectionQuotientMap B b g (ModuleCat.of B B)
                (j.unop + 1)) hx).trans
              (congrArg (fun t => t.1 (j.unop + 1)) hw))))⟩

/-- **The chain (1) ⇒ (4) of [Stacks, Tag 0EKP], with condition (1) in the shape the proof of
Stacks 0EKS quotes it.** For every Noetherian ring `B`, every ideal `𝔟 ⊆ B` and every `g ∈ B`:
if `U = Spec(B) ∖ V(𝔟)` is quasi-affine and `Γ(U, 𝒪_U) ⟶ lim_n Γ(U, (B/gⁿB)~)` is bijective,
then the completion functor `Coh(𝒪_U) ⟶ Coh(U, g 𝒪_U)` of Stacks 0880 is fully faithful on the
finite locally free objects.

This is exactly the hypothesis `hEKP` carried by
`AlgebraicGeometry.LocalLefschetzSituation.fullyFaithful_finiteEtaleRestriction_of_annihilated`
and by `Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated`.

The proof is in two steps. Condition (1) in the shape Stacks 0EII produces it gives condition (3)
at the structure sheaf, `Stacks.Algebraization.isIso_globalSectionsToLimit_unitCoherentModule`:
the tower of Stacks 0EII and the completion of `𝒪_U` are the same tower. Condition (3) at the
structure sheaf then gives condition (4), by
`Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_isIso_globalSectionsToLimit`:
condition (3) propagates to every finite locally free coherent module by duality, and from there
the completion functor is bijective on each hom set because the source is presented by direct
sums of copies of `𝒪_X`. -/
public theorem completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit :
    ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (b : Ideal B) (g : B),
      Scheme.IsQuasiAffine (complementZeroLocus B b : Scheme) →
      Function.Bijective
        (Stacks.Algebraization.ComplementTower.sectionsToLimit B b g (ModuleCat.of B B)) →
      CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus B b : Scheme)
        (complementPrincipalIdealSheaf B b g) :=
  fun B _ _ b g hqa hsec =>
    completionFullyFaithfulOnFiniteLocallyFree_of_isIso_globalSectionsToLimit _ hqa
      (isIso_globalSectionsToLimit_unitCoherentModule B b g hsec)

end Stacks.Algebraization

end
