module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.RingTheory.AdicCompletion.HomCompletion
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# The completed internal hom computes the morphisms of the completions

**Stacks 0882.** Let `X` be a locally Noetherian scheme, `I` a quasi-coherent sheaf of ideals on
`X`, and `G`, `F` coherent `𝒪_X`-modules. Put `H = SheafHom_{𝒪_X}(G, F)`. Then

`lim_n H⁰(X, H / Iⁿ H) = Mor_{Coh(X, I)}(G^∧, F^∧)`,

the inverse limit of the global sections of the ideal-power quotients of `H` being the morphisms
of coherent adic systems between the completions of `G` and `F`.

The proof is Stacks', factored into four identifications. Three are formal: global sections
commute with the inverse limit; the global sections of an internal hom are the morphisms
(`internalHomSectionsTopEquiv`); and morphisms out of a completion are morphisms into the inverse
limit (`completionHomLimitEquiv`, the adjunction of `CompletionFunctor.Adjunction`). The
substance is the fourth, that the comparison

`lim_n H / Iⁿ H ⟶ SheafHom(G, lim_n F / Iⁿ F)`

of `CompletionFunctor.InternalHom` is an isomorphism. That is checked on the sections over an
affine open, where it becomes the algebraic statement `Hom_A(N, P)^∧ = Hom_A(N, P^∧)` of
Stacks 00MB for finite modules over a Noetherian ring.

## Main results

* `Stacks.Algebraization.completedSheafHomComparison_bijective_on_affine` — the comparison is
  bijective on the sections over an affine open.
* `Stacks.Algebraization.isIso_completedSheafHomComparison` — hence an isomorphism.
* `Stacks.Algebraization.completionInternalHomEquiv` — **the tag**, as an isomorphism of abelian
  groups.

## Implementation notes

The comparison is *not* an isomorphism level by level: the map `H / Iⁿ H ⟶ SheafHom(G, F / Iⁿ F)`
has kernel and cokernel annihilated by a power of `I` and no more (Stacks 09BB). Only the limit
is an isomorphism, which is why the affine computation is made at the level of the adic completion
rather than termwise.

Evaluation of the internal hom on affine sections is known to be *bijective* only when the target
is quasi-coherent (`internalHomEvaluation_bijective`), and quasi-coherence of `lim_n F / Iⁿ F` is
not available here. At the limit only injectivity is used (`internalHomEvaluation_injective`,
which needs no hypothesis on the target), and both halves of bijectivity of the comparison are
extracted from the identity `t ∘ c ∘ eH = a` with `a` and `eH` isomorphisms and `t` injective:
injectivity of `c` from that of `a`, and surjectivity because `a w = t z` forces `c (eH w) = z`.

Stacks states the tag for a Noetherian scheme. Only local Noetherianness is used — coherence of
the ideal-power quotients, Noetherianness of `Γ(X, U)` on affine opens, and finiteness of the
sections there — so the statement below is the slightly more general one.

## References

* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.SheafOfModules.InternalHom

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}

/-- **Evaluation of the internal hom on affine sections, as an isomorphism.** For `G`
quasi-coherent and `U` affine, a section of `SheafHom(G, M)` over `U` is exactly a
`Γ(X, U)`-linear map `Γ(G, U) → Γ(M, U)`. No hypothesis on `M` is needed: the content is the
`tilde ⊣ Γ` adjunction on `Spec Γ(X, U)`, which constrains only the source. -/
public noncomputable def internalHomEvaluationEquiv {X : Scheme.{u}} (G M : X.Modules)
    [G.IsQuasicoherent] (U : X.affineOpens) :
    ((sheafHomFunctor X G).obj M).val.obj (op U.1) ≃ₗ[Γ(X, U)]
      (Γ(G, U) →ₗ[Γ(X, U)] Γ(M, U)) :=
  LinearEquiv.ofBijective _ (internalHomEvaluation_bijective G M U)

/-- **The comparison of Stacks 0882 is bijective on the sections over an affine open.**

Over an affine open `U` write `A = Γ(X, U)`, `N = Γ(G, U)`, `P = Γ(F, U)`. The sections of the
limit of the completion of `H = SheafHom(G, F)` are the `I(U)`-adic completion of `Γ(H, U)`
(`completionSectionsEquiv`), and `Γ(H, U)` is `Hom_A(N, P)` (`internalHomEvaluationEquiv`); the
sections of `SheafHom(G, lim F / I ^ n F)` are the `A`-linear maps from `N` into the completion of
`P`. Under those identifications the comparison becomes
`Hom_A(N, P)^∧ = Hom_A(N, P^∧)`, which is `AdicCompletion.homCompletionEquiv`, i.e. Stacks 00MB.

The identification is checked on the image of `Γ(H, U)` and extended by density: the target is
`I(U)`-adically complete, so `AdicCompletion.linearMap_ext_of` applies. Evaluation at the limit is
only known to be *injective* (its target is not known to be quasi-coherent), which is why the two
halves of bijectivity are extracted from the identity rather than from an inverse. -/
public theorem completedSheafHomComparison_bijective_on_affine
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (U : X.affineOpens) :
    Function.Bijective ((completedSheafHomComparison (I := I) G F).val.app (op U.1)) := by
  have hGtf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (coherentObj G)
  have hFtf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (coherentObj F)
  have : (coherentObj G).IsQuasicoherent := hGtf.1
  have : (coherentObj G).IsFiniteType := hGtf.2
  have : (coherentObj F).IsQuasicoherent := hFtf.1
  have : (coherentObj F).IsFiniteType := hFtf.2
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(X, U.1) Γ(coherentObj G, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections (coherentObj G) U.2
  have : Module.Finite Γ(X, U.1) Γ(coherentObj F, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections (coherentObj F) U.2
  -- the three identifications
  let eH := completionSectionsEquiv X I (internalHomCoherent X G F) U
  let eF := completionSectionsEquiv X I F U
  let e0 := internalHomEvaluationEquiv (coherentObj G) (coherentObj F) U
  let p : Γ(limit (C := X.Modules)
        ((completionFunctor X I).obj (internalHomCoherent X G F)).obj, U.1) →ₗ[Γ(X, U.1)]
      Γ((sheafHomFunctor X (coherentObj G)).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj), U.1) :=
    ((completedSheafHomComparison G F).val.app (op U.1)).hom
  let a := ((AdicCompletion.congr (I.ideal U) e0).restrictScalars Γ(X, U.1)).trans
    (AdicCompletion.homCompletionEquiv (I.ideal U))
  let t : Γ((sheafHomFunctor X (coherentObj G)).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj), U.1) →ₗ[Γ(X, U.1)]
      (Γ(coherentObj G, U.1) →ₗ[Γ(X, U.1)]
        AdicCompletion (I.ideal U) Γ(coherentObj F, U.1)) :=
    (LinearEquiv.arrowCongr (LinearEquiv.refl Γ(X, U.1) Γ(coherentObj G, U.1))
      eF.symm).toLinearMap.comp
        (internalHomEvaluation (coherentObj G)
          (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) U.1)
  have ht : Function.Injective t := fun z z' hzz ↦
    internalHomEvaluation_injective (coherentObj G) _ U
      (LinearMap.ext fun y ↦ eF.symm.injective (LinearMap.congr_fun hzz y))
  have hcomplete : IsAdicComplete (I.ideal U)
      (AdicCompletion (I.ideal U) Γ(coherentObj F, U.1)) :=
    AdicCompletion.isAdicComplete (I.ideal U).fg_of_isNoetherianRing
  have hc : t.comp (p.comp eH.toLinearMap) = a.toLinearMap := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have hmaps : (LinearMap.applyₗ y).comp (t.comp (p.comp eH.toLinearMap)) =
        (LinearMap.applyₗ y).comp a.toLinearMap := by
      refine AdicCompletion.linearMap_ext_of (I.ideal U).fg_of_isNoetherianRing _ _ fun s => ?_
      have h1 := completionSectionsEquiv_of X I (internalHomCoherent X G F) U s
      have h2 := congrArg (fun k : (internalHomCoherent X G F).obj ⟶
          (sheafHomFunctor X (coherentObj G)).obj
            (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) =>
        k.val.app (op U.1) s) (completionToLimit_completedSheafHomComparison G F)
      have h3 := completionSectionsEquiv_of X I F U
        (internalHomEvaluation (coherentObj G) (coherentObj F) U.1 s y)
      have h4 := AdicCompletion.homCompletionEquiv_of_apply (I.ideal U)
        (e0 s) y
      have hstep : p (eH (AdicCompletion.of (I.ideal U)
            Γ((internalHomCoherent X G F).obj, U.1) s)) =
          ((sheafHomFunctor X (coherentObj G)).map
            (completionToLimit X I F)).val.app (op U.1) s := by
        change ((completedSheafHomComparison G F).val.app (op U.1)).hom
          (eH (AdicCompletion.of (I.ideal U) Γ((internalHomCoherent X G F).obj, U.1) s)) = _
        rw [h1]
        exact h2
      have hfinal := internalHomEvaluation_map (coherentObj G)
        (completionToLimit X I F) U.1 s y
      change eF.symm (internalHomEvaluation (coherentObj G)
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) U.1
          (p (eH (AdicCompletion.of (I.ideal U)
            Γ((internalHomCoherent X G F).obj, U.1) s))) y) = _
      rw [hstep, hfinal, ← h3, LinearEquiv.symm_apply_apply]
      change _ = AdicCompletion.homCompletionEquiv (I.ideal U)
        (AdicCompletion.congr (I.ideal U) e0
          (AdicCompletion.of (I.ideal U) Γ((internalHomCoherent X G F).obj, U.1) s)) y
      have hcg : AdicCompletion.congr (I.ideal U) e0
            (AdicCompletion.of (I.ideal U) Γ((internalHomCoherent X G F).obj, U.1) s) =
          AdicCompletion.of (I.ideal U)
            (Γ(coherentObj G, U.1) →ₗ[Γ(X, U.1)] Γ(coherentObj F, U.1)) (e0 s) :=
        AdicCompletion.map_of (I.ideal U) e0.toLinearMap s
      rw [hcg]
      exact h4.symm
    exact LinearMap.congr_fun hmaps x
  have hp : ∀ w, t (p (eH w)) = a w := fun w => LinearMap.congr_fun hc w
  refine ⟨fun {x x'} hxx => ?_, fun z => ?_⟩
  · have e : ∀ y, t (p y) = a (eH.symm y) := fun y =>
      (congrArg (fun w => t (p w)) (eH.apply_symm_apply y)).symm.trans (hp (eH.symm y))
    exact eH.symm.injective (a.injective ((e x).symm.trans (hxx ▸ e x')))
  · exact ⟨eH (a.symm (t z)),
      ht ((hp (a.symm (t z))).trans (a.apply_symm_apply (t z)))⟩


/-- **The comparison of Stacks 0882 is an isomorphism.** It is bijective on the sections over every
affine open, and the affine opens form a basis of the topology. -/
public theorem isIso_completedSheafHomComparison
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    IsIso (completedSheafHomComparison (I := I) G F) :=
  Stacks.LeibnizDerivation.isIso_of_isIso_app_basis _
    (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens)
    (fun U => (ConcreteCategory.isIso_iff_bijective _).mpr
      (completedSheafHomComparison_bijective_on_affine G F U))

/-- **Stacks 0882.** Let `X` be a locally Noetherian scheme, `I` a quasi-coherent sheaf of ideals
on `X` and `G`, `F` coherent `𝒪_X`-modules; put `H = SheafHom(G, F)`. Then

`lim_n H⁰(X, H / Iⁿ H) = Mor_{Coh(X, I)}(G^∧, F^∧)`.

The left side is the inverse limit of the global sections of the completion of the internal hom;
the right side the morphisms of coherent adic systems between the completions of `G` and `F`. The
identification is additive.

Four steps: global sections commute with the inverse limit; the comparison
`lim H / Iⁿ H ⟶ SheafHom(G, lim F / Iⁿ F)` is an isomorphism
(`isIso_completedSheafHomComparison`); the global sections of an internal hom are the morphisms
(`internalHomSectionsTopEquiv`); and a morphism `G ⟶ lim F / Iⁿ F` is a morphism of coherent adic
systems `G^∧ ⟶ F^∧` (`completionHomLimitEquiv`).

Stacks states this for a Noetherian scheme; it holds, as here, on any locally Noetherian one. -/
@[stacks 0882, sga "2 X 2.2" "partial"]
public noncomputable def completionInternalHomEquiv (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    limit (C := ModuleCat.{u} Γ(X, ⊤)) (Stacks.Coherent.globalSectionsSystem
      ((completionFunctor X I).obj (internalHomCoherent X G F))) ≃+
      ((completionFunctor X I).obj G ⟶ (completionFunctor X I).obj F) := by
  haveI hiso := isIso_completedSheafHomComparison (I := I) G F
  exact ((IsLimit.conePointUniqueUpToIso
        (@isLimitOfPreserves _ _ _ _ _ _ _
          (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
          (limit.cone ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (limit.isLimit ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (_root_.SheafOfModules.evaluationPreservesLimit _ (op ⊤)))
        (limit.isLimit (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor X I).obj
            (internalHomCoherent X G F))))).symm.toLinearEquiv.toAddEquiv).trans
    ((((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
          (@asIso _ _ _ _ (completedSheafHomComparison (I := I) G F)
            hiso)).toLinearEquiv.toAddEquiv).trans
      ((internalHomSectionsTopEquiv (coherentObj G)
          (limit (C := X.Modules) ((completionFunctor X I).obj F).obj)).trans
        (completionHomLimitEquiv G ((completionFunctor X I).obj F))))

end Stacks.Algebraization
