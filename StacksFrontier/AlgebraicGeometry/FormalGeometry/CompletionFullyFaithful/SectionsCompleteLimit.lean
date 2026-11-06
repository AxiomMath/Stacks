module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete

/-!
# Infinitesimal section completeness is the comparison of the theorem on formal functions

Let `X` be a locally Noetherian scheme, `i : Z ⟶ X` a closed immersion with ideal sheaf
`I = i.ker`, and `Y_n` the infinitesimal neighbourhoods of `i`. For a coherent module `F` there
are two ways of saying that the global sections of `F` are determined by the infinitesimal data
along `Z`:

* the universal property of `lim_n Γ(Y_n, F|_{Y_n})`, which is
  `Stacks.Algebraization.IsInfinitesimalSectionsComplete` — every compatible family of sections
  over the neighbourhoods has a unique antecedent in `Γ(X, F)`;
* invertibility of the comparison `Γ(X, F) ⟶ lim_n Γ(X, F / Iⁿ F)` of the theorem on formal
  functions in degree zero, which is `Stacks.Algebraization.globalSectionsToLimit`.

This file proves that the two agree.

## Main results

* `Stacks.Algebraization.completionTermSectionsEquiv_globalSectionsToLimit` — the `n`-th component
  of the comparison is the restriction of a global section to the `n`-th infinitesimal
  neighbourhood, once the global sections of the `n`-th term of the completion are identified with
  the sections over that neighbourhood by the Stacks 0EL1 comparison
  `Stacks.Algebraization.completionTermSectionsEquiv`.
* `Stacks.Algebraization.pullbackGlobalSections_nthInfinitesimalNeighbourhood_compatible` and
  `Stacks.Algebraization.completionTermSectionsEquiv_limit_π_compatible` — the restrictions of a
  global section to the infinitesimal neighbourhoods, and the components of an element of the
  limit, are compatible families of sections.
* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isInfinitesimalSectionsComplete` — **the
  forward direction**: infinitesimal section completeness makes the comparison of the theorem on
  formal functions an isomorphism.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_globalSectionsToLimit` and
  `Stacks.Algebraization.isIso_globalSectionsToLimit_iff_isInfinitesimalSectionsComplete` — the
  converse and the resulting equivalence.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

private theorem app_comp_apply {W : Scheme.{u}} {M N P : W.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (U : W.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app (φ ≫ ψ) U x =
      Scheme.Modules.Hom.app ψ U (Scheme.Modules.Hom.app φ U x) := rfl

/-! ### The components of the comparison -/

section Components

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  [F.obj.IsQuasicoherent]

/-- **The restrictions of a global section to the infinitesimal neighbourhoods are compatible.** -/
public theorem pullbackGlobalSections_nthInfinitesimalNeighbourhood_compatible
    (t : Γ(F.obj, (⊤ : X.Opens))) {n m : ℕ} (h : n ≤ m) :
    pullbackSectionsMap F.obj (nthInfinitesimalNeighbourhoodTransition i h)
        (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i m) F.obj t) =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F.obj t :=
  (congrArg (pullbackSectionsMap F.obj (nthInfinitesimalNeighbourhoodTransition i h))
      (completionTermSectionsEquiv_projection i F m t).symm).trans
    ((completionTermSectionsEquiv_transition i F h _).trans
      ((congrArg (completionTermSectionsEquiv i F n)
          ((app_comp_apply (completionProjection X i.ker F m)
              (((completionFunctor X i.ker).obj F).obj.map (homOfLE h).op) ⊤ t).symm.trans
            (congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : X.Opens) t)
              (completionProjection_naturality_le X i.ker F h)))).trans
        (completionTermSectionsEquiv_projection i F n t)))

/-- **The `n`-th component of the comparison of the theorem on formal functions is restriction to
the `n`-th infinitesimal neighbourhood**, read through the Stacks 0EL1 identification of the
global sections of the `n`-th term of the completion with the sections over that
neighbourhood. -/
public theorem completionTermSectionsEquiv_globalSectionsToLimit (n : ℕ)
    (t : Γ(F.obj, (⊤ : X.Opens))) :
    completionTermSectionsEquiv i F n
        ((limit.π (C := ModuleCat.{u} Γ(X, ⊤))
            (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
            (op n)).hom ((globalSectionsToLimit i.ker F).hom t)) =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F.obj t :=
  (congrArg (completionTermSectionsEquiv i F n)
      (ConcreteCategory.congr_hom (globalSectionsToLimit_π i.ker F (op n)) t)).trans
    (completionTermSectionsEquiv_projection i F n t)

/-- **The components of an element of the limit form a compatible family of sections over the
infinitesimal neighbourhoods.** -/
public theorem completionTermSectionsEquiv_limit_π_compatible
    (z : limit (C := ModuleCat.{u} Γ(X, ⊤))
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)))
    {n m : ℕ} (h : n ≤ m) :
    pullbackSectionsMap F.obj (nthInfinitesimalNeighbourhoodTransition i h)
        (completionTermSectionsEquiv i F m
          ((limit.π (C := ModuleCat.{u} Γ(X, ⊤))
            (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
            (op m)).hom z)) =
      completionTermSectionsEquiv i F n
        ((limit.π (C := ModuleCat.{u} Γ(X, ⊤))
          (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
          (op n)).hom z) :=
  (completionTermSectionsEquiv_transition i F h _).trans
    (congrArg (completionTermSectionsEquiv i F n)
      (ConcreteCategory.congr_hom
        (limit.w (C := ModuleCat.{u} Γ(X, ⊤))
          (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
          (homOfLE h).op) z))

/-- A compatible family of global sections of the terms of the completion, as a cone with vertex
the ring of global functions viewed as a module over itself: the `j`-th leg sends `r` to
`r • x j`. -/
private def sectionsFamilyCone
    (x : ∀ j : ℕᵒᵖ,
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).obj j)
    (hx : ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).map f).hom
        (x j) = x j') :
    Cone (C := ModuleCat.{u} Γ(X, ⊤))
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)) where
  pt := ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)
  π :=
    { app := fun j => ModuleCat.ofHom
        (Y := (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor X i.ker).obj F)).obj j)
        (LinearMap.toSpanSingleton _ _ (x j))
      naturality := fun j j' f => by
        refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
        change (show Γ(X, ⊤) from r) • x j' =
          ((Stacks.Coherent.globalSectionsSystem
            ((completionFunctor X i.ker).obj F)).map f).hom ((show Γ(X, ⊤) from r) • x j)
        rw [map_smul, hx j j' f] }

omit [IsClosedImmersion i] [F.obj.IsQuasicoherent] in
/-- The legs of that cone are multiplication into the members of the family. -/
private theorem sectionsFamilyCone_π_app_apply
    (x : ∀ j : ℕᵒᵖ,
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).obj j)
    (hx : ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).map f).hom
        (x j) = x j') (j : ℕᵒᵖ) (r : Γ(X, ⊤)) :
    ((sectionsFamilyCone i F x hx).π.app j).hom r = r • x j := rfl

/-- The element of the limit attached to a compatible family: the image of `1` under the map
induced by the cone. -/
private def sectionsFamilyLimitElement
    (x : ∀ j : ℕᵒᵖ,
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).obj j)
    (hx : ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).map f).hom
        (x j) = x j') :
    limit (C := ModuleCat.{u} Γ(X, ⊤))
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)) :=
  (limit.lift (C := ModuleCat.{u} Γ(X, ⊤))
    (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
    (sectionsFamilyCone i F x hx)).hom (1 : Γ(X, ⊤))

omit [IsClosedImmersion i] [F.obj.IsQuasicoherent] in
/-- The components of that element are the members of the family. -/
private theorem limit_π_sectionsFamilyLimitElement
    (x : ∀ j : ℕᵒᵖ,
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).obj j)
    (hx : ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).map f).hom
        (x j) = x j') (j : ℕᵒᵖ) :
    (limit.π (C := ModuleCat.{u} Γ(X, ⊤))
        (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)) j).hom
      (sectionsFamilyLimitElement i F x hx) = x j :=
  (ConcreteCategory.congr_hom (limit.lift_π (sectionsFamilyCone i F x hx) j)
      (1 : Γ(X, ⊤))).trans
    ((sectionsFamilyCone_π_app_apply i F x hx j 1).trans (one_smul _ _))

/-- The comparison sends `t` to `z` exactly when all restrictions of `t` to the infinitesimal
neighbourhoods are the components of `z`. -/
private theorem globalSectionsToLimit_eq_iff
    (t : Γ(F.obj, (⊤ : X.Opens)))
    (z : limit (C := ModuleCat.{u} Γ(X, ⊤))
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))) :
    (globalSectionsToLimit i.ker F).hom t = z ↔ ∀ n : ℕ,
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F.obj t =
        completionTermSectionsEquiv i F n
          ((limit.π (C := ModuleCat.{u} Γ(X, ⊤))
            (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
            (op n)).hom z) := by
  refine ⟨fun h n => ?_, fun h => Concrete.limit_ext _ _ _ fun j => ?_⟩
  · subst h
    exact (completionTermSectionsEquiv_globalSectionsToLimit i F n t).symm
  · refine (completionTermSectionsEquiv i F j.unop).injective ?_
    exact (completionTermSectionsEquiv_globalSectionsToLimit i F j.unop t).trans (h j.unop)

end Components

/-! ### The comparison of the theorem on formal functions in degree zero -/

/-- **Infinitesimal section completeness makes the comparison of the theorem on formal functions
an isomorphism.** Let `i : Z ⟶ X` be a closed immersion into a locally Noetherian scheme, with
ideal sheaf `I = i.ker`, and let `F` be a coherent module whose global sections are exactly the
compatible systems of sections over the infinitesimal neighbourhoods of `i`. Then
`Γ(X, F) ⟶ lim_n Γ(X, F / Iⁿ F)` is an isomorphism. -/
public theorem isIso_globalSectionsToLimit_of_isInfinitesimalSectionsComplete
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : IsInfinitesimalSectionsComplete i F.obj) :
    IsIso (globalSectionsToLimit i.ker F) := by
  have hcoh : F.obj.IsCoherent := F.property
  have hqc : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun t t' ht => ?_, fun z => ?_⟩
  · obtain ⟨t₀, -, huniq⟩ := hF
      (fun n => pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F.obj t)
      (fun n m h => pullbackGlobalSections_nthInfinitesimalNeighbourhood_compatible i F t h)
    exact (huniq t fun n => rfl).trans (huniq t' fun n =>
      ((globalSectionsToLimit_eq_iff i F t' _).1 rfl n).trans
        ((globalSectionsToLimit_eq_iff i F t _).1 ht n).symm).symm
  · obtain ⟨t, ht, -⟩ := hF
      (fun n => completionTermSectionsEquiv i F n
        ((limit.π (C := ModuleCat.{u} Γ(X, ⊤))
          (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F))
          (op n)).hom z))
      (fun n m h => completionTermSectionsEquiv_limit_π_compatible i F z h)
    exact ⟨t, (globalSectionsToLimit_eq_iff i F t z).2 ht⟩

/-- **The converse.** If the comparison of the theorem on formal functions is an isomorphism in
degree zero, then the global sections of `F` are exactly the compatible systems of sections over
the infinitesimal neighbourhoods of `i`. -/
public theorem isInfinitesimalSectionsComplete_of_isIso_globalSectionsToLimit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hiso : IsIso (globalSectionsToLimit i.ker F)) :
    IsInfinitesimalSectionsComplete i F.obj := by
  have hcoh : F.obj.IsCoherent := F.property
  have hqc : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  have hbij := (ConcreteCategory.isIso_iff_bijective (globalSectionsToLimit i.ker F)).1 hiso
  intro s hs
  obtain ⟨x, hx⟩ : ∃ x : ∀ j : ℕᵒᵖ,
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X i.ker).obj F)).obj j,
      ∀ j : ℕᵒᵖ, completionTermSectionsEquiv i F j.unop (x j) = s j.unop :=
    ⟨fun j => (completionTermSectionsEquiv i F j.unop).symm (s j.unop),
      fun j => Equiv.apply_symm_apply _ _⟩
  have hxc : ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((Stacks.Coherent.globalSectionsSystem
        ((completionFunctor X i.ker).obj F)).map f).hom (x j) = x j' := by
    intro j j' f
    have hle : j'.unop ≤ j.unop := leOfHom f.unop
    refine Eq.trans (congrArg (fun g : j ⟶ j' => ((Stacks.Coherent.globalSectionsSystem
      ((completionFunctor X i.ker).obj F)).map g).hom (x j))
        (Subsingleton.elim f (homOfLE hle).op)) ?_
    refine (completionTermSectionsEquiv i F j'.unop).injective ?_
    refine (completionTermSectionsEquiv_transition i F hle (x j)).symm.trans ?_
    exact ((congrArg (pullbackSectionsMap F.obj
        (nthInfinitesimalNeighbourhoodTransition i hle)) (hx j)).trans
      (hs j'.unop j.unop hle)).trans (hx j').symm
  obtain ⟨t, htz⟩ := hbij.2 (sectionsFamilyLimitElement i F x hxc)
  have htn : ∀ n : ℕ,
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F.obj t = s n := fun n =>
    ((globalSectionsToLimit_eq_iff i F t _).1 htz n).trans
      ((congrArg (completionTermSectionsEquiv i F n)
        (limit_π_sectionsFamilyLimitElement i F x hxc (op n))).trans (hx (op n)))
  exact ⟨t, htn, fun t' ht' => hbij.1 ((globalSectionsToLimit_eq_iff i F t' _).2 fun n =>
    (ht' n).trans ((htn n).symm.trans ((globalSectionsToLimit_eq_iff i F t _).1 rfl n)))⟩

/-- **Infinitesimal section completeness is the theorem on formal functions in degree zero.** For
a coherent module on a locally Noetherian scheme and a closed immersion `i`, the global sections
are the inverse limit of the sections over the infinitesimal neighbourhoods of `i` precisely when
the comparison `Γ(X, F) ⟶ lim_n Γ(X, F / i.kerⁿ F)` is an isomorphism. -/
public theorem isIso_globalSectionsToLimit_iff_isInfinitesimalSectionsComplete
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    IsIso (globalSectionsToLimit i.ker F) ↔ IsInfinitesimalSectionsComplete i F.obj :=
  ⟨isInfinitesimalSectionsComplete_of_isIso_globalSectionsToLimit i F,
    isIso_globalSectionsToLimit_of_isInfinitesimalSectionsComplete i F⟩

end Stacks.Algebraization

end
