module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison

/-!
# Sections of the internal hom over an affine open

Let `X` be a scheme, `G` a quasi-coherent `𝒪_X`-module, `M` an `𝒪_X`-module and `U ⊆ X` an
affine open. A section of `SheafHom(G, M)` over `U` is a morphism `G|_U ⟶ M|_U` on the slice
site over `U`, and `Stacks.Algebraization.internalHomEvaluation` reads off its component at the
terminal object of that site, a `Γ(X, U)`-linear map `Γ(G, U) → Γ(M, U)`. This file proves that
this comparison is bijective.

## Main definitions

* `Stacks.Algebraization.internalHomRestrictEquiv` — the sections of `SheafHom(G, M)` over an
  open `U` are the morphisms `G|_U ⟶ M|_U` of modules on the open subscheme `U`.

## Main results

* `Stacks.Algebraization.specΓ_map_bijective` — on the spectrum of a ring, taking global
  sections is bijective on morphisms out of a quasi-coherent module, with no hypothesis on the
  target.
* `Stacks.Algebraization.sectionsTop_bijective` — the same statement on an arbitrary affine
  scheme: a morphism of modules out of a quasi-coherent module is the same datum as a linear map
  on global sections.
* `Stacks.Algebraization.internalHomEvaluation_injective` — a section of `SheafHom(G, M)` over an
  affine open is determined by its component at the terminal object of the slice site, for `G`
  quasi-coherent and `M` arbitrary.
* `Stacks.Algebraization.internalHomEvaluation_bijective` — that component may moreover be
  prescribed arbitrarily, so evaluation identifies `Γ(SheafHom(G, M), U)` with
  `Hom_{Γ(X,U)}(Γ(G, U), Γ(M, U))`, again with no hypothesis on `M`.

## Implementation notes

Global sections over `⊤` of a module on the open subscheme `U` are the sections over
`U.ι ''ᵁ ⊤`, which is `U` only up to `Scheme.Opens.ι_image_top`, so the comparisons here pass
through restriction along that equality.

`Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful` gives the hom-set bijection in one
step but requires both modules to be quasi-coherent, whereas `specΓ_map_bijective` asks nothing
of the target.

## References

* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

/-! ### Global sections of a module on an affine scheme -/

/-- **Global sections are bijective on morphisms out of a quasi-coherent module on a spectrum.**
The target `G` is an arbitrary module. -/
public theorem specΓ_map_bijective {R : CommRingCat.{u}} (F G : (Spec R).Modules)
    [F.IsQuasicoherent] :
    Function.Bijective (moduleSpecΓFunctor.map :
      (F ⟶ G) → (moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G)) := by
  have : IsIso ((tilde.adjunction (R := R)).counit.app F) :=
    (inferInstance : IsIso F.fromTildeΓ)
  let adj := tilde.adjunction (R := R)
  let c := asIso (adj.counit.app F)
  let e : (F ⟶ G) ≃ (moduleSpecΓFunctor.obj F ⟶ moduleSpecΓFunctor.obj G) :=
    (c.symm.homCongr (Iso.refl G)).trans (adj.homEquiv _ G)
  have he : ∀ f : F ⟶ G, e f = moduleSpecΓFunctor.map f := by
    intro f
    change adj.homEquiv _ G (adj.counit.app F ≫ f ≫ 𝟙 G) = _
    rw [Category.comp_id, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
      Adjunction.right_triangle_components, Category.id_comp]
  have h : Function.Bijective (fun f : F ⟶ G => e f) := e.bijective
  simpa only [he] using h

/-- **On an affine scheme a morphism out of a quasi-coherent module is a linear map of global
sections.** The target `B` is an arbitrary module. -/
public theorem sectionsTop_bijective {Y : Scheme.{u}} [IsAffine Y] (A B : Y.Modules)
    [A.IsQuasicoherent] :
    Function.Bijective (fun h : A ⟶ B =>
      show Γ(A, ⊤) →ₗ[Γ(Y, ⊤)] Γ(B, ⊤) from (h.val.app (op ⊤)).hom) := by
  have hpb : (Scheme.Modules.pullback (isAffineOpen_top Y).fromSpec).IsEquivalence := by
    rw [IsAffineOpen.fromSpec_top]
    exact Stacks.Coherent.pullback_isEquivalence_of_iso Y.isoSpec.symm
  have hr : (Scheme.Modules.restrictFunctor (isAffineOpen_top Y).fromSpec).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful
      (Scheme.Modules.pullback (isAffineOpen_top Y).fromSpec)).ofIso
      (Scheme.Modules.restrictFunctorIsoPullback (isAffineOpen_top Y).fromSpec).symm
  have : (A.restrict (isAffineOpen_top Y).fromSpec).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (isAffineOpen_top Y).fromSpec A
  let eA := affineSectionsEquiv A ⊤ (isAffineOpen_top Y)
  let eB := affineSectionsEquiv B ⊤ (isAffineOpen_top Y)
  let e : (A ⟶ B) ≃ (Γ(A, ⊤) →ₗ[Γ(Y, ⊤)] Γ(B, ⊤)) :=
    (hr.homEquiv (X := A) (Y := B)).trans
      ((Equiv.ofBijective _ (specΓ_map_bijective
        (A.restrict (isAffineOpen_top Y).fromSpec)
        (B.restrict (isAffineOpen_top Y).fromSpec))).trans
        (ModuleCat.homEquiv.trans (LinearEquiv.arrowCongr eA eB).toEquiv))
  have he : ∀ h : A ⟶ B,
      e h = show Γ(A, ⊤) →ₗ[Γ(Y, ⊤)] Γ(B, ⊤) from (h.val.app (op ⊤)).hom := by
    intro h
    apply LinearMap.ext
    intro x
    change eB (((Scheme.Modules.restrictFunctor (isAffineOpen_top Y).fromSpec).map h).app ⊤
      (eA.symm x)) = _
    rw [affineSectionsEquiv_naturality, LinearEquiv.apply_symm_apply]
    rfl
  have hb : Function.Bijective (fun h : A ⟶ B => e h) := e.bijective
  simpa only [he] using hb

/-! ### Sections of the internal hom as morphisms on the open subscheme -/

/-- **A section of `SheafHom(G, M)` over `U` is a morphism `G|_U ⟶ M|_U` of modules on the open
subscheme `U`.** It identifies the sections over `U` with the morphisms on the slice site over
`U`, and these with morphisms of modules on `U` by `Scheme.Modules.overEquiv`, under which the
restriction of a module from `X` corresponds to its restriction along `U.ι`
(`Scheme.Modules.overFunctorEquiv`). -/
public noncomputable def internalHomRestrictEquiv {X : Scheme.{u}} (G M : X.Modules)
    (U : X.Opens) :
    ((sheafHomFunctor X G).obj M).val.obj (op U) ≃ (G.restrict U.ι ⟶ M.restrict U.ι) :=
  (SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).homEquiv.symm.trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (((Scheme.Modules.overFunctorEquiv U).app G).homCongr
        ((Scheme.Modules.overFunctorEquiv U).app M)))

/-- The global sections of the morphism attached to a section `f` of the internal hom are the
component of `f` at the object `U.ι ''ᵁ ⊤` of the slice site. -/
private lemma internalHomRestrictEquiv_app_top {X : Scheme.{u}} (G M : X.Modules) (U : X.Opens)
    (f : ((sheafHomFunctor X G).obj M).val.obj (op U)) (x : Γ(G.restrict U.ι, ⊤)) :
    (internalHomRestrictEquiv G M U f).val.app (op ⊤) x =
      f.app (op (Over.mk (homOfLE (U.ι_image_le (⊤ : (U : Scheme).Opens))))) x := rfl

/-- The components of a section `f` of the internal hom at `U.ι ''ᵁ ⊤` and at the terminal object
`Over.mk (𝟙 U)` of the slice site agree under restriction along `U.ι ''ᵁ ⊤ = U`. -/
private lemma internalHom_app_ι_image_top {X : Scheme.{u}} (G M : X.Modules) (U : X.Opens)
    (f : ((sheafHomFunctor X G).obj M).val.obj (op U))
    (y : Γ(G, U.ι ''ᵁ (⊤ : (U : Scheme).Opens))) :
    M.presheaf.map (eqToHom U.ι_image_top.symm).op
        (f.app (op (Over.mk (homOfLE (U.ι_image_le (⊤ : (U : Scheme).Opens))))) y) =
      f.app (op (Over.mk (𝟙 U))) (G.presheaf.map (eqToHom U.ι_image_top.symm).op y) := by
  let i : (Over.mk (𝟙 U) : Over U) ⟶ Over.mk (homOfLE (U.ι_image_le (⊤ : (U : Scheme).Opens))) :=
    Over.homMk (eqToHom U.ι_image_top.symm) (Subsingleton.elim _ _)
  exact (congrArg (fun k => (ConcreteCategory.hom k) y) (f.naturality i.op)).symm

/-! ### Transporting a hom-module to the open subscheme -/

/-- The scalar action on the sections of a restriction along `U.ι` is the scalar action on the
sections of the ambient scheme. -/
private lemma restrict_ι_smul {X : Scheme.{u}} (G : X.Modules) (U : X.Opens)
    (V : (U : Scheme).Opens) (r : Γ((U : Scheme), V)) (s : Γ(G.restrict U.ι, V)) :
    (r • s : Γ(G.restrict U.ι, V)) =
      (show Γ(X, U.ι ''ᵁ V) from r) • (show Γ(G, U.ι ''ᵁ V) from s) := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι G V r s
  rwa [Scheme.Opens.ι_appIso] at h

/-- Restricting a section along an equality of opens and back along its symmetry is the
identity. -/
private lemma presheaf_map_eqToHom_symm_apply {C D : Type*} [Category C] [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] (P : Cᵒᵖ ⥤ D) {V W : C} (h : V = W) (x : ToType (P.obj (op W))) :
    P.map (eqToHom h.symm).op (P.map (eqToHom h).op x) = x := by
  simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
    eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
    CategoryTheory.id_apply]

/-- A `Γ(X, U)`-linear map on the sections over `U`, read as a `Γ(U, ⊤)`-linear map on the global
sections of the restrictions to the open subscheme `U`, by conjugating with the restriction
isomorphisms along `U.ι ''ᵁ ⊤ = U`. -/
private noncomputable def restrictTopHom {X : Scheme.{u}} {G M : X.Modules} (U : X.Opens)
    (φ : Γ(G, U) →ₗ[Γ(X, U)] Γ(M, U)) :
    Γ(G.restrict U.ι, ⊤) →ₗ[Γ((U : Scheme), ⊤)] Γ(M.restrict U.ι, ⊤) where
  toFun y := M.presheaf.map (eqToHom U.ι_image_top).op
    (φ (G.presheaf.map (eqToHom U.ι_image_top.symm).op y))
  map_add' y z := by
    have h : (ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op))
        (show Γ(G, U.ι ''ᵁ (⊤ : (U : Scheme).Opens)) from y + z) =
      (ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op))
          (show Γ(G, U.ι ''ᵁ (⊤ : (U : Scheme).Opens)) from y) +
        (ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op))
          (show Γ(G, U.ι ''ᵁ (⊤ : (U : Scheme).Opens)) from z) := map_add _ _ _
    rw [h, map_add, map_add]
    rfl
  map_smul' r y := by
    rw [restrict_ι_smul G U ⊤ r y,
      Scheme.Modules.map_smul G (eqToHom U.ι_image_top.symm), map_smul,
      Scheme.Modules.map_smul M (eqToHom U.ι_image_top),
      presheaf_map_eqToHom_symm_apply X.presheaf U.ι_image_top.symm]
    exact (restrict_ι_smul M U ⊤ r _).symm

/-! ### Evaluation of the internal hom over an affine open -/

/-- **Evaluation of the internal hom at the terminal object of the slice site is injective over
an affine open**, for a quasi-coherent source and an arbitrary target: a morphism
`G|_U ⟶ M|_U` on the slice site over an affine `U` is determined by its component at
`Over.mk (𝟙 U)`. -/
public theorem internalHomEvaluation_injective {X : Scheme.{u}} (G M : X.Modules)
    [G.IsQuasicoherent] (U : X.affineOpens) :
    Function.Injective (internalHomEvaluation G M U.1) := by
  have : IsAffine (U.1 : Scheme) := U.2
  have : (G.restrict U.1.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι G
  intro f₁ f₂ hf
  apply (internalHomRestrictEquiv G M U.1).injective
  apply (sectionsTop_bijective (G.restrict U.1.ι) (M.restrict U.1.ι)).1
  apply LinearMap.ext
  intro y
  change (internalHomRestrictEquiv G M U.1 f₁).val.app (op ⊤) y =
    (internalHomRestrictEquiv G M U.1 f₂).val.app (op ⊤) y
  rw [internalHomRestrictEquiv_app_top, internalHomRestrictEquiv_app_top]
  refine (ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (eqToHom U.1.ι_image_top.symm).op)).injective ?_
  exact (internalHom_app_ι_image_top G M U.1 f₁ y).trans
    ((LinearMap.congr_fun hf _).trans (internalHom_app_ι_image_top G M U.1 f₂ y).symm)

/-- **Evaluation of the internal hom at the terminal object of the slice site is bijective over
an affine open**, for quasi-coherent `G` and arbitrary `M`: it identifies the sections of
`SheafHom(G, M)` over an affine open `U` with the `Γ(X, U)`-linear maps `Γ(G, U) → Γ(M, U)`. -/
public theorem internalHomEvaluation_bijective {X : Scheme.{u}} (G M : X.Modules)
    [G.IsQuasicoherent] (U : X.affineOpens) :
    Function.Bijective (internalHomEvaluation G M U.1) := by
  have : IsAffine (U.1 : Scheme) := U.2
  have : (G.restrict U.1.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι G
  refine ⟨internalHomEvaluation_injective G M U, fun φ => ?_⟩
  obtain ⟨h, hh⟩ := (sectionsTop_bijective (G.restrict U.1.ι) (M.restrict U.1.ι)).2
    (restrictTopHom U.1 φ)
  refine ⟨(internalHomRestrictEquiv G M U.1).symm h, ?_⟩
  apply LinearMap.ext
  intro x
  have hcomp : internalHomRestrictEquiv G M U.1 ((internalHomRestrictEquiv G M U.1).symm h) = h :=
    Equiv.apply_symm_apply _ _
  have hx := presheaf_map_eqToHom_symm_apply G.presheaf U.1.ι_image_top x
  have hO := (internalHomRestrictEquiv_app_top G M U.1
      ((internalHomRestrictEquiv G M U.1).symm h)
      (G.presheaf.map (eqToHom U.1.ι_image_top).op x)).symm.trans
    ((congrArg (fun k : G.restrict U.1.ι ⟶ M.restrict U.1.ι =>
        (ConcreteCategory.hom (k.val.app (op ⊤)))
          (G.presheaf.map (eqToHom U.1.ι_image_top).op x)) hcomp).trans
      (LinearMap.congr_fun hh _))
  have hev := internalHom_app_ι_image_top G M U.1 ((internalHomRestrictEquiv G M U.1).symm h)
    (G.presheaf.map (eqToHom U.1.ι_image_top).op x)
  have hs1 : ((internalHomRestrictEquiv G M U.1).symm h).app (op (Over.mk (𝟙 U.1))) x =
      ((internalHomRestrictEquiv G M U.1).symm h).app (op (Over.mk (𝟙 U.1)))
        (G.presheaf.map (eqToHom U.1.ι_image_top.symm).op
          (G.presheaf.map (eqToHom U.1.ι_image_top).op x)) := by rw [hx]
  have hs3 := congrArg (fun z => (ConcreteCategory.hom
    (M.presheaf.map (eqToHom U.1.ι_image_top.symm).op)) z) hO
  have hs4 : M.presheaf.map (eqToHom U.1.ι_image_top.symm).op
      (restrictTopHom U.1 φ (G.presheaf.map (eqToHom U.1.ι_image_top).op x)) = φ x := by
    change M.presheaf.map (eqToHom U.1.ι_image_top.symm).op
      (M.presheaf.map (eqToHom U.1.ι_image_top).op
        (φ (G.presheaf.map (eqToHom U.1.ι_image_top.symm).op
          (G.presheaf.map (eqToHom U.1.ι_image_top).op x)))) = φ x
    rw [hx]
    exact presheaf_map_eqToHom_symm_apply M.presheaf U.1.ι_image_top (φ x)
  exact hs1.trans (hev.symm.trans (hs3.trans hs4))

end Stacks.Algebraization

end
