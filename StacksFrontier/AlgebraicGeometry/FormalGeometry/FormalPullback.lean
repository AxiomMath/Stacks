module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleDescent
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules

/-!
# The formal pullback of an algebraization

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` and `G` a
coherent `𝒪_X`-module. The completion functor of Stacks 0880 sends `G` to the inverse system
`n ↦ G / ℐ ⁿ⁺¹ G` of coherent modules, and `Stacks.Algebraization.completionToLimit` is the
canonical map from `G` to the limit of that system. Given a coherent `ℐ`-adic system `(F_n)`
together with a map `α : (F_n) ⟶ (G / ℐ ⁿ⁺¹ G)` of inverse systems, the *formal pullback* is the
fibre product

`P = G ×_{lim G / ℐ ⁿ⁺¹ G} lim F_n`

formed in the abelian category of `𝒪_X`-modules.

A coherent module `F` with a map `a : F ⟶ G` and an identification `β` of `(F_n)` with the
completion of `F` compatible with `α` maps canonically to `P`. That map is an isomorphism as soon
as, over every affine open `U`, the kernel and the cokernel of `a` on sections are `ℐ(U)`-power
torsion. Consequently any two such algebraizations of `(F_n)` over `G` are related by a unique
isomorphism compatible with the maps to `G` and with the identifications of the formal system,
which is the uniqueness clause of Stacks 0889.

The formal pullback commutes with restriction to an open subscheme, and it is coherent as soon
as such an algebraization exists over every affine open.

## Main definitions

* `Stacks.Algebraization.formalPullbackModule` — the formal pullback, together with its two
  projections `Stacks.Algebraization.formalPullbackFst` and
  `Stacks.Algebraization.formalPullbackSnd`.
* `Stacks.Algebraization.formalPullbackFromAlgebraization` — the canonical map from an
  algebraization of `(F_n)` to the formal pullback.
* `Stacks.Algebraization.restrictedSystemMap` — the datum `α` transported to an open subscheme.
* `Stacks.Algebraization.formalPullbackRestrictionIso` — the formal pullback commutes with
  restriction to an open subscheme.
* `Stacks.Algebraization.affineSectionMap` — a morphism of `𝒪_X`-modules read on the sections over
  an affine open, as a map of `Γ(X, U)`-modules.

## Main results

* `Stacks.Algebraization.formalPullbackFromAlgebraization_isIso` — an algebraization whose
  comparison map has power-torsion kernel and cokernel on affine sections *is* the formal
  pullback.
* `Stacks.Algebraization.formalPullback_unique_iso_of_isIso` — the uniqueness clause of Stacks
  0889: two such algebraizations are related by a unique isomorphism compatible with the maps to
  `G` and with the identifications of the formal system.
* `Stacks.Algebraization.formalPullbackModule_isCoherent` — the formal pullback is coherent,
  checked affine-locally.
* `Stacks.Algebraization.module_completion_pullback` — the affine input: a map of finite modules
  over a Noetherian ring with power-torsion kernel and cokernel is the pullback of its completion.
* `Stacks.Algebraization.completionSectionsEquiv_map` — the identification of the affine sections
  of `lim G / ℐ ⁿ⁺¹ G` with an adic completion is natural in the coherent module.
* `Stacks.Algebraization.completionProjection_comp_completionRestrictOpenIso` — the comparison
  isomorphism of Stacks 0880 for restriction to an open is compatible with the canonical
  projections out of `G`.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

/-! ### Limits of morphisms of inverse systems -/

/-- The limit of a composite of morphisms of diagrams is the composite of the limits. -/
public theorem limMap_comp {J : Type*} [Category J] {C : Type*} [Category C]
    {F G H : J ⥤ C} [HasLimit F] [HasLimit G] [HasLimit H] (α : F ⟶ G) (β : G ⟶ H) :
    limMap (α ≫ β) = limMap α ≫ limMap β := by
  refine limit.hom_ext fun j => ?_
  simp

/-- The limit of the identity morphism of a diagram is the identity of its limit. -/
public theorem limMap_id {J : Type*} [Category J] {C : Type*} [Category C]
    {F : J ⥤ C} [HasLimit F] : limMap (𝟙 F) = 𝟙 (limit F) := by
  refine limit.hom_ext fun j => ?_
  simp

/-- An isomorphism of diagrams induces an isomorphism of their limits. -/
public noncomputable def limMapIso {J : Type*} [Category J] {C : Type*} [Category C]
    {F G : J ⥤ C} [HasLimit F] [HasLimit G] (e : F ≅ G) : limit F ≅ limit G where
  hom := limMap e.hom
  inv := limMap e.inv
  hom_inv_id := (limMap_comp e.hom e.inv).symm.trans
    ((congrArg (fun z : F ⟶ F => limMap z) e.hom_inv_id).trans limMap_id)
  inv_hom_id := (limMap_comp e.inv e.hom).symm.trans
    ((congrArg (fun z : G ⟶ G => limMap z) e.inv_hom_id).trans limMap_id)

/-! ### The canonical map to the limit of a completion -/

/-- The canonical map from a coherent module to the limit of the terms of its completion is
natural: a map `a : F ⟶ G` of coherent modules commutes with it and with the limit of the
completion of `a`. -/
public theorem completionToLimit_naturality (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G) :
    a.hom ≫ completionToLimit X I G =
      completionToLimit X I F ≫ limMap (C := X.Modules) ((completionFunctor X I).map a).hom := by
  refine limit.hom_ext (F := ((completionFunctor X I).obj G).obj) fun n => ?_
  calc
    (a.hom ≫ completionToLimit X I G) ≫
          limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n
        = a.hom ≫ completionProjection X I G n.unop :=
          (Category.assoc _ _ _).trans
            (congrArg (fun z => a.hom ≫ z) (completionToLimit_projection X I G n))
    _ = completionProjection X I F n.unop ≫ ((completionFunctor X I).map a).hom.app n :=
          (completionFunctor_map_quotient X I a n.unop).symm
    _ = (completionToLimit X I F ≫ limMap (C := X.Modules) ((completionFunctor X I).map a).hom) ≫
          limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n :=
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => completionToLimit X I F ≫ z)
                (limMap_π ((completionFunctor X I).map a).hom n)).trans
              ((Category.assoc _ _ _).symm.trans
                (congrArg (fun z => z ≫ ((completionFunctor X I).map a).hom.app n)
                  (completionToLimit_projection X I F n))))).symm


/-! ### The formal pullback -/

/-- **The formal pullback.** For a coherent module `G`, a coherent `ℐ`-adic system `(F_n)` and a
map `α : (F_n) ⟶ (G / ℐ ⁿ⁺¹ G)` of inverse systems, the fibre product

`G ×_{lim G / ℐ ⁿ⁺¹ G} lim F_n`

taken in the abelian category of `𝒪_X`-modules along the canonical map from `G` to the limit of
its completion and along the limit of `α`. -/
public noncomputable def formalPullbackModule (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) : X.Modules :=
  pullback (C := X.Modules) (completionToLimit X I G) (limMap (C := X.Modules) α)

/-- The projection of the formal pullback to `G`. This is the map that realises `α` after
completion. -/
public noncomputable def formalPullbackFst (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    formalPullbackModule X I G Fsys α ⟶ G.obj :=
  pullback.fst (completionToLimit X I G) (limMap (C := X.Modules) α)

/-- The projection of the formal pullback to the limit of the formal system `(F_n)`. -/
public noncomputable def formalPullbackSnd (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    formalPullbackModule X I G Fsys α ⟶ limit (C := X.Modules) Fsys.obj :=
  pullback.snd (completionToLimit X I G) (limMap (C := X.Modules) α)

/-- The defining cartesian square of the formal pullback: completing the projection to `G` agrees
with reading the projection to `lim F_n` through the limit of `α`. -/
public theorem formalPullback_condition (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    formalPullbackFst X I G Fsys α ≫ completionToLimit X I G =
      formalPullbackSnd X I G Fsys α ≫ limMap (C := X.Modules) α :=
  pullback.condition (C := X.Modules) (f := completionToLimit X I G)
    (g := limMap (C := X.Modules) α)


/-! ### Comparison with an algebraization -/

/-- An algebraization of `(F_n)` over `G` makes the square defining the formal pullback commute.

If `a : F ⟶ G` is a map of coherent modules and `β` identifies `(F_n)` with the completion of `F`
in such a way that `α` is the completion of `a` read through `β`, then completing `a` agrees with
the map from `F` to `lim F_n` obtained from the canonical map to the limit of the completion of
`F` and from `β⁻¹`. -/
public theorem formalPullback_square_of_algebraization (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom) :
    a.hom ≫ completionToLimit X I G =
      (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv) ≫
        limMap (C := X.Modules) α := by
  have hinv : β.inv ≫ α = ((completionFunctor X I).map a).hom :=
    (congrArg (fun z => β.inv ≫ z) hα).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ ((completionFunctor X I).map a).hom) β.inv_hom_id).trans
          (Category.id_comp _)))
  calc a.hom ≫ completionToLimit X I G
      = completionToLimit X I F ≫
          limMap (C := X.Modules) ((completionFunctor X I).map a).hom :=
        completionToLimit_naturality X I a
    _ = completionToLimit X I F ≫ limMap (C := X.Modules) (β.inv ≫ α) :=
        congrArg (fun z => completionToLimit X I F ≫ limMap (C := X.Modules) z) hinv.symm
    _ = completionToLimit X I F ≫
          (limMap (C := X.Modules) β.inv ≫ limMap (C := X.Modules) α) :=
        congrArg (fun z => completionToLimit X I F ≫ z) (limMap_comp β.inv α)
    _ = (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv) ≫
          limMap (C := X.Modules) α := (Category.assoc _ _ _).symm

/-- **The canonical map from an algebraization to the formal pullback.** An algebraization
`(F, a, β)` of `(F_n)` over `G` maps to the formal pullback by the universal property of the
fibre product, through `a` on the first factor and through the canonical map to the limit of the
completion of `F` composed with `β⁻¹` on the second. -/
public noncomputable def formalPullbackFromAlgebraization (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom) :
    F.obj ⟶ formalPullbackModule X I G Fsys α :=
  pullback.lift (f := completionToLimit X I G) (g := limMap (C := X.Modules) α) a.hom
    (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv)
    (formalPullback_square_of_algebraization X I G Fsys α F a β hα)

/-- The canonical map from an algebraization composed with the projection to `G` is the
comparison map `a`. -/
public theorem formalPullbackFromAlgebraization_fst (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom) :
    formalPullbackFromAlgebraization X I G Fsys α F a β hα ≫ formalPullbackFst X I G Fsys α =
      a.hom :=
  pullback.lift_fst (f := completionToLimit X I G) (g := limMap (C := X.Modules) α) a.hom
    (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv)
    (formalPullback_square_of_algebraization X I G Fsys α F a β hα)

/-- The canonical map from an algebraization composed with the projection to `lim F_n` is the
canonical map to the limit of the completion of `F` read through `β⁻¹`. -/
public theorem formalPullbackFromAlgebraization_snd (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom) :
    formalPullbackFromAlgebraization X I G Fsys α F a β hα ≫ formalPullbackSnd X I G Fsys α =
      completionToLimit X I F ≫ limMap (C := X.Modules) β.inv :=
  pullback.lift_snd (f := completionToLimit X I G) (g := limMap (C := X.Modules) α) a.hom
    (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv)
    (formalPullback_square_of_algebraization X I G Fsys α F a β hα)


/-- If two algebraizations `(F, a, β)` and `(F', a', β')` of the same datum both have invertible
canonical map to the formal pullback, then there is a unique isomorphism `F ≅ F'` compatible with
the maps to `G` and with the two identifications of the formal system. -/
public theorem formalPullback_unique_iso_of_isIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (a : F ⟶ G) (a' : F' ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (β' : Fsys.obj ≅ ((completionFunctor X I).obj F').obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom)
    (hα' : α = β'.hom ≫ ((completionFunctor X I).map a').hom)
    (hp : IsIso (formalPullbackFromAlgebraization X I G Fsys α F a β hα))
    (hq : IsIso (formalPullbackFromAlgebraization X I G Fsys α F' a' β' hα')) :
    ∃! e : F.obj ≅ F'.obj,
      e.hom ≫ a'.hom = a.hom ∧
        e.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
          completionToLimit X I F ≫ limMap (C := X.Modules) β.inv := by
  set p := formalPullbackFromAlgebraization X I G Fsys α F a β hα with hpdef
  set q := formalPullbackFromAlgebraization X I G Fsys α F' a' β' hα' with hqdef
  let e : F.obj ≅ F'.obj := asIso p ≪≫ (asIso q).symm
  have he : e.hom ≫ q = p :=
    (Category.assoc p (inv q) q).trans
      ((congrArg (fun z => p ≫ z) (IsIso.inv_hom_id q)).trans (Category.comp_id p))
  have hefst : e.hom ≫ a'.hom = a.hom :=
    (congrArg (fun z => e.hom ≫ z)
        (formalPullbackFromAlgebraization_fst X I G Fsys α F' a' β' hα').symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ formalPullbackFst X I G Fsys α) he).trans
          (formalPullbackFromAlgebraization_fst X I G Fsys α F a β hα)))
  have hesnd : e.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
      completionToLimit X I F ≫ limMap (C := X.Modules) β.inv :=
    (congrArg (fun z => e.hom ≫ z)
        (formalPullbackFromAlgebraization_snd X I G Fsys α F' a' β' hα').symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ formalPullbackSnd X I G Fsys α) he).trans
          (formalPullbackFromAlgebraization_snd X I G Fsys α F a β hα)))
  refine ⟨e, ⟨hefst, hesnd⟩, fun d hd => ?_⟩
  have hdq : d.hom ≫ q = p := by
    refine pullback.hom_ext (f := completionToLimit X I G) (g := limMap (C := X.Modules) α) ?_ ?_
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => d.hom ≫ z)
            (formalPullbackFromAlgebraization_fst X I G Fsys α F' a' β' hα')).trans
          (hd.1.trans (formalPullbackFromAlgebraization_fst X I G Fsys α F a β hα).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => d.hom ≫ z)
            (formalPullbackFromAlgebraization_snd X I G Fsys α F' a' β' hα')).trans
          (hd.2.trans (formalPullbackFromAlgebraization_snd X I G Fsys α F a β hα).symm))
  exact Iso.ext (((@asIso _ _ _ _ q hq).cancel_iso_hom_right _ _).1 (hdq.trans he.symm))


/-! ### Restriction to an open subscheme -/

/-- Restriction along an open immersion preserves limits indexed by `ℕᵒᵖ`. -/
public theorem preservesLimitsOfShape_natOp_restrictFunctor {Y Z : Scheme.{u}} (r : Z ⟶ Y)
    [IsOpenImmersion r] : PreservesLimitsOfShape ℕᵒᵖ (Scheme.Modules.restrictFunctor r) := by
  have h₀ : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Y) :=
    preservesLimitsOfSize_shrink _
  have h₁ : PreservesLimitsOfShape ℕᵒᵖ
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj r.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor r ⋙ Scheme.Modules.toPresheaf Z ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj r.opensFunctor.op := Iso.refl _
  have h₂ : PreservesLimitsOfShape ℕᵒᵖ
      (Scheme.Modules.restrictFunctor r ⋙ Scheme.Modules.toPresheaf Z) :=
    preservesLimitsOfShape_of_natIso e.symm
  have h₃ : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Z) :=
    preservesLimitsOfSize_shrink _
  have h₄ : ReflectsLimitsOfShape ℕᵒᵖ (Scheme.Modules.toPresheaf Z) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Z)

attribute [local instance] preservesLimitsOfShape_natOp_restrictFunctor

/-- **The comparison isomorphism of Stacks 0880 for restriction to an open is compatible with the
canonical projections.** Restricting the projection of `M` onto the `n`-th term of its completion
and then comparing gives the projection of `M|_Y` onto the `n`-th term of its own completion. -/
public theorem completionProjection_comp_completionRestrictOpenIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (Scheme.Modules.restrictFunctor f).map (completionProjection X I M n) ≫
        (completionRestrictOpenIso f I M).hom.app (op n) =
      completionProjection Y (I.comap f) (restrictCoherentModules f M) n := by
  have hMq : M.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj).1
  set R := Scheme.Modules.restrictFunctor f with hRdef
  set ι := (idealPowerMultiple I (n + 1) M.obj).ι with hιdef
  set ρ := restrictIdealPowerQuotientIso f I (n + 1) M.obj with hρdef
  set eX := eqToHom (completionFunctor_obj X I M n) with heXdef
  set eY := eqToHom
    (completionFunctor_obj Y (I.comap f) (restrictCoherentModules f M) n).symm with heYdef
  have happ : (completionRestrictOpenIso f I M).hom.app (op n) =
      R.map eX ≫ (ρ.inv ≫ eY) := rfl
  have hinner : completionProjection X I M n ≫ eX = cokernel.π ι :=
    (Category.assoc (cokernel.π ι) (eqToHom (completionFunctor_obj X I M n).symm) eX).trans
      ((congrArg (fun k => cokernel.π ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
  have t1 : R.map (completionProjection X I M n) ≫ R.map eX = R.map (cokernel.π ι) :=
    (R.map_comp _ _).symm.trans (congrArg R.map hinner)
  have key : R.map (cokernel.π ι) ≫ ρ.inv =
      cokernel.π (idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι :=
    (congrArg (fun z => z ≫ ρ.inv)
        (cokernel_π_comp_restrictIdealPowerQuotientIso f I (n + 1) M.obj).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
            (fun z => cokernel.π (idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι ≫ z)
            ρ.hom_inv_id).trans (Category.comp_id _)))
  rw [happ, ← Category.assoc, t1]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ eY) key)


/-- Restriction along an open immersion commutes with the limit of an `ℕᵒᵖ`-indexed inverse
system of `𝒪_X`-modules. -/
public noncomputable def restrictLimitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (S : ℕᵒᵖ ⥤ X.Modules) :
    (Scheme.Modules.restrictFunctor f).obj (limit (C := X.Modules) S) ≅
      limit (C := Y.Modules) (S ⋙ Scheme.Modules.restrictFunctor f) :=
  have _hpl : PreservesLimit S (Scheme.Modules.restrictFunctor f) :=
    (preservesLimitsOfShape_natOp_restrictFunctor f).preservesLimit
  preservesLimitIso (Scheme.Modules.restrictFunctor f) S

/-- Restriction along an open immersion commutes with the limit of a coherent adic system; the
same isomorphism as `Stacks.Algebraization.restrictLimitIso`, with the restricted system named
through `Stacks.Coherent.restrictFunctor`. -/
public noncomputable def restrictSystemLimitIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) :
    (Scheme.Modules.restrictFunctor f).obj (limit (C := X.Modules) Fsys.obj) ≅
      limit (C := Y.Modules) ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj :=
  restrictLimitIso f Fsys.obj

/-- Restricting the limit of the completion of `G` gives the limit of the completion of `G|_Y`. -/
public noncomputable def restrictCompletionLimitIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj G).obj) ≅
      limit (C := Y.Modules)
        ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj :=
  restrictLimitIso f ((completionFunctor X I).obj G).obj ≪≫
    limMapIso (completionRestrictOpenIso f I G)

/-- The identification of the restricted limit with the limit of the restricted completion
carries the restriction of the canonical map of `G` to the canonical map of `G|_Y`. -/
public theorem restrictCompletionLimitIso_completionToLimit {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f).map (completionToLimit X I G) ≫
        (restrictCompletionLimitIso f I G).hom =
      completionToLimit Y (I.comap f) (restrictCoherentModules f G) := by
  refine limit.hom_ext
    (F := ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj)
    fun n => ?_
  set R := Scheme.Modules.restrictFunctor f with hRdef
  set e := completionRestrictOpenIso f I G with hedef
  set A := R.map (completionToLimit X I G) with hAdef
  set B := (restrictLimitIso f ((completionFunctor X I).obj G).obj).hom with hBdef
  set C := limMap e.hom with hCdef
  set D := limit.π ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj n
    with hDdef
  set P := limit.π (((completionFunctor X I).obj G).obj ⋙ R) n with hPdef
  set E := e.hom.app n with hEdef
  set Q := R.map (limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) with hQdef
  have h0 : (restrictCompletionLimitIso f I G).hom = B ≫ C := rfl
  have h1 : C ≫ D = P ≫ E := limMap_π e.hom n
  have h2 : B ≫ P = Q := preservesLimitIso_hom_π _ _ _
  have h3 : A ≫ Q = R.map (completionProjection X I G n.unop) :=
    (R.map_comp _ _).symm.trans (congrArg R.map (completionToLimit_projection X I G n))
  have h4 : R.map (completionProjection X I G n.unop) ≫ E =
      completionProjection Y (I.comap f) (restrictCoherentModules f G) n.unop :=
    completionProjection_comp_completionRestrictOpenIso f I G n.unop
  have h5 : completionToLimit Y (I.comap f) (restrictCoherentModules f G) ≫ D =
      completionProjection Y (I.comap f) (restrictCoherentModules f G) n.unop :=
    completionToLimit_projection Y (I.comap f) (restrictCoherentModules f G) n
  rw [h0, Category.assoc, Category.assoc, h1, ← Category.assoc B, h2, ← Category.assoc, h3, h4]
  exact h5.symm

/-- The datum `α` transported to an open subscheme: restrict it term by term, then compare the
restricted completion of `G` with the completion of `G|_Y`. -/
public noncomputable def restrictedSystemMap {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj ⟶
      ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj :=
  Functor.whiskerRight α (Scheme.Modules.restrictFunctor f) ≫
    (completionRestrictOpenIso f I G).hom

/-- The identification of the restricted limit with the limit of the restricted completion
carries the restriction of the limit of `α` to the limit of the restricted datum. -/
public theorem restrictCompletionLimitIso_limMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    (Scheme.Modules.restrictFunctor f).map (limMap (C := X.Modules) α) ≫
        (restrictCompletionLimitIso f I G).hom =
      (restrictSystemLimitIso f I Fsys).hom ≫
        limMap (C := Y.Modules) (restrictedSystemMap f I G Fsys α) := by
  refine limit.hom_ext
    (F := ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj)
    fun n => ?_
  set R := Scheme.Modules.restrictFunctor f with hRdef
  set e := completionRestrictOpenIso f I G with hedef
  set A := R.map (limMap (C := X.Modules) α) with hAdef
  set B := (restrictLimitIso f ((completionFunctor X I).obj G).obj).hom with hBdef
  set C := limMap e.hom with hCdef
  set D := limit.π ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj n
    with hDdef
  set P := limit.π (((completionFunctor X I).obj G).obj ⋙ R) n with hPdef
  set E := e.hom.app n with hEdef
  set Q := R.map (limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) with hQdef
  set BF := (restrictSystemLimitIso f I Fsys).hom with hBFdef
  set CS := limMap (C := Y.Modules) (restrictedSystemMap f I G Fsys α) with hCSdef
  set PF := limit.π (Fsys.obj ⋙ R) n with hPFdef
  set W := R.map (limit.π (C := X.Modules) Fsys.obj n) with hWdef
  set V := R.map (α.app n) with hVdef
  have h0 : (restrictCompletionLimitIso f I G).hom = B ≫ C := rfl
  have h1 : C ≫ D = P ≫ E := limMap_π e.hom n
  have h2 : B ≫ P = Q := preservesLimitIso_hom_π _ _ _
  have h3 : A ≫ Q = W ≫ V :=
    (R.map_comp _ _).symm.trans ((congrArg R.map (limMap_π α n)).trans (R.map_comp _ _))
  have h4 : CS ≫ D = PF ≫ (restrictedSystemMap f I G Fsys α).app n :=
    limMap_π (restrictedSystemMap f I G Fsys α) n
  have h5 : BF ≫ PF = W := preservesLimitIso_hom_π _ _ _
  have h6 : (restrictedSystemMap f I G Fsys α).app n = V ≫ E := rfl
  rw [h0, Category.assoc, Category.assoc, h1, ← Category.assoc B, h2, ← Category.assoc, h3,
    Category.assoc, Category.assoc, h4, h6]
  exact ((Category.assoc BF PF (V ≫ E)).symm.trans (congrArg (fun z => z ≫ (V ≫ E)) h5)).symm


attribute [local implicit_reducible] restrictCoherentModules

/-- **The formal pullback commutes with restriction to an open subscheme.** Restricting the
formal pullback of `(G, (F_n), α)` along an open immersion gives the formal pullback of the
restricted data. -/
public noncomputable def formalPullbackRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    (Scheme.Modules.restrictFunctor f).obj (formalPullbackModule X I G Fsys α) ≅
      formalPullbackModule Y (I.comap f) (restrictCoherentModules f G)
        ((Stacks.Coherent.restrictFunctor I f).obj Fsys) (restrictedSystemMap f I G Fsys α) :=
  have _hfl : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor f
  let m := pullback.map ((Scheme.Modules.restrictFunctor f).map (completionToLimit X I G))
    ((Scheme.Modules.restrictFunctor f).map (limMap (C := X.Modules) α))
    (completionToLimit Y (I.comap f) (restrictCoherentModules f G))
    (limMap (C := Y.Modules) (restrictedSystemMap f I G Fsys α))
    (𝟙 _) (restrictSystemLimitIso f I Fsys).hom (restrictCompletionLimitIso f I G).hom
    ((restrictCompletionLimitIso_completionToLimit f I G).trans (Category.id_comp _).symm)
    (restrictCompletionLimitIso_limMap f I G Fsys α)
  have hiso : IsIso m := pullback.map_isIso
    ((Scheme.Modules.restrictFunctor f).map (completionToLimit X I G))
    ((Scheme.Modules.restrictFunctor f).map (limMap (C := X.Modules) α))
    (completionToLimit Y (I.comap f) (restrictCoherentModules f G))
    (limMap (C := Y.Modules) (restrictedSystemMap f I G Fsys α))
    (𝟙 _) (restrictSystemLimitIso f I Fsys).hom (restrictCompletionLimitIso f I G).hom
    ((restrictCompletionLimitIso_completionToLimit f I G).trans (Category.id_comp _).symm)
    (restrictCompletionLimitIso_limMap f I G Fsys α)
  PreservesPullback.iso (Scheme.Modules.restrictFunctor f) (completionToLimit X I G)
      (limMap (C := X.Modules) α) ≪≫ @asIso _ _ _ _ m hiso

/-- The restriction isomorphism is compatible with the projections to `G`. -/
public theorem formalPullbackRestrictionIso_hom_fst {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    (formalPullbackRestrictionIso f I G Fsys α).hom ≫
        formalPullbackFst Y (I.comap f) (restrictCoherentModules f G)
          ((Stacks.Coherent.restrictFunctor I f).obj Fsys) (restrictedSystemMap f I G Fsys α) =
      (Scheme.Modules.restrictFunctor f).map (formalPullbackFst X I G Fsys α) := by
  unfold formalPullbackRestrictionIso formalPullbackFst
  erw [Category.assoc, pullback.lift_fst]
  exact PreservesPullback.iso_hom_fst _ _ _

/-- The restriction isomorphism is compatible with the projections to the limit of the formal
system, through the identification of the restricted limit with the limit of the restricted
system. -/
public theorem formalPullbackRestrictionIso_hom_snd {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj) :
    (formalPullbackRestrictionIso f I G Fsys α).hom ≫
        formalPullbackSnd Y (I.comap f) (restrictCoherentModules f G)
          ((Stacks.Coherent.restrictFunctor I f).obj Fsys) (restrictedSystemMap f I G Fsys α) =
      (Scheme.Modules.restrictFunctor f).map (formalPullbackSnd X I G Fsys α) ≫
        (restrictSystemLimitIso f I Fsys).hom := by
  unfold formalPullbackRestrictionIso formalPullbackSnd
  erw [Category.assoc, pullback.lift_snd, ← Category.assoc]
  exact congrArg (· ≫ _) (PreservesPullback.iso_hom_snd _ _ _)


/-! ### An affine-local criterion for the comparison to be invertible -/

/-- A morphism of `𝒪_X`-modules which is bijective on the sections over every affine open is an
isomorphism. -/
public theorem isIso_of_affine_sections_bijective {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ U : X.affineOpens, Function.Bijective (a.val.app (op U.1)).hom) : IsIso a := by
  let M' : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  let N' : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  let a' : M' ⟶ N' := ⟨a.mapPresheaf⟩
  have ha' : IsIso a' := TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    (fun U => (ConcreteCategory.isIso_iff_bijective _).2 (ha U))
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) :=
    (TopCat.Sheaf.forget AddCommGrpCat X).map_isIso a'
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

/-- The map into a fibre product induced by a commuting square is an isomorphism as soon as, over
every affine open, every pair of sections agreeing in the common target comes from a unique
section of the source. -/
public theorem isIso_pullback_lift_of_affine_sections {X : Scheme.{u}}
    {M N P Q : X.Modules} (a : M ⟶ N) (b : M ⟶ P) (r : N ⟶ Q) (s : P ⟶ Q)
    (hab : a ≫ r = b ≫ s)
    (h : ∀ (U : X.affineOpens) (g : Γ(N, U)) (y : Γ(P, U)),
      r.val.app (op U.1) g = s.val.app (op U.1) y →
      ∃! x : Γ(M, U), a.val.app (op U.1) x = g ∧ b.val.app (op U.1) x = y) :
    IsIso (pullback.lift (C := X.Modules) (f := r) (g := s) a b hab) := by
  refine isIso_of_affine_sections_bijective _ fun U => ?_
  have hE : PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U.1)
  have hEc : PreservesLimitsOfShape WalkingCospan
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)) := hE.preservesFiniteLimits _
  have hEl : PreservesLimit (cospan r s)
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)) := hEc.preservesLimit
  set p := pullback.lift (C := X.Modules) (f := r) (g := s) a b hab with hpdef
  have hp₁ : ∀ x : Γ(M, U), (pullback.fst r s).val.app (op U.1) (p.val.app (op U.1) x) =
      a.val.app (op U.1) x :=
    fun x => congrArg (fun z => (z.val.app (op U.1)).hom x) (pullback.lift_fst a b hab)
  have hp₂ : ∀ x : Γ(M, U), (pullback.snd r s).val.app (op U.1) (p.val.app (op U.1) x) =
      b.val.app (op U.1) x :=
    fun x => congrArg (fun z => (z.val.app (op U.1)).hom x) (pullback.lift_snd a b hab)
  constructor
  · intro x y hxy
    have hax : a.val.app (op U.1) x = a.val.app (op U.1) y :=
      (hp₁ x).symm.trans ((congrArg ((pullback.fst r s).val.app (op U.1)) hxy).trans (hp₁ y))
    have hbx : b.val.app (op U.1) x = b.val.app (op U.1) y :=
      (hp₂ x).symm.trans ((congrArg ((pullback.snd r s).val.app (op U.1)) hxy).trans (hp₂ y))
    obtain ⟨z, hz, huniq⟩ := h U (a.val.app (op U.1) x) (b.val.app (op U.1) x)
      (congrArg (fun k => (k.val.app (op U.1)).hom x) hab)
    exact (huniq x ⟨rfl, rfl⟩).trans (huniq y ⟨hax.symm, hbx.symm⟩).symm
  · intro z
    have hz : r.val.app (op U.1) ((pullback.fst r s).val.app (op U.1) z) =
        s.val.app (op U.1) ((pullback.snd r s).val.app (op U.1) z) :=
      congrArg (fun k => (k.val.app (op U.1)).hom z) (pullback.condition (f := r) (g := s))
    obtain ⟨x, hx, _⟩ := h U ((pullback.fst r s).val.app (op U.1) z)
      ((pullback.snd r s).val.app (op U.1) z) hz
    refine ⟨x, ?_⟩
    refine Concrete.isLimit_ext (cospan r s ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U.1))
      (@isLimitOfPreserves _ _ _ _ _ _ (cospan r s)
        (SheafOfModules.evaluation X.ringCatSheaf (op U.1)) _
        (pullbackIsPullback r s) hEl) _ _ fun j => ?_
    match j with
    | WalkingCospan.left => exact (hp₁ x).trans hx.1
    | WalkingCospan.right => exact (hp₂ x).trans hx.2
    | WalkingCospan.one =>
      exact congrArg (r.val.app (op U.1)) ((hp₁ x).trans hx.1)


/-! ### A finite module is the fibre product of its completion -/

/-- A map `ψ : M → N` of finite modules over a Noetherian ring
whose kernel and cokernel are `J`-power torsion exhibits `M` as the fibre product of `N` and the
`J`-adic completion of `M` over the `J`-adic completion of `N`: an element of `N` and an element
of `M^∧` with the same image in `N^∧` come from a unique element of `M`. -/
public theorem module_completion_pullback {R : Type u} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (ψ : M →ₗ[R] N)
    (hK : IsIPowerTorsion R (LinearMap.ker ψ) J)
    (hC : IsIPowerTorsion R (N ⧸ LinearMap.range ψ) J)
    (n : N) (x : AdicCompletion J M)
    (hx : AdicCompletion.map J ψ x = AdicCompletion.of J N n) :
    ∃! m : M, ψ m = n ∧ AdicCompletion.of J M m = x := by
  set eM := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J M with heM
  set eN := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J N with heN
  have heMtmul : ∀ (s : AdicCompletion J R) (m : M),
      eM (s ⊗ₜ[R] m) = s • AdicCompletion.of J M m := fun s m =>
    AdicCompletion.ofTensorProduct_tmul J M s m
  have heNtmul : ∀ (s : AdicCompletion J R) (y : N),
      eN (s ⊗ₜ[R] y) = s • AdicCompletion.of J N y := fun s y =>
    AdicCompletion.ofTensorProduct_tmul J N s y
  set φ := (eN.symm.toLinearMap).comp (AdicCompletion.map J ψ) with hφ
  have hcomp : φ.comp eM.toLinearMap = LinearMap.baseChange (AdicCompletion J R) ψ := by
    refine LinearMap.ext fun y => ?_
    refine eN.injective ?_
    induction y using TensorProduct.inductionOn with
    | tmul s m =>
      have h1 : φ (eM (s ⊗ₜ[R] m)) = eN.symm (AdicCompletion.map J ψ (eM (s ⊗ₜ[R] m))) := rfl
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, eN.apply_symm_apply, heMtmul,
        map_smul, AdicCompletion.map_of, LinearMap.baseChange_tmul, heNtmul]
    | add y z hy hz =>
      simp only [map_add] at hy hz ⊢
      rw [hy, hz]
  have hy : φ x = (1 : AdicCompletion J R) ⊗ₜ[R] n := by
    have h1 : φ x = eN.symm (AdicCompletion.map J ψ x) := rfl
    refine eN.injective ?_
    rw [h1, eN.apply_symm_apply, hx, heNtmul, one_smul]
  obtain ⟨m, hm, huniq⟩ :=
    AdicCompletion.existsUnique_of_descent.{u, u} J ψ φ eM hcomp hK hC n x hy
  refine ⟨m, ⟨hm.1, ?_⟩, fun m' hm' => huniq m' ⟨hm'.1, ?_⟩⟩
  · exact ((heMtmul 1 m).trans (one_smul _ _)).symm.trans hm.2
  · exact ((heMtmul 1 m').trans (one_smul _ _)).trans hm'.2


/-! ### Naturality of the identification of affine sections -/

/-- The identification of the sections over an affine open of a term of the completion with a
module quotient of `Γ(F, U)` is natural in the coherent module: a map `a : F ⟶ G` induces on the
quotients the reduction of `a` modulo the ideal power. -/
public theorem completionQuotientSectionsEquiv_map (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (n : ℕ) (U : X.affineOpens)
    (y : Γ(F.obj, U) ⧸ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U))) :
    (((completionFunctor X I).map a).hom.app (op n)).val.app (op U.1)
        (completionQuotientSectionsEquiv X I F n U y) =
      completionQuotientSectionsEquiv X I G n U
        ((a.hom.val.app (op U.1)).hom.reduceModIdeal (I.ideal U ^ (n + 1)) y) := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    have h1 : completionQuotientSectionsEquiv X I F n U (Submodule.Quotient.mk x) =
        (completionProjection X I F n).val.app (op U.1) x :=
      completionQuotientSectionsEquiv_mk X I F n U x
    have h2 : completionQuotientSectionsEquiv X I G n U
          (Submodule.Quotient.mk ((a.hom.val.app (op U.1)).hom x)) =
        (completionProjection X I G n).val.app (op U.1) ((a.hom.val.app (op U.1)).hom x) :=
      completionQuotientSectionsEquiv_mk X I G n U _
    have h3 : (completionProjection X I F n ≫
          ((completionFunctor X I).map a).hom.app (op n)).val.app (op U.1) x =
        (a.hom ≫ completionProjection X I G n).val.app (op U.1) x :=
      congrArg (fun k : F.obj ⟶ ((completionFunctor X I).obj G).obj.obj (op n) =>
        (k.val.app (op U.1)).hom x) (completionFunctor_map_quotient X I a n)
    exact (congrArg
      ((((((completionFunctor X I).map a).hom.app (op n)).val.app (op U.1))).hom) h1).trans
        (h3.trans h2.symm)

/-- The identification of the sections over an affine open of the limit of the completion with
the `ℐ(U)`-adic completion of `Γ(F, U)` is natural in the coherent module: a map `a : F ⟶ G`
induces the adic completion of `a` on sections. -/
public theorem completionSectionsEquiv_map (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (U : X.affineOpens) (x : AdicCompletion (I.ideal U) Γ(F.obj, U)) :
    (limMap (C := X.Modules) ((completionFunctor X I).map a).hom).val.app (op U.1)
        (completionSectionsEquiv X I F U x) =
      completionSectionsEquiv X I G U
        (AdicCompletion.map (I.ideal U) (a.hom.val.app (op U.1)).hom x) := by
  set w := AdicCompletion.map (I.ideal U) (a.hom.val.app (op U.1)).hom x with hwdef
  set L := (limMap (C := X.Modules) ((completionFunctor X I).map a).hom).val.app (op U.1)
    (completionSectionsEquiv X I F U x) with hLdef
  set v := (completionSectionsEquiv X I G U).symm L with hvdef
  have hv : completionSectionsEquiv X I G U v = L :=
    (completionSectionsEquiv X I G U).apply_symm_apply L
  have hkey : ∀ n : ℕ,
      (limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj (op n)).val.app (op U.1) L =
        completionQuotientSectionsEquiv X I G n U (w.val (n + 1)) := by
    intro n
    have e1 : (limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj (op n)).val.app
          (op U.1) L =
        (((completionFunctor X I).map a).hom.app (op n)).val.app (op U.1)
          ((limit.π (C := X.Modules) ((completionFunctor X I).obj F).obj (op n)).val.app (op U.1)
            (completionSectionsEquiv X I F U x)) :=
      congrArg (fun k : limit (C := X.Modules) ((completionFunctor X I).obj F).obj ⟶
          ((completionFunctor X I).obj G).obj.obj (op n) =>
        k.val.app (op U.1) (completionSectionsEquiv X I F U x))
        (limMap_π ((completionFunctor X I).map a).hom (op n))
    have e2 := completionSectionsEquiv_projection X I F U n x
    have e3 := completionQuotientSectionsEquiv_map X I a n U
      (AdicCompletion.eval (I.ideal U) Γ(F.obj, U) (n + 1) x)
    exact e1.trans ((congrArg
      ((((completionFunctor X I).map a).hom.app (op n)).val.app (op U.1)).hom e2).trans e3)
  have hvw : v = w := by
    refine AdicCompletion.ext fun k => ?_
    match k with
    | 0 =>
      have : Subsingleton (Γ(G.obj, U) ⧸
          (I.ideal U ^ 0 • (⊤ : Submodule Γ(X, U) Γ(G.obj, U)))) := by
        simp only [pow_zero, Submodule.one_smul]
        infer_instance
      exact Subsingleton.elim _ _
    | (n + 1) =>
      refine (completionQuotientSectionsEquiv X I G n U).injective ?_
      refine Eq.trans ?_ (hkey n)
      refine Eq.trans (completionSectionsEquiv_projection X I G U n v).symm ?_
      exact congrArg
        ((limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj (op n)).val.app
          (op U.1)).hom hv
  exact hv.symm.trans (congrArg (completionSectionsEquiv X I G U) hvw)


/-! ### The comparison with an algebraization is an isomorphism -/

/-- A morphism of `𝒪_X`-modules read on the sections over an affine open `U`, as a map of
`Γ(X, U)`-modules. -/
public noncomputable def affineSectionMap {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (U : X.affineOpens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (a.val.app (op U.1)).hom

/-- Over an affine open, a coherent module whose comparison map to `G` has power-torsion kernel
and cokernel on sections is the fibre product of `G` and the limit of its completion: every
section of `G` and every section of the limit of the completion of `F` that agree in the limit of
the completion of `G` come from a unique section of `F`. -/
public theorem coherent_completion_pullback_sections {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (U : X.affineOpens)
    (hK : IsIPowerTorsion Γ(X, U) (LinearMap.ker (affineSectionMap a.hom U)) (I.ideal U))
    (hC : IsIPowerTorsion Γ(X, U)
      (Γ(G.obj, U) ⧸ LinearMap.range (affineSectionMap a.hom U)) (I.ideal U))
    (g : Γ(G.obj, U)) (x : Γ(limit (C := X.Modules) ((completionFunctor X I).obj F).obj, U))
    (hx : (limMap (C := X.Modules) ((completionFunctor X I).map a).hom).val.app (op U.1) x =
      (completionToLimit X I G).val.app (op U.1) g) :
    ∃! m : Γ(F.obj, U), affineSectionMap a.hom U m = g ∧
      (completionToLimit X I F).val.app (op U.1) m = x := by
  have hFc : F.obj.IsCoherent := F.property
  have hGc : G.obj.IsCoherent := G.property
  obtain ⟨hFq, hFt⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj
  obtain ⟨hGq, hGt⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G.obj
  have hFfin : Module.Finite Γ(X, U) Γ(F.obj, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F.obj U.2
  have hGfin : Module.Finite Γ(X, U) Γ(G.obj, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections G.obj U.2
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  set z := (completionSectionsEquiv X I F U).symm x with hzdef
  have hz : completionSectionsEquiv X I F U z = x :=
    (completionSectionsEquiv X I F U).apply_symm_apply x
  have hcomp : AdicCompletion.map (I.ideal U) (affineSectionMap a.hom U) z =
      AdicCompletion.of (I.ideal U) Γ(G.obj, U) g := by
    refine (completionSectionsEquiv X I G U).injective ?_
    refine Eq.trans (completionSectionsEquiv_map X I a U z).symm ?_
    refine Eq.trans ?_ (completionSectionsEquiv_of X I G U g).symm
    exact (congrArg
      ((limMap (C := X.Modules) ((completionFunctor X I).map a).hom).val.app (op U.1)).hom
        hz).trans hx
  obtain ⟨m, hm, huniq⟩ := module_completion_pullback (I.ideal U)
    (affineSectionMap a.hom U) hK hC g z hcomp
  refine ⟨m, ⟨hm.1, ?_⟩, fun m' hm' => huniq m' ⟨hm'.1, ?_⟩⟩
  · exact ((completionSectionsEquiv_of X I F U m).symm.trans
      (congrArg (completionSectionsEquiv X I F U) hm.2)).trans hz
  · refine (completionSectionsEquiv X I F U).injective ?_
    exact (completionSectionsEquiv_of X I F U m').trans (hm'.2.trans hz.symm)


/-- **An algebraization is the formal pullback.** Let `(F, a, β)` be an algebraization of `(F_n)`
over `G`, and suppose that over every affine open the kernel and the cokernel of `a` on sections
are `ℐ(U)`-power torsion. Then the canonical map from `F` to the formal pullback is an
isomorphism. -/
public theorem formalPullbackFromAlgebraization_isIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom)
    (hK : ∀ U : X.affineOpens,
      IsIPowerTorsion Γ(X, U) (LinearMap.ker (affineSectionMap a.hom U)) (I.ideal U))
    (hC : ∀ U : X.affineOpens, IsIPowerTorsion Γ(X, U)
      (Γ(G.obj, U) ⧸ LinearMap.range (affineSectionMap a.hom U)) (I.ideal U)) :
    IsIso (formalPullbackFromAlgebraization X I G Fsys α F a β hα) := by
  refine isIso_pullback_lift_of_affine_sections a.hom
    (completionToLimit X I F ≫ limMap (C := X.Modules) β.inv)
    (completionToLimit X I G) (limMap (C := X.Modules) α)
    (formalPullback_square_of_algebraization X I G Fsys α F a β hα) ?_
  intro U g y hy
  have hmap : limMap (C := X.Modules) α = limMap (C := X.Modules) β.hom ≫
      limMap (C := X.Modules) ((completionFunctor X I).map a).hom :=
    (congrArg (fun z => limMap (C := X.Modules) z) hα).trans
      (limMap_comp β.hom ((completionFunctor X I).map a).hom)
  have hbi : ∀ t : Γ(limit (C := X.Modules) Fsys.obj, U.1),
      (limMap (C := X.Modules) β.inv).val.app (op U.1)
        ((limMap (C := X.Modules) β.hom).val.app (op U.1) t) = t := fun t =>
    congrArg (fun k : limit (C := X.Modules) Fsys.obj ⟶ limit (C := X.Modules) Fsys.obj =>
      (k.val.app (op U.1)).hom t) (limMapIso β).hom_inv_id
  have hbi' : ∀ t : Γ(limit (C := X.Modules) ((completionFunctor X I).obj F).obj, U.1),
      (limMap (C := X.Modules) β.hom).val.app (op U.1)
        ((limMap (C := X.Modules) β.inv).val.app (op U.1) t) = t := fun t =>
    congrArg (fun k : limit (C := X.Modules) ((completionFunctor X I).obj F).obj ⟶
        limit (C := X.Modules) ((completionFunctor X I).obj F).obj =>
      (k.val.app (op U.1)).hom t) (limMapIso β).inv_hom_id
  have hcompat : (limMap (C := X.Modules) ((completionFunctor X I).map a).hom).val.app (op U.1)
        ((limMap (C := X.Modules) β.hom).val.app (op U.1) y) =
      (completionToLimit X I G).val.app (op U.1) g :=
    (congrArg (fun k : limit (C := X.Modules) Fsys.obj ⟶
        limit (C := X.Modules) ((completionFunctor X I).obj G).obj =>
      (k.val.app (op U.1)).hom y) hmap).symm.trans hy.symm
  obtain ⟨m, hm, huniq⟩ := coherent_completion_pullback_sections I a U (hK U) (hC U) g
    ((limMap (C := X.Modules) β.hom).val.app (op U.1) y) hcompat
  refine ⟨m, ⟨hm.1, ?_⟩, fun m' hm' => huniq m' ⟨hm'.1, ?_⟩⟩
  · exact (congrArg ((limMap (C := X.Modules) β.inv).val.app (op U.1)).hom hm.2).trans (hbi y)
  · exact (hbi' ((completionToLimit X I F).val.app (op U.1) m')).symm.trans
      (congrArg ((limMap (C := X.Modules) β.hom).val.app (op U.1)).hom hm'.2)


/-! ### Coherence of the formal pullback -/


/-- **The formal pullback is coherent.** If over every affine open `U` the restricted datum
admits an algebraization whose comparison map has power-torsion kernel and cokernel on sections,
then the formal pullback is a coherent `𝒪_X`-module. -/
public theorem formalPullbackModule_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (h : ∀ U : X.affineOpens,
      ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
        (b : F ⟶ restrictCoherentModules U.1.ι G)
        (β : ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj ≅
          ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj F).obj),
        restrictedSystemMap U.1.ι I G Fsys α =
            β.hom ≫ ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map b).hom ∧
          (∀ V : U.1.toScheme.affineOpens, IsIPowerTorsion Γ(U.1.toScheme, V)
            (LinearMap.ker (affineSectionMap b.hom V)) ((I.comap U.1.ι).ideal V)) ∧
          (∀ V : U.1.toScheme.affineOpens, IsIPowerTorsion Γ(U.1.toScheme, V)
            (Γ((restrictCoherentModules U.1.ι G).obj, V) ⧸
              LinearMap.range (affineSectionMap b.hom V)) ((I.comap U.1.ι).ideal V))) :
    (formalPullbackModule X I G Fsys α).IsCoherent := by
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict _ (fun U : X.affineOpens => U.1)
    (iSup_affineOpens_eq_top X) fun U => ?_
  obtain ⟨F, b, β, hβ, hbK, hbC⟩ := h U
  have hLN : IsLocallyNoetherian U.1.toScheme := isLocallyNoetherian_of_isOpenImmersion U.1.ι
  have hiso : IsIso (formalPullbackFromAlgebraization U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α) F b β hβ) :=
    formalPullbackFromAlgebraization_isIso U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α) F b β hβ hbK hbC
  exact AlgebraicGeometry.isCoherent_of_moduleIso
    ((@asIso _ _ _ _ _ hiso ≪≫ (formalPullbackRestrictionIso U.1.ι I G Fsys α).symm)) F.property


end Stacks.Algebraization

end

