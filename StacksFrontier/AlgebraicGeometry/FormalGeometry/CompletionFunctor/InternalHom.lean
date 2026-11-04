module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction

/-!
# Completing the internal hom of two coherent modules

Let `X` be a locally Noetherian scheme, `I` a quasi-coherent ideal sheaf on `X` and `G`, `F`
coherent `𝒪_X`-modules. The internal hom `H = SheafHom(G, F)` is again coherent, so it has a
completion `H^∧` along `I`, and postcomposition with the projections `F ⟶ F / I ^ (n+1) F`
assembles into a comparison

`lim_n H / I ^ (n+1) H ⟶ SheafHom(G, lim_n F / I ^ (n+1) F)`.

The comparison is not an isomorphism level by level — the map
`H / I ^ n H ⟶ SheafHom(G, F / I ^ n F)` has kernel and cokernel annihilated by a power of `I`
— but it becomes one in the limit, which is the geometric half of Stacks 0882.

## Main definitions

* `Stacks.Algebraization.sheafHomFunctor` — internal hom with a fixed source, as an endofunctor
  of `X.Modules`; it preserves `ℕᵒᵖ`-limits, which is Stacks 03EN.
* `Stacks.Algebraization.internalHomCoherent` — the internal hom of two coherent modules, as a
  coherent module (Stacks 01CQ).
* `Stacks.Algebraization.completedSheafHomStageMap` and
  `Stacks.Algebraization.completedSheafHomStages` — the comparison at level `n`, and the
  resulting morphism of inverse systems.
* `Stacks.Algebraization.completedSheafHomComparison` — the comparison in the limit.
* `Stacks.Algebraization.internalHomEvaluation` — evaluation of a section of the internal hom on a
  section of the source, which over an affine open is the comparison with `Hom_{Γ(X,U)}`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_sheafHom_eq_bot` — if `I ^ n` annihilates `N` then it
  annihilates `SheafHom(G, N)`. This is what lets the level-`n` comparison descend to the
  quotient `H / I ^ (n+1) H`.
* `Stacks.Algebraization.completionProjection_completedSheafHomStageMap` and
  `Stacks.Algebraization.completedSheafHomComparison_π` — the normalizations of the two
  comparisons.
* `Stacks.Algebraization.completionToLimit_completedSheafHomComparison` — the comparison is
  compatible with the canonical maps from `H` and `F` into the limits. This is the identity that
  pins the comparison down on the image of `H`, and hence, the image being dense in the adic
  topology, everywhere.

## Implementation notes

The internal hom used here is the one carried by the Stacks 03EN functor
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor`, whose value is `rfl`-equal to
`Stacks.SheafOfModules.sheafHom`; that is what makes the coherence theorem of Stacks 01CQ
(`Stacks.SheafOfModules.sheafHom_isCoherent`) applicable to it without any transport. Its
sections over `U` are *definitionally* the morphisms `G|_U ⟶ N|_U` of presheaves of modules on
the slice site over `U`, which is how the annihilation statement is proved: a section is
multiplied by `r` componentwise, and each component lands in a module `I ^ n` annihilates.

`PreservesLimits` of the 03EN functor is `PreservesLimitsOfSize` at the ambient hom universe,
whereas `ℕᵒᵖ` is a `Category.{0, 0}`; `preservesSmallestLimits_of_preservesLimits` bridges the
two, and only then is `PreservesLimitsOfShape ℕᵒᵖ` available.

`coherentObj` of `CompletionFunctor.Adjunction` is used in place of `G.obj` wherever the result
feeds instance search: `AlgebraicGeometry.Scheme.Modules` is a `def` for
`SheafOfModules X.ringCatSheaf`, and the `PreservesLimitsOfShape` instance above, whose binder is
typed at the first presentation, is not found for an argument typed at the second.

For the same reason the naturality squares are explicit `Category.assoc`/`congrArg`/`Eq.trans`
chains rather than `rw` or `simp` calls, and `Scheme.Modules.map_smul` is applied as a term: a
rewrite motive mixing the two presentations is not type correct at the transparency `rw` builds
it at.

## References

* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
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

/-- Internal hom with a fixed source, as an endofunctor of the modules on a scheme. -/
public abbrev sheafHomFunctor (X : Scheme.{u}) (G : X.Modules) : X.Modules ⥤ X.Modules :=
  internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X) X.sheaf G

/-- **Stacks 03EN.** Internal hom with a fixed source preserves inverse limits indexed by `ℕᵒᵖ`.

The tag gives `PreservesLimits`, which is `PreservesLimitsOfSize` at the ambient hom universe;
`ℕᵒᵖ` is a `Category.{0, 0}`, so the size has to be shrunk first. -/
public instance sheafHomFunctor_preservesLimitsOfShape (X : Scheme.{u}) (G : X.Modules) :
    PreservesLimitsOfShape ℕᵒᵖ (sheafHomFunctor X G) :=
  letI : PreservesLimits (sheafHomFunctor X G) :=
    internalHomSecondFunctor_preservesLimits.{u, u, u, u} _ _ G
  letI : PreservesLimitsOfSize.{0, 0} (sheafHomFunctor X G) :=
    preservesSmallestLimits_of_preservesLimits _
  inferInstance

/-- The internal hom of two coherent modules is coherent. -/
public noncomputable def internalHomCoherent (X : Scheme.{u})
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf := by
  have hG : _root_.SheafOfModules.IsCoherent G.obj := G.property
  have hFs : Stacks.SheafOfModules.IsCoherent F.obj :=
    (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff F.obj).mp F.property
  letI : G.obj.IsCoherent := hG
  letI hfp : G.obj.IsFinitePresentation := isFinitePresentation_of_isCoherent G.obj
  refine ⟨(sheafHomFunctor X (coherentObj G)).obj F.obj, ?_⟩
  exact (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff _).mpr
    (@Stacks.SheafOfModules.sheafHom_isCoherent _ X.presheaf X.ringCatSheaf.property
      G.obj F.obj hfp hFs)

/-- The underlying module of `internalHomCoherent` is the internal hom, on the nose. -/
public theorem internalHomCoherent_obj (X : Scheme.{u})
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (internalHomCoherent X G F).obj = (sheafHomFunctor X (coherentObj G)).obj F.obj := rfl


/-- A section of a sheaf of modules that dies under restriction to every affine open refining
its domain is zero: the affine opens generate the topology and the sheaf is separated. -/
public theorem section_eq_zero_of_affine {X : Scheme.{u}} (N : X.Modules) {V : X.Opens}
    (s : Γ(N, V))
    (h : ∀ (W : X.affineOpens) (i : W.1 ⟶ V), N.val.map i.op s = 0) : s = 0 := by
  have hs : s ∈ (⊥ : N.Submodule).toSubmodule.obj (op V) :=
    mem_submodule_of_affine (⊥ : N.Submodule) V s fun W i => by
      rw [h W i]
      exact Submodule.zero_mem _
  exact (Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj N (op V)).le hs)

/-- If the subsheaf `I ^ n N` vanishes then a section of `I(U) ^ n` annihilates every section of
`N` over an affine open `U`. -/
public theorem smul_eq_zero_of_idealPowerMultiple_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (N : X.Modules) (hN : idealPowerMultiple I n N = ⊥) (U : X.affineOpens)
    {r : Γ(X, U)} (hr : r ∈ I.ideal U ^ n) (s : Γ(N, U)) : r • s = 0 :=
  (Submodule.mem_bot _).mp
    ((idealPower_smul_sections_eq_bot_of_idealPowerMultiple_eq_bot I n N hN U).le
      (Submodule.smul_mem_smul hr Submodule.mem_top))

/-- If `I ^ n` annihilates `N` then a section of `I(U) ^ n` annihilates every section of
`SheafHom(G, N)` over an affine open `U`.

A section of the internal hom over `U` is a morphism `G|_U ⟶ N|_U` on the slice site, and the
action of `r` multiplies each of its components by a restriction of `r`; each component lands in
`N`, where that restriction acts by zero. The components are checked over affine opens, which is
enough by `section_eq_zero_of_affine`. -/
public theorem idealPower_smul_sheafHom_section_eq_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ)
    (G N : X.Modules) (hN : idealPowerMultiple I n N = ⊥) (U : X.affineOpens)
    {r : Γ(X, U)} (hr : r ∈ I.ideal U ^ n)
    (α : ((sheafHomFunctor X G).obj N).val.obj (op U.1)) : r • α = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  refine Eq.trans
    (Stacks.SheafOfModules.internalHom_smul_app_apply X.presheaf G.val N.val U.1 r α V x) ?_
  apply section_eq_zero_of_affine N
  intro W i
  refine Eq.trans (Scheme.Modules.map_smul N i _ _) ?_
  have hrW : (X.presheaf.map (i ≫ V.unop.hom).op).hom r ∈ I.ideal W ^ n := by
    rw [← I.map_ideal' (i ≫ V.unop.hom).op, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have hcomp : (X.presheaf.map i.op).hom (fRestr X.presheaf U.1 r V) =
      (X.presheaf.map (i ≫ V.unop.hom).op).hom r := by
    show (X.presheaf.map i.op).hom ((X.presheaf.map V.unop.hom.op).hom r) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hcomp]
  exact smul_eq_zero_of_idealPowerMultiple_eq_bot I n N hN W hrW _


/-! ### Evaluation of the internal hom on sections -/

/-- **Evaluation of the internal hom on sections.** A section of `SheafHom(G, M)` over `U` is a
morphism `G|_U ⟶ M|_U` on the slice site over `U`; this reads off its component at the terminal
object `Over.mk (𝟙 U)` of that site, which is a `Γ(X, U)`-linear map `Γ(G, U) → Γ(M, U)`.

This is `Stacks.SheafOfModules.evalSection` of the internal-hom presheaf, with the module
structures pinned, and it is the map Stacks 0882 compares against `Hom_{Γ(X,U)}` over an affine
open. -/
public noncomputable def internalHomEvaluation {X : Scheme.{u}} (G M : X.Modules) (U : X.Opens) :
    ((sheafHomFunctor X G).obj M).val.obj (op U) →ₗ[Γ(X, U)] (Γ(G, U) →ₗ[Γ(X, U)] Γ(M, U)) where
  toFun f := (f.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r f := by
    ext x
    have hid : fRestr X.presheaf U r (op (Over.mk (𝟙 U))) = r := by
      change (X.presheaf.map (𝟙 U).op).hom r = r
      rw [op_id, CategoryTheory.Functor.map_id]
      rfl
    have h := Stacks.SheafOfModules.internalHom_smul_app_apply X.presheaf G.val M.val U r f
      (op (Over.mk (𝟙 U))) x
    rwa [hid] at h

/-- Evaluation is natural in the target: the internal hom of a morphism `f` acts on sections by
postcomposition with `f`. This holds by definition, which is why evaluation at the terminal
object of the slice site is the right map to compare against. -/
public theorem internalHomEvaluation_map {X : Scheme.{u}} (G : X.Modules) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (s : ((sheafHomFunctor X G).obj M).val.obj (op U)) (y : Γ(G, U)) :
    internalHomEvaluation G N U (((sheafHomFunctor X G).map f).val.app (op U) s) y =
      (f.val.app (op U)).hom (internalHomEvaluation G M U s y) := rfl


variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}

omit [IsLocallyNoetherian X] in
/-- If `I ^ n` annihilates `N`, then it annihilates the internal hom `SheafHom(G, N)`. This is what
lets the level-`n` comparison descend to the quotient `H / I ^ (n+1) H`. -/
public theorem idealPowerMultiple_sheafHom_eq_bot (n : ℕ) (G N : X.Modules)
    (hN : idealPowerMultiple I n N = ⊥) :
    idealPowerMultiple I n ((sheafHomFunctor X G).obj N) = ⊥ := by
  refine le_antisymm ((idealPowerMultiple_le_iff I n _ ⊥).2 fun U => ?_) bot_le
  refine Submodule.smul_le.2 fun r hr α _ => ?_
  exact (SheafOfModules.Submodule.bot_obj _ (op U.1)).ge
    ((Submodule.mem_bot _).mpr (idealPower_smul_sheafHom_section_eq_zero I n G N hN U hr α))

variable (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The level-`n` component of the comparison from the completion of the internal hom. -/
public noncomputable def completedSheafHomStageMap (n : ℕ) :
    ((completionFunctor X I).obj (internalHomCoherent X G F)).obj.obj (op n) ⟶
      (sheafHomFunctor X (coherentObj G)).obj (((completionFunctor X I).obj F).obj.obj (op n)) :=
  eqToHom (completionFunctor_obj X I (internalHomCoherent X G F) n) ≫
    cokernel.desc (C := X.Modules)
      (idealPowerMultiple I (n + 1) (internalHomCoherent X G F).obj).ι
      ((sheafHomFunctor X (coherentObj G)).map (completionProjection X I F n))
      (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) _
        (idealPowerMultiple_sheafHom_eq_bot (n + 1) (coherentObj G) _
          (((completionFunctor X I).obj F).property.2.1 n)))

/-- The normalization of the level-`n` comparison: composing it with the projection of the
internal hom onto the `n`-th term of its completion is postcomposition with the projection of
`F`. Since that projection is an epimorphism, this determines the comparison. -/
public theorem completionProjection_completedSheafHomStageMap (n : ℕ) :
    completionProjection X I (internalHomCoherent X G F) n ≫ completedSheafHomStageMap G F n =
      (sheafHomFunctor X (coherentObj G)).map (completionProjection X I F n) := by
  have hdesc := cokernel.π_desc (C := X.Modules)
    (idealPowerMultiple I (n + 1) (internalHomCoherent X G F).obj).ι
    ((sheafHomFunctor X (coherentObj G)).map (completionProjection X I F n))
    (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) _
      (idealPowerMultiple_sheafHom_eq_bot (n + 1) (coherentObj G) _
        (((completionFunctor X I).obj F).property.2.1 n)))
  rw [completionProjection, completedSheafHomStageMap]
  exact (comp_eqToHom_symm_comp_eqToHom _
    (completionFunctor_obj X I (internalHomCoherent X G F) n) _).trans hdesc

/-- The level-`n` comparisons assembled into a morphism of inverse systems from the completion of
the internal hom to the internal homs into the completion of `F`. -/
public noncomputable def completedSheafHomStages :
    ((completionFunctor X I).obj (internalHomCoherent X G F)).obj ⟶
      ((completionFunctor X I).obj F).obj ⋙ sheafHomFunctor X (coherentObj G) where
  app n := completedSheafHomStageMap G F n.unop
  naturality _m n a := by
    have hepi := epi_completionProjection X I (internalHomCoherent X G F) _m.unop
    have hL : completionProjection X I (internalHomCoherent X G F) _m.unop ≫
        (((completionFunctor X I).obj (internalHomCoherent X G F)).obj.map a ≫
          completedSheafHomStageMap G F n.unop) =
        (sheafHomFunctor X (coherentObj G)).map (completionProjection X I F n.unop) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ completedSheafHomStageMap G F n.unop)
            (completionProjection_map X I (internalHomCoherent X G F) a)).trans
          (completionProjection_completedSheafHomStageMap G F n.unop))
    have hR : completionProjection X I (internalHomCoherent X G F) _m.unop ≫
        (completedSheafHomStageMap G F _m.unop ≫
          (((completionFunctor X I).obj F).obj ⋙ sheafHomFunctor X (coherentObj G)).map a) =
        (sheafHomFunctor X (coherentObj G)).map (completionProjection X I F n.unop) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (sheafHomFunctor X (coherentObj G)).map
              (((completionFunctor X I).obj F).obj.map a))
            (completionProjection_completedSheafHomStageMap G F _m.unop)).trans
          (((sheafHomFunctor X (coherentObj G)).map_comp _ _).symm.trans
            (congrArg (sheafHomFunctor X (coherentObj G)).map (completionProjection_map X I F a))))
    exact (cancel_epi _).mp (hL.trans hR.symm)

/-- **The comparison of Stacks 0882.** The canonical map from the limit of the completion of
`SheafHom(G, F)` to the internal hom from `G` into the limit of the completion of `F`, obtained
from the morphism of systems and the fact that internal hom preserves limits. -/
public noncomputable def completedSheafHomComparison :
    limit (C := X.Modules)
        ((completionFunctor X I).obj (internalHomCoherent X G F)).obj ⟶
      (sheafHomFunctor X (coherentObj G)).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) :=
  limMap (completedSheafHomStages G F) ≫
    (preservesLimitIso (sheafHomFunctor X (coherentObj G))
      ((completionFunctor X I).obj F).obj).inv

/-- The normalization of the comparison against the limit projections. -/
public theorem completedSheafHomComparison_π (n : ℕᵒᵖ) :
    completedSheafHomComparison G F ≫ (sheafHomFunctor X (coherentObj G)).map
        (limit.π ((completionFunctor X I).obj F).obj n) =
      limit.π ((completionFunctor X I).obj (internalHomCoherent X G F)).obj n ≫
        completedSheafHomStageMap G F n.unop := by
  simp only [completedSheafHomComparison, Category.assoc, preservesLimitIso_inv_π,
    limMap_π, completedSheafHomStages]

/-- The comparison carries the canonical map of the internal hom into its limit to the internal
hom of the canonical map of `F` into its limit. This is the identity that computes the comparison
on the image of `SheafHom(G, F)`. -/
public theorem completionToLimit_completedSheafHomComparison :
    completionToLimit X I (internalHomCoherent X G F) ≫ completedSheafHomComparison G F =
      (sheafHomFunctor X (coherentObj G)).map (completionToLimit X I F) := by
  refine (isLimitOfPreserves (sheafHomFunctor X (coherentObj G))
    (limit.isLimit ((completionFunctor X I).obj F).obj)).hom_ext fun n => ?_
  show (completionToLimit X I (internalHomCoherent X G F) ≫ completedSheafHomComparison G F) ≫
      (sheafHomFunctor X (coherentObj G)).map
        (limit.π ((completionFunctor X I).obj F).obj n) =
    (sheafHomFunctor X (coherentObj G)).map (completionToLimit X I F) ≫
      (sheafHomFunctor X (coherentObj G)).map (limit.π ((completionFunctor X I).obj F).obj n)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => completionToLimit X I (internalHomCoherent X G F) ≫ k)
    (completedSheafHomComparison_π G F n)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ completedSheafHomStageMap G F n.unop)
    (completionToLimit_projection X I (internalHomCoherent X G F) n)) ?_
  refine Eq.trans (completionProjection_completedSheafHomStageMap G F n.unop) ?_
  refine Eq.trans (congrArg (sheafHomFunctor X (coherentObj G)).map
    (completionToLimit_projection X I F n).symm) ?_
  exact (sheafHomFunctor X (coherentObj G)).map_comp _ _

end Stacks.Algebraization

end
