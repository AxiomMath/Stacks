module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelImageAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.CategoryTheory.Limits.ImageSubobjectFactors
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The limit of the completed stable kernel images, and the second stabilization

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf and `α : F ⟶ G` a morphism of
coherent adic systems along `ℐ`. The first stabilization produced the stable kernel images
`Stacks.Coherent.stableKernelImage ℐ α m ⊆ F_m` and their inverse system. Each of them is a
coherent module, so the completion functor of Tag 0880 turns it into a coherent adic system; the
transition maps of the stable kernel images make these completions into an inverse system of
coherent adic systems, that is, a double system indexed by `ℕᵒᵖ × ℕᵒᵖ`. This file builds that
double system, takes its limit in the image level, and proves the *second* stabilization of
Tag 087X: for each fixed quotient level `n` the transition maps of the double system in the image
level are eventually isomorphisms.

Three ideas carry the argument. First, the stable kernel image at level `m` is annihilated by
`ℐ ᵐ⁺¹`, being a subobject of `F_m`, so for `n ≤ m` its `(n+1)`-st adic quotient receives a
canonical map to `F_n` landing in `ker(α_n)`; the limit over the image level therefore maps to
`ker(α_n)` as well. Second, a coherent module annihilated by `ℐ ᵇ⁺¹` is the limit of its own
completion — the projections past level `b` are isomorphisms — which identifies the sections of
the completion of the stable kernel image with the adic quotients of a module of global sections
over an affine scheme. Third, on an affine scheme Tag 087W presents `F_l` as a quotient of a
single completed module `M` and the sections of the stable kernel image as the image of `ker f`
under that quotient map, by `Stacks.Coherent.affineStableKernelImage_range`; Artin–Rees makes the
kernel of that quotient map meet `ker f` inside `𝔞 ⁿ⁺¹ ker f` once `l` is large, so the `(n+1)`-st
adic quotients of the images at two such levels are both the intrinsic `(n+1)`-st adic quotient of
`ker f` and the transition between them is bijective. Being an isomorphism is local, and a
Noetherian scheme has a finite cover by affine spectra, so finitely many Artin–Rees constants may
be taken at once.

## Main definitions

* `Stacks.Coherent.coherentStableKernelImageSystem` — the inverse system of stable kernel images,
  read in the category of coherent modules.
* `Stacks.Coherent.stableKernelImageCompletion` — the completion of a stable kernel image, as a
  coherent adic system.
* `Stacks.Coherent.stableKernelImageCompletion_project` — the map of completions induced by a
  transition of stable kernel images.
* `Stacks.Coherent.stableKernelImageCompletionDiagram` — the double system of these completions.
* `Stacks.Coherent.stableKernelImageQuotientDiagram` — its slice at a fixed quotient level `n`.
* `Stacks.Coherent.stableKernelImageLimitSystem` — the limit of the double system over the image
  level.
* `Stacks.Coherent.stableKernelImageLimitProjection` — its projections onto the terms of the
  slices.
* `Stacks.Coherent.stableKernelImageQuotientToLevel` and
  `Stacks.Coherent.stableKernelImageQuotientToKernel` — the canonical map from the `(n+1)`-st adic
  quotient of the stable kernel image at level `m ≥ n` to `F_n`, and its factorization through
  `ker(α_n)`.
* `Stacks.Coherent.stableKernelImageLimitToLevel` and
  `Stacks.Coherent.stableKernelImageLimitToKernel` — the same maps out of the limit system.
* `Stacks.Coherent.completionCone` — the cone on the completion of a coherent module with summit
  the module itself.
* `Stacks.Coherent.coherentModuleSections`, `Stacks.Coherent.completionSections` and
  `Stacks.Coherent.completionSectionsProjection` — the global sections of a coherent module, of a
  term of its completion, and the projection between them.
* `Stacks.AdicCompletion.linearMap_bijective_of_quotient_images` — the module-theoretic diagram
  chase the affine case runs on.

## Main results

* `Stacks.Coherent.stableKernelImage_idealPowerMultiple_eq_bot` — the stable kernel image at
  level `m` is annihilated by `ℐ ᵐ⁺¹`.
* `Stacks.Coherent.completionProjection_isIso` and `Stacks.Coherent.completionCone_isLimit` — a
  coherent module annihilated by a power of `ℐ` is the limit of its own completion.
* `Stacks.Coherent.affineCompletionProjection_ker_surjective` and
  `Stacks.Coherent.affineCompletionProjection_ker_surjective_of_idealSheaf` — on an affine scheme
  the projection onto a term of the completion of such a module is surjective with the expected
  kernel on global sections.
* `Stacks.Coherent.affineStableKernelImageQuotientMap_bijective` — on an affine Noetherian scheme
  the transitions of the completed stable kernel images are eventually bijective on global
  sections, with one Artin–Rees constant for all levels above the bound.
* `Stacks.Coherent.exists_restrictImageIso`, `Stacks.Coherent.kernelImageAt_restrictIso` and
  `Stacks.Coherent.stableKernelImage_restrictIso` — restriction along an open immersion commutes
  with images, with the levelwise kernel images and with the stabilized kernel images.
* `Stacks.Coherent.completion_restrictIso` and `Stacks.Coherent.completion_iso` — the completion
  functor commutes with restriction to an open and respects isomorphisms, termwise and
  compatibly with the canonical projections.
* `Stacks.Coherent.stableKernelImageCompletion_restrictIso` and
  `Stacks.Coherent.stableKernelImageCompletion_restrictMap_isIso` — restriction along an open
  immersion commutes with the completion of the stable kernel image, compatibly with the
  canonical projections, and transports invertibility of the canonical transitions.
* `Stacks.Coherent.specStableKernelImageQuotientMap_isIso` — the second stabilization on an
  affine spectrum.
* `Stacks.Coherent.stableKernelImageQuotientMap_eventually_isIso` — **the second stabilization**:
  for each quotient level `n` there is a constant `c` such that every transition of the slice
  diagram at `n` above level `n + c` is an isomorphism.

## Implementation notes

The double system is indexed by `ℕᵒᵖ` twice and is zero-indexed in both variables: the quotient
level `n` represents the Stacks source's `ℐ ⁿ⁺¹`, and the image level `m` the source's `F_{m+1}`.

The limit over the image level is taken in the functor category `ℕᵒᵖ ⥤ X.Modules`, so its terms
are only canonically isomorphic — not equal — to the limits of the slices; the identification is
`CategoryTheory.Limits.limitObjIsoLimitCompEvaluation`, and
`Stacks.Coherent.stableKernelImageLimitProjection` builds it into the projections once and for
all.

The three purely module-theoretic lemmas in `Stacks.AdicCompletion` below are a diagram chase for
a map between two quotients of two images of one submodule. They are stated for arbitrary targets
`D₁`, `D₂` of the quotient maps rather than for the literal quotient modules, which is what their
use here needs: the quotient maps are the projections of the completion functor, and the
identification of their targets with quotient modules is exactly what is being avoided.
`Stacks.AdicCompletion.projectedSubmoduleAdicQuotientMap_bijective` is the statement for the
literal quotients, and does not apply directly.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) {F G : CoherentAdicSystems I}

/-! ### The completions of the stable kernel images -/

/-- The stable kernel image at level `m`, as an object of the category of coherent modules: it is
coherent by `Stacks.Coherent.stableKernelImage_isCoherent`. This is the shape the completion
functor of Tag 0880 accepts. -/
public abbrev coherentStableKernelImage (α : F ⟶ G) (m : ℕ) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨stableKernelImage I α m, stableKernelImage_isCoherent I α m⟩

/-- The inverse system of stable kernel images, read in the category of coherent modules: the
transition maps of `Stacks.Coherent.stableKernelImageSystem` are maps of coherent modules. This
is the system the completion functor of Tag 0880 is applied to. -/
public def coherentStableKernelImageSystem (α : F ⟶ G) :
    ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf where
  obj n := coherentStableKernelImage I α n.unop
  map {n m} f := ObjectProperty.homMk
    (stableKernelImage_project I α m.unop n.unop (leOfHom f.unop))
  map_id n := ObjectProperty.hom_ext _ (stableKernelImage_project_self I α n.unop)
  map_comp f g := ObjectProperty.hom_ext _
    (stableKernelImage_project_trans I α _ _ _ (leOfHom g.unop) (leOfHom f.unop)).symm

/-- **The completion of the stable kernel image at level `m`**: the coherent adic system of its
successive adic quotients, obtained by applying the completion functor of Tag 0880. -/
public def stableKernelImageCompletion (α : F ⟶ G) (m : ℕ) : CoherentAdicSystems I :=
  (Stacks.Algebraization.completionFunctor X I).obj (coherentStableKernelImage I α m)

/-- The `n`-th term of the completion of the stable kernel image at level `m` is its `(n+1)`-st
adic quotient. -/
public theorem stableKernelImageCompletion_obj (α : F ⟶ G) (m n : ℕ) :
    (stableKernelImageCompletion I α m).obj.obj (op n) =
      Stacks.Algebraization.idealPowerQuotient I (n + 1) (stableKernelImage I α m) :=
  Stacks.Algebraization.completionFunctor_obj X I (coherentStableKernelImage I α m) n

/-- The transition map of the stable kernel images at `n ≤ m`, read as a map of coherent
modules. -/
public abbrev coherentStableKernelImage_project (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    coherentStableKernelImage I α m ⟶ coherentStableKernelImage I α n :=
  ObjectProperty.homMk (stableKernelImage_project I α n m h)

/-- The map of completions induced by the transition map of the stable kernel images at `n ≤ m`:
the second variable of the double system of Tag 087X. -/
public def stableKernelImageCompletion_project (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    stableKernelImageCompletion I α m ⟶ stableKernelImageCompletion I α n :=
  (Stacks.Algebraization.completionFunctor X I).map
    (coherentStableKernelImage_project I α n m h)

/-- **The double system of the completed stable kernel images.** The image level `m` indexes the
completions `Stacks.Coherent.stableKernelImageCompletion`, each of which is itself an inverse
system in the quotient level. -/
public def stableKernelImageCompletionDiagram (α : F ⟶ G) : ℕᵒᵖ ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  coherentStableKernelImageSystem I α ⋙ Stacks.Algebraization.completionFunctor X I ⋙
    ObjectProperty.ι (IsCoherentAdicSystem I)

/-- The slice of the double system at a fixed quotient level `n`: the inverse system, in the
image level, of the `(n+1)`-st adic quotients of the stable kernel images. The second
stabilization of Tag 087X is a statement about this diagram. -/
public def stableKernelImageQuotientDiagram (α : F ⟶ G) (n : ℕ) : ℕᵒᵖ ⥤ X.Modules :=
  coherentStableKernelImageSystem I α ⋙ Stacks.Algebraization.completionFunctor X I ⋙
    ObjectProperty.ι (IsCoherentAdicSystem I) ⋙ (evaluation ℕᵒᵖ X.Modules).obj (op n)

/-- The `m`-th term of the slice diagram at quotient level `n` is the `(n+1)`-st adic quotient of
the stable kernel image at level `m`. -/
public theorem stableKernelImageQuotientDiagram_obj (α : F ⟶ G) (n m : ℕ) :
    (stableKernelImageQuotientDiagram I α n).obj (op m) =
      Stacks.Algebraization.idealPowerQuotient I (n + 1) (stableKernelImage I α m) := by
  dsimp only [stableKernelImageQuotientDiagram, Functor.comp_obj]
  exact Stacks.Algebraization.completionFunctor_obj X I (coherentStableKernelImage I α m) n

/-- The transition maps of the slice diagram are the components of the maps of completions. -/
public theorem stableKernelImageQuotientDiagram_map (α : F ⟶ G) (n k m : ℕ) (h : k ≤ m) :
    (stableKernelImageQuotientDiagram I α n).map (homOfLE h).op =
      (stableKernelImageCompletion_project I α k m h).hom.app (op n) := by
  dsimp only [stableKernelImageQuotientDiagram, stableKernelImageCompletion_project,
    Functor.comp_map]
  rfl

/-- **The limit of the double system over the image level**, an inverse system in the quotient
level. Its term at `n` is the limit of the `(n+1)`-st adic quotients of all the stable kernel
images. -/
public def stableKernelImageLimitSystem (α : F ⟶ G) : ℕᵒᵖ ⥤ X.Modules :=
  limit (stableKernelImageCompletionDiagram I α)

/-- The terms of the limit system are the limits of the slice diagrams: limits in a functor
category are computed pointwise. -/
public def stableKernelImageLimitSystem_objIso (α : F ⟶ G) (n : ℕ) :
    (stableKernelImageLimitSystem I α).obj (op n) ≅
      limit (stableKernelImageQuotientDiagram I α n) :=
  limitObjIsoLimitCompEvaluation (stableKernelImageCompletionDiagram I α) (op n)

/-- The projection from the `n`-th term of the limit system onto the `(n+1)`-st adic quotient of
the stable kernel image at level `m`. -/
public def stableKernelImageLimitProjection (α : F ⟶ G) (n m : ℕ) :
    (stableKernelImageLimitSystem I α).obj (op n) ⟶
      Stacks.Algebraization.idealPowerQuotient I (n + 1) (stableKernelImage I α m) :=
  (stableKernelImageLimitSystem_objIso I α n).hom ≫
    limit.π (stableKernelImageQuotientDiagram I α n) (op m) ≫
      eqToHom (stableKernelImageQuotientDiagram_obj I α n m)

/-- The projections of the limit system are compatible with the transition maps of the slice
diagram. -/
public theorem stableKernelImageLimitProjection_transition (α : F ⟶ G) (n k m : ℕ) (h : k ≤ m) :
    (stableKernelImageLimitSystem_objIso I α n).hom ≫
        limit.π (stableKernelImageQuotientDiagram I α n) (op m) ≫
          (stableKernelImageQuotientDiagram I α n).map (homOfLE h).op =
      (stableKernelImageLimitSystem_objIso I α n).hom ≫
        limit.π (stableKernelImageQuotientDiagram I α n) (op k) :=
  congrArg (fun t => (stableKernelImageLimitSystem_objIso I α n).hom ≫ t)
    (limit.w (stableKernelImageQuotientDiagram I α n) (homOfLE h).op)

/-- Once the slice diagram at quotient level `n` is eventually constant to the image level `m`,
the projection of the limit system onto the term at `m` is an isomorphism. -/
public theorem stableKernelImageLimitProjection_isIso (α : F ⟶ G) (n m : ℕ)
    (h : (stableKernelImageQuotientDiagram I α n).IsEventuallyConstantTo (op m)) :
    IsIso (stableKernelImageLimitProjection I α n m) := by
  have : IsIso (limit.π (stableKernelImageQuotientDiagram I α n) (op m)) :=
    h.isIso_π_of_isLimit (limit.isLimit _)
  dsimp only [stableKernelImageLimitProjection]
  infer_instance

/-- A uniform stabilization bound makes the slice diagram eventually constant: `ℕᵒᵖ` has at most
one morphism between any two objects, so every morphism into `op (n + c)` is the one named by the
hypothesis. -/
public theorem stableKernelImageQuotientDiagram_eventuallyConstant (α : F ⟶ G) (n c : ℕ)
    (h : ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso ((stableKernelImageQuotientDiagram I α n).map (homOfLE hml).op)) :
    (stableKernelImageQuotientDiagram I α n).IsEventuallyConstantTo (op (n + c)) := by
  intro i f
  have hl : n + c ≤ i.unop := leOfHom f.unop
  have hf : f = (homOfLE hl).op := Subsingleton.elim _ _
  subst hf
  exact h (n + c) le_rfl i.unop hl

/-- Past a uniform stabilization bound every projection of the limit system is an isomorphism. -/
public theorem stableKernelImageLimitProjection_isIso_of_bound (α : F ⟶ G) (n c m : ℕ)
    (hm : n + c ≤ m)
    (h : (stableKernelImageQuotientDiagram I α n).IsEventuallyConstantTo (op (n + c))) :
    IsIso (stableKernelImageLimitProjection I α n m) :=
  stableKernelImageLimitProjection_isIso I α n m (h.precomp (homOfLE hm).op)

/-- The maps of completions are the maps induced on the adic quotients: they commute with the
canonical projections out of the stable kernel images. -/
public theorem stableKernelImageCompletion_project_projection (α : F ⟶ G) (n m : ℕ) (h : n ≤ m)
    (k : ℕ) :
    Stacks.Algebraization.completionProjection X I (coherentStableKernelImage I α m) k ≫
        (stableKernelImageCompletion_project I α n m h).hom.app (op k) =
      stableKernelImage_project I α n m h ≫
        Stacks.Algebraization.completionProjection X I (coherentStableKernelImage I α n) k :=
  Stacks.Algebraization.completionFunctor_map_quotient X I
    (coherentStableKernelImage_project I α n m h) k

/-! ### The maps to the levelwise kernels -/

/-- **The stable kernel image at level `m` is annihilated by `ℐ ᵐ⁺¹`**, being a subobject of the
term `F_m`, which is annihilated by `ℐ ᵐ⁺¹` as part of the adic-system condition. -/
public theorem stableKernelImage_idealPowerMultiple_eq_bot (α : F ⟶ G) (m : ℕ) :
    Stacks.Algebraization.idealPowerMultiple I (m + 1) (stableKernelImage I α m) = ⊥ := by
  refine Stacks.Algebraization.idealPowerMultiple_eq_bot_of_affine_sections_annihilated
    fun V a ha x => ?_
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, V.1) :=
    SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  have hfl : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hinj : Function.Injective (E.map (stableKernelImageIncl I α m)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hzero : a • (stableKernelImageIncl I α m).app V.1 x = 0 :=
    Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_eq_bot
      (F.property.idealPowerMultiple_eq_bot m) V ha _
  refine hinj ?_
  show (stableKernelImageIncl I α m).app V.1 (a • x) =
    (stableKernelImageIncl I α m).app V.1 0
  rw [Scheme.Modules.Hom.app_smul, hzero, map_zero]

/-- For `n ≤ m` the inclusion of the stable kernel image at level `m` into `F_n` annihilates the
subsheaf `ℐ ⁿ⁺¹` of its source, since `F_n` itself is annihilated by `ℐ ⁿ⁺¹`. It therefore
factors through the `(n+1)`-st adic quotient. -/
public theorem stableKernelImage_toLevel_killsIdealPower (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    ((Stacks.Algebraization.idealPowerMultiple I (n + 1) (stableKernelImage I α m)).ι :
          ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
            (stableKernelImage I α m)).toSheafOfModules : X.Modules) ⟶
            stableKernelImage I α m) ≫
        (stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op) =
      (0 : ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
        (stableKernelImage I α m)).toSheafOfModules : X.Modules) ⟶ _) :=
  Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1)
    (stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op)
    (F.property.idealPowerMultiple_eq_bot n)

/-- **The canonical map from the `(n+1)`-st adic quotient of the stable kernel image at level
`m ≥ n` to `F_n`**, induced by the inclusion into `F_m` followed by the transition map of `F`. -/
public def stableKernelImageQuotientToLevel (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    Stacks.Algebraization.idealPowerQuotient I (n + 1) (stableKernelImage I α m) ⟶
      F.obj.obj (op n) :=
  cokernel.desc _ (stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op)
    (stableKernelImage_toLevel_killsIdealPower I α n m h)

/-- The canonical map out of the adic quotient computes the inclusion into `F_n` on
representatives. -/
public theorem stableKernelImageQuotientToLevel_comp (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1)
          (stableKernelImage I α m)).ι ≫
        stableKernelImageQuotientToLevel I α n m h =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op :=
  cokernel.π_desc _ _ _

/-- The canonical map out of the adic quotient lands in the kernel of `α_n`: the stable kernel
image is annihilated by `α`. -/
public theorem stableKernelImageQuotientToLevel_comp_alpha (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    stableKernelImageQuotientToLevel I α n m h ≫ α.hom.app (op n) = 0 := by
  have : Epi (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I (n + 1)
      (stableKernelImage I α m)).ι) :=
    Stacks.Algebraization.epi_cokernel_π_submodule_ι _
  refine (cancel_epi (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
    I (n + 1) (stableKernelImage I α m)).ι)).mp ?_
  calc
    _ = (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I (n + 1)
            (stableKernelImage I α m)).ι ≫ stableKernelImageQuotientToLevel I α n m h) ≫
          α.hom.app (op n) := (Category.assoc _ _ _).symm
    _ = (stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op) ≫ α.hom.app (op n) :=
      congrArg (fun t => t ≫ α.hom.app (op n))
        (stableKernelImageQuotientToLevel_comp I α n m h)
    _ = (stableKernelImageIncl I α m ≫ α.hom.app (op m)) ≫ G.obj.map (homOfLE h).op := by
      simp only [Category.assoc, α.hom.naturality]
    _ = 0 := by rw [stableKernelImageIncl_comp]; simp
    _ = _ := comp_zero.symm

/-- **The canonical map from the `(n+1)`-st adic quotient of the stable kernel image at level
`m ≥ n` to the kernel of `α_n`**, the factorization of
`Stacks.Coherent.stableKernelImageQuotientToLevel` through that kernel. -/
public def stableKernelImageQuotientToKernel (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    Stacks.Algebraization.idealPowerQuotient I (n + 1) (stableKernelImage I α m) ⟶
      kernel (α.hom.app (op n)) :=
  kernel.lift _ (stableKernelImageQuotientToLevel I α n m h)
    (stableKernelImageQuotientToLevel_comp_alpha I α n m h)

/-- The factorization through the kernel lies over the map to `F_n`. -/
public theorem stableKernelImageQuotientToKernel_ι (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    stableKernelImageQuotientToKernel I α n m h ≫ kernel.ι (α.hom.app (op n)) =
      stableKernelImageQuotientToLevel I α n m h :=
  kernel.lift_ι _ _ _

/-- On representatives the factorization through the kernel is the inclusion of the stable kernel
image into `F_n`. -/
public theorem stableKernelImageQuotientToKernel_projection (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1)
          (stableKernelImage I α m)).ι ≫
        stableKernelImageQuotientToKernel I α n m h ≫ kernel.ι (α.hom.app (op n)) =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op :=
  (congrArg (fun t => cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
        I (n + 1) (stableKernelImage I α m)).ι ≫ t)
      (stableKernelImageQuotientToKernel_ι I α n m h)).trans
    (stableKernelImageQuotientToLevel_comp I α n m h)

/-- The canonical map from the `n`-th term of the limit system to `F_n`, through the projection
onto the stable kernel image at the same level. -/
public def stableKernelImageLimitToLevel (α : F ⟶ G) (n : ℕ) :
    (stableKernelImageLimitSystem I α).obj (op n) ⟶ F.obj.obj (op n) :=
  stableKernelImageLimitProjection I α n n ≫ stableKernelImageQuotientToLevel I α n n le_rfl

/-- The canonical map out of the limit system lands in the kernel of `α_n`. -/
public theorem stableKernelImageLimitToLevel_comp_alpha (α : F ⟶ G) (n : ℕ) :
    stableKernelImageLimitToLevel I α n ≫ α.hom.app (op n) = 0 := by
  rw [stableKernelImageLimitToLevel, Category.assoc,
    stableKernelImageQuotientToLevel_comp_alpha, comp_zero]

/-- **The canonical map from the `n`-th term of the limit system to the kernel of `α_n`.** The
second stabilization is what makes this map an isomorphism. -/
public def stableKernelImageLimitToKernel (α : F ⟶ G) (n : ℕ) :
    (stableKernelImageLimitSystem I α).obj (op n) ⟶ kernel (α.hom.app (op n)) :=
  kernel.lift _ (stableKernelImageLimitToLevel I α n)
    (stableKernelImageLimitToLevel_comp_alpha I α n)

/-- The map out of the limit system lies over the map to `F_n`. -/
public theorem stableKernelImageLimitToKernel_ι (α : F ⟶ G) (n : ℕ) :
    stableKernelImageLimitToKernel I α n ≫ kernel.ι (α.hom.app (op n)) =
      stableKernelImageLimitToLevel I α n :=
  kernel.lift_ι _ _ _


/-! ### A power-annihilated coherent module is the limit of its completion -/

section Completion

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (J : Y.IdealSheafData)
  (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)

/-- **A coherent module annihilated by `𝒥 ⁿ⁺¹` is its own `(n+1)`-st adic quotient**: the
subsheaf being divided out is zero, so the quotient projection is an isomorphism. -/
public theorem completionProjection_isIso (n : ℕ)
    (h : Stacks.Algebraization.idealPowerMultiple J (n + 1) M.obj = ⊥) :
    IsIso (C := Y.Modules) (Stacks.Algebraization.completionProjection Y J M n) := by
  have hz : IsIso (cokernel.π (C := Y.Modules)
      (Stacks.Algebraization.idealPowerMultiple J (n + 1) M.obj).ι) :=
    Stacks.Algebraization.isIso_cokernel_π_of_idealPowerMultiple_eq_bot J (n + 1) M.obj h
  exact @IsIso.comp_isIso Y.Modules _ _ _ _ _ _ hz
    (eqToIso (Stacks.Algebraization.completionFunctor_obj Y J M n).symm).isIso_hom

/-- The projections of a coherent module onto the terms of its completion are compatible with
every transition map, in numeric form. -/
public theorem completionProjection_map {n m : ℕ} (h : n ≤ m) :
    Stacks.Algebraization.completionProjection Y J M m ≫
        ((Stacks.Algebraization.completionFunctor Y J).obj M).obj.map (homOfLE h).op =
      Stacks.Algebraization.completionProjection Y J M n :=
  Stacks.Algebraization.completionProjection_naturality J M (homOfLE h).op

/-- **The canonical cone on the completion of a coherent module**, with summit the module itself
and legs the quotient projections. -/
public def completionCone : Cone ((Stacks.Algebraization.completionFunctor Y J).obj M).obj where
  pt := M.obj
  π :=
    { app := fun n => Stacks.Algebraization.completionProjection Y J M n.unop
      naturality := fun {_ j} f =>
        (Category.id_comp (Stacks.Algebraization.completionProjection Y J M j.unop)).trans
          (Stacks.Algebraization.completionProjection_naturality J M f).symm }

/-- **A coherent module annihilated by a power of `𝒥` is the limit of its own completion.** Past
the annihilating exponent every projection `M ⟶ M / 𝒥 ᵏ⁺¹ M` is an isomorphism, so the inverse
system is eventually constant with value `M` and
`Stacks.Coherent.completionCone` is a limit cone. -/
public def completionCone_isLimit (b : ℕ)
    (hb : Stacks.Algebraization.idealPowerMultiple J (b + 1) M.obj = ⊥) :
    IsLimit (completionCone J M) := by
  have hp : ∀ m : ℕ, b ≤ m →
      IsIso (C := Y.Modules) (Stacks.Algebraization.completionProjection Y J M m) :=
    fun m hm => completionProjection_isIso J M m
      (Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le hb (Nat.add_le_add_right hm 1))
  let eb := @asIso Y.Modules _ _ _ (Stacks.Algebraization.completionProjection Y J M b)
    (hp b le_rfl)
  have hb₁ : Stacks.Algebraization.completionProjection Y J M b ≫ eb.inv = 𝟙 M.obj :=
    eb.hom_inv_id
  refine { lift := fun s => s.π.app (op b) ≫ eb.inv, fac := ?_, uniq := ?_ }
  · intro s n
    let ek := @asIso Y.Modules _ _ _
      (Stacks.Algebraization.completionProjection Y J M (max b n.unop))
      (hp (max b n.unop) (le_max_left _ _))
    have hA : ((Stacks.Algebraization.completionFunctor Y J).obj M).obj.map
          (homOfLE (le_max_left b n.unop)).op ≫ eb.inv ≫
          Stacks.Algebraization.completionProjection Y J M n.unop =
        ((Stacks.Algebraization.completionFunctor Y J).obj M).obj.map
          (homOfLE (le_max_right b n.unop)).op :=
      (ek.cancel_iso_hom_left _ _).mp <| (Category.assoc _ _ _).symm.trans <|
        (eq_whisker (completionProjection_map J M (le_max_left b n.unop)) _).trans <|
          (Category.assoc _ _ _).symm.trans <| (eq_whisker hb₁ _).trans <|
            (Category.id_comp _).trans (completionProjection_map J M (le_max_right b n.unop)).symm
    exact (Category.assoc _ _ _).trans <|
      (s.w_assoc (homOfLE (le_max_left b n.unop)).op _).symm.trans <|
        (congrArg (s.π.app _ ≫ ·) hA).trans (s.w (homOfLE (le_max_right b n.unop)).op)
  · exact fun s f hf => eb.eq_comp_inv.mpr (hf (op b))

/-- The global sections of a coherent module, as a module over the ring of global sections. -/
public abbrev coherentModuleSections : ModuleCat.{u} Γ(Y, ⊤) :=
  (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj M.obj

/-- The global sections of the `n`-th term of the completion of a coherent module, as a module
over the ring of global sections. -/
public abbrev completionSections (n : ℕ) : ModuleCat.{u} Γ(Y, ⊤) :=
  (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj
    (((Stacks.Algebraization.completionFunctor Y J).obj M).obj.obj (op n))

/-- The projection of a coherent module onto the `n`-th term of its completion, on global
sections. -/
public abbrev completionSectionsProjection (n : ℕ) :
    coherentModuleSections M ⟶ completionSections J M n :=
  (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
    (Stacks.Algebraization.completionProjection Y J M n)

end Completion

/-- **The sections of the completion of a power-annihilated coherent module on an affine
Noetherian scheme.** The projection onto the `n`-th term of the completion is surjective on
global sections with kernel `J ⁿ⁺¹` times everything.

By `Stacks.Coherent.completionCone_isLimit` the module is the limit of its completion; global
sections preserve that limit, so the module of global sections is the limit of the global
sections of the completion, which Tag 087W identifies with the completed module of the
completion. Under that identification the projection becomes
`Stacks.Coherent.affineLevelProjection`, whose kernel and surjectivity are known. -/
public theorem affineCompletionProjection_ker_surjective (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (b : ℕ)
    (hb : Stacks.Algebraization.idealPowerMultiple
      (Scheme.IdealSheafData.ofIdealTop J) (b + 1) M.obj = ⊥) (n : ℕ) :
    LinearMap.ker
          (completionSectionsProjection (Scheme.IdealSheafData.ofIdealTop J) M n).hom =
        J ^ (n + 1) • (⊤ : Submodule Γ(Y, ⊤) (coherentModuleSections M)) ∧
      Function.Surjective
        (completionSectionsProjection (Scheme.IdealSheafData.ofIdealTop J) M n).hom := by
  let I := Scheme.IdealSheafData.ofIdealTop J
  let E : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  let H := (Stacks.Algebraization.completionFunctor Y I).obj M
  have hpl : PreservesLimitsOfShape ℕᵒᵖ E :=
    SheafOfModules.evaluationPreservesLimitsOfShape _ _ _
  let hlim := isLimitOfPreserves E (completionCone_isLimit I M b hb)
  let e : E.obj M.obj ≅ limit (globalSectionsSystem H) :=
    hlim.conePointUniqueUpToIso (limit.isLimit _)
  let a := globalSectionsComparison Y J H ≪≫ e.symm
  have ha : a.hom ≫ E.map (Stacks.Algebraization.completionProjection Y I M n) =
      affineLevelProjection Y J H n := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc]
    exact congrArg (fun t => (globalSectionsComparison Y J H).hom ≫ t)
      (hlim.conePointUniqueUpToIso_inv_comp (limit.isLimit _) (op n))
  have hsurj : Function.Surjective a.hom.hom :=
    (ModuleCat.epi_iff_surjective a.hom).mp inferInstance
  have hrange : LinearMap.range a.hom.hom = ⊤ := LinearMap.range_eq_top.mpr hsurj
  refine ⟨?_, fun x => ?_⟩
  · have hker := congrArg (fun q => Submodule.map a.hom.hom (LinearMap.ker q.hom)) ha
    simp only [ModuleCat.hom_comp, LinearMap.ker_comp,
      Submodule.map_comap_eq_of_surjective hsurj] at hker
    rw [affineLevelProjection_ker, Submodule.map_smul'', Submodule.map_top, hrange] at hker
    exact hker
  · obtain ⟨y, hy⟩ := affineLevelProjection_surjective Y J H n x
    exact ⟨a.hom.hom y, (congrArg (fun q => ModuleCat.Hom.hom q y) ha).trans hy⟩

/-- **The sections of the completion of a power-annihilated coherent module**, stated for a
quasi-coherent ideal sheaf rather than for an ideal of global sections. On an affine scheme the
two are the same datum, by `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`. -/
public theorem affineCompletionProjection_ker_surjective_of_idealSheaf (Y : Scheme.{u})
    [IsAffine Y] [IsNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (J : Y.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (b : ℕ)
    (hb : Stacks.Algebraization.idealPowerMultiple J (b + 1) M.obj = ⊥) (n : ℕ) :
    LinearMap.ker (completionSectionsProjection J M n).hom =
        J.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ (n + 1) •
          (⊤ : Submodule Γ(Y, ⊤) (coherentModuleSections M)) ∧
      Function.Surjective (completionSectionsProjection J M n).hom := by
  obtain ⟨J, rfl⟩ := (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).symm.surjective J
  obtain ⟨hk, hs⟩ := affineCompletionProjection_ker_surjective Y J M b hb n
  refine ⟨hk.trans ?_, hs⟩
  exact congrArg (fun K : Ideal Γ(Y, ⊤) =>
      K ^ (n + 1) • (⊤ : Submodule Γ(Y, ⊤) (coherentModuleSections M)))
    ((Scheme.IdealSheafData.equivOfIsAffine (X := Y)).apply_symm_apply J).symm

end Stacks.Coherent

namespace Stacks.AdicCompletion

/-! ### A map between two quotients of two images of a submodule -/

/-- Precomposing a quotient map whose kernel is `J` times everything with a surjection whose
kernel is contained in `J` times everything again has kernel `J` times everything. -/
public theorem ker_comp_eq_smul_of_surjective {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (J : Ideal R)
    (s : A →ₗ[R] B) (q : B →ₗ[R] C) (hs : Function.Surjective s)
    (hker : LinearMap.ker s ≤ J • (⊤ : Submodule R A))
    (hq : LinearMap.ker q = J • (⊤ : Submodule R B)) :
    LinearMap.ker (q.comp s) = J • (⊤ : Submodule R A) := by
  rw [LinearMap.ker_comp, hq]
  have hmap : Submodule.map s (J • (⊤ : Submodule R A)) = J • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hs]
  rw [← hmap, Submodule.comap_map_eq_self hker]

/-- **Two surjections with the same kernel present the same quotient.** If `f ∘ s = t` with `s`
and `t` surjective and `ker s = ker t`, then `f` is bijective. -/
public theorem linearMap_bijective_of_comp_ker {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (s : A →ₗ[R] B) (t : A →ₗ[R] C) (f : B →ₗ[R] C)
    (hs : Function.Surjective s) (ht : Function.Surjective t)
    (hker : LinearMap.ker s = LinearMap.ker t) (hf : f.comp s = t) :
    Function.Bijective f := by
  refine ⟨?_, fun z => ?_⟩
  · refine LinearMap.ker_eq_bot.mp (le_antisymm (fun y hy => ?_) bot_le)
    obtain ⟨x, rfl⟩ := hs y
    have hx : x ∈ LinearMap.ker t := by
      show t x = 0
      rw [← hf]
      exact hy
    exact (show x ∈ LinearMap.ker s from hker.symm ▸ hx)
  · obtain ⟨x, rfl⟩ := ht z
    exact ⟨s x, congrArg (fun g : A →ₗ[R] C => g x) hf⟩

/-- A projection `p : A → B` whose kernel is inside `J • ⊤` and whose range is that of an
injection `i : C → B` factors through a surjection `s : A → C` with `i ∘ s = p`, and composing
with a surjection `q` with kernel `J • ⊤` again gives kernel `J • ⊤`. -/
private theorem exists_surjective_comp_ker_smul {R A B C D : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (J : Ideal R)
    (p : A →ₗ[R] B) (i : C →ₗ[R] B) (q : C →ₗ[R] D) (hi : Function.Injective i)
    (hr : LinearMap.range i = LinearMap.range p) (hp : LinearMap.ker p ≤ J • (⊤ : Submodule R A))
    (hq : LinearMap.ker q = J • (⊤ : Submodule R C)) :
    ∃ s : A →ₗ[R] C, Function.Surjective s ∧ (∀ x, i (s x) = p x) ∧
      LinearMap.ker (q.comp s) = J • (⊤ : Submodule R A) := by
  let e := LinearEquiv.ofInjective i hi
  let s := e.symm.toLinearMap.comp (p.codRestrict (LinearMap.range i) fun x => hr.symm ▸ ⟨x, rfl⟩)
  have h : ∀ x, i (s x) = p x := fun _ => congrArg Subtype.val (e.apply_symm_apply _)
  have hs' : Function.Surjective s := by
    intro y
    obtain ⟨x, hx⟩ := hr ▸ (show i y ∈ LinearMap.range i from ⟨y, rfl⟩)
    exact ⟨x, hi ((h x).trans hx)⟩
  exact ⟨s, hs', h, ker_comp_eq_smul_of_surjective J s q hs' (fun x hx =>
    hp (show p x = 0 by rw [← h, show s x = 0 from hx, map_zero])) hq⟩

/-- **The diagram chase behind the second stabilization of Tag 087X.** A submodule of `A` is
presented, through two projections `p₁ : A → B₁` and `p₂ : A → B₂` with `p₂ = t ∘ p₁`, as the
images `C₁` and `C₂` (via injections `i₁`, `i₂` with ranges those of `p₁`, `p₂`, and a map `j`
over `t`); `q₁ : C₁ → D₁` and `q₂ : C₂ → D₂` are surjections with kernel `J` times everything,
and `f : D₁ → D₂` satisfies `f ∘ q₁ = q₂ ∘ j`. If the kernels of `p₁` and `p₂` are contained in
`J` times everything, then `f` is bijective.

Both `D₁` and `D₂` are then the quotient of `A` by `J` times everything: the injections identify
`Cᵢ` with the image of `pᵢ`, so `qᵢ ∘ pᵢ` is a surjection out of `A` whose kernel is `J` times
everything by `Stacks.AdicCompletion.ker_comp_eq_smul_of_surjective`, and `f` matches the two
presentations. -/
public theorem linearMap_bijective_of_quotient_images
    {R A B₁ B₂ C₁ C₂ D₁ D₂ : Type*} [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂]
    [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
    (J : Ideal R) (p₁ : A →ₗ[R] B₁) (p₂ : A →ₗ[R] B₂)
    (i₁ : C₁ →ₗ[R] B₁) (i₂ : C₂ →ₗ[R] B₂)
    (q₁ : C₁ →ₗ[R] D₁) (q₂ : C₂ →ₗ[R] D₂)
    (t : B₁ →ₗ[R] B₂) (j : C₁ →ₗ[R] C₂) (f : D₁ →ₗ[R] D₂)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂)
    (hr₁ : LinearMap.range i₁ = LinearMap.range p₁)
    (hr₂ : LinearMap.range i₂ = LinearMap.range p₂)
    (hp₁ : LinearMap.ker p₁ ≤ J • (⊤ : Submodule R A))
    (hp₂ : LinearMap.ker p₂ ≤ J • (⊤ : Submodule R A))
    (hq₁ : LinearMap.ker q₁ = J • (⊤ : Submodule R C₁))
    (hq₂ : LinearMap.ker q₂ = J • (⊤ : Submodule R C₂))
    (hs₁ : Function.Surjective q₁) (hs₂ : Function.Surjective q₂)
    (ht : t.comp p₁ = p₂) (hj : i₂.comp j = t.comp i₁)
    (hf : f.comp q₁ = q₂.comp j) : Function.Bijective f := by
  obtain ⟨s₁, hs₁', h₁, hk₁⟩ := exists_surjective_comp_ker_smul J p₁ i₁ q₁ hi₁ hr₁ hp₁ hq₁
  obtain ⟨s₂, hs₂', h₂, hk₂⟩ := exists_surjective_comp_ker_smul J p₂ i₂ q₂ hi₂ hr₂ hp₂ hq₂
  refine linearMap_bijective_of_comp_ker (q₁.comp s₁) (q₂.comp s₂) f
    (hs₁.comp hs₁') (hs₂.comp hs₂') (hk₁.trans hk₂.symm) ?_
  · refine LinearMap.ext fun x => (LinearMap.congr_fun hf (s₁ x)).trans (congrArg q₂ (hi₂ ?_))
    rw [h₂, ← ht, ← LinearMap.comp_apply i₂ j, hj, LinearMap.comp_apply, h₁,
      LinearMap.comp_apply]

end Stacks.AdicCompletion

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) {F G : CoherentAdicSystems I}

/-! ### The affine case of the second stabilization -/

/-- **The transitions of the completed stable kernel images are eventually bijective on the
global sections of an affine Noetherian scheme**, with one Artin–Rees constant serving all source
levels above the bound.

Tag 087W presents every term of `F` as a quotient of one completed module `M`, with
`Stacks.Coherent.affineLevelProjection` as the projection, and
`Stacks.Coherent.affineStableKernelImage_range` identifies the global sections of the stable
kernel image at level `k` with the image of `ker f` under that projection. Artin–Rees, in the form
`Stacks.AdicCompletion.exists_comap_subtype_pow_smul_restrictScalars_le`, supplies a constant `c`
past which the kernel of that projection meets `ker f` inside `J ⁿ⁺¹ ker f`; the projection out of
the stable kernel image onto the `(n+1)`-st term of its completion has kernel `J ⁿ⁺¹` times
everything by `Stacks.Coherent.affineCompletionProjection_ker_surjective`, so
`Stacks.AdicCompletion.linearMap_bijective_of_quotient_images` applies. -/
public theorem affineStableKernelImageQuotientMap_bijective (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (J : Ideal Γ(Y, ⊤))
    {H K : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop J)} (α : H ⟶ K) (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      Function.Bijective ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map
        ((stableKernelImageCompletion_project (Scheme.IdealSheafData.ofIdealTop J)
          α m l hml).hom.app (op n))).hom := by
  let I := Scheme.IdealSheafData.ofIdealTop J
  let E : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  have hfl : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  let Q := coherentAdicSystemsEquivFGModuleCat Y J
  let _ : Module (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J H) :=
    (Q.functor.obj H).obj.isModule
  let _ : IsScalarTower Γ(Y, ⊤) (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J H) :=
    IsScalarTower.of_compHom _ _ _
  let _ : Module.Finite (AdicCompletion J Γ(Y, ⊤)) (completedModuleAsBase Y J H) :=
    inferInstanceAs (Module.Finite (AdicCompletion J Γ(Y, ⊤)) (Q.functor.obj H))
  let f : completedModuleAsBase Y J H →ₗ[AdicCompletion J Γ(Y, ⊤)]
      completedModuleAsBase Y J K := (Q.functor.map α).hom.hom
  obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_comap_subtype_pow_smul_restrictScalars_le
    J (LinearMap.ker f)
  refine ⟨c, fun m hm l hml => ?_⟩
  let K₀ : Submodule Γ(Y, ⊤) (completedModuleAsBase Y J H) :=
    (LinearMap.ker f).restrictScalars Γ(Y, ⊤)
  let p : ∀ k : ℕ, K₀ →ₗ[Γ(Y, ⊤)] (globalSectionsSystem H).obj (op k) := fun k =>
    (affineLevelProjection Y J H k).hom.comp K₀.subtype
  have hi : ∀ k : ℕ, Function.Injective (E.map (stableKernelImageIncl I α k)).hom := fun k =>
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hr : ∀ k : ℕ, LinearMap.range (E.map (stableKernelImageIncl I α k)).hom =
      LinearMap.range (p k) := fun k =>
    (affineStableKernelImage_range Y J α k).trans (by
      rw [LinearMap.range_comp, Submodule.range_subtype]; rfl)
  have hp : ∀ k : ℕ, n + c ≤ k →
      LinearMap.ker (p k) ≤ J ^ (n + 1) • (⊤ : Submodule Γ(Y, ⊤) K₀) := fun k hk => by
    rw [LinearMap.ker_comp, affineLevelProjection_ker]
    exact hc (n + 1) (k + 1) (by omega)
  have hq : ∀ k : ℕ,
      LinearMap.ker (completionSectionsProjection I (coherentStableKernelImage I α k) n).hom =
          J ^ (n + 1) • (⊤ : Submodule Γ(Y, ⊤)
            (coherentModuleSections (coherentStableKernelImage I α k))) ∧
        Function.Surjective
          (completionSectionsProjection I (coherentStableKernelImage I α k) n).hom := fun k =>
    affineCompletionProjection_ker_surjective Y J (coherentStableKernelImage I α k) k
      (stableKernelImage_idealPowerMultiple_eq_bot I α k) n
  refine Stacks.AdicCompletion.linearMap_bijective_of_quotient_images (J ^ (n + 1))
    (p l) (p m) (E.map (stableKernelImageIncl I α l)).hom
    (E.map (stableKernelImageIncl I α m)).hom
    (completionSectionsProjection I (coherentStableKernelImage I α l) n).hom
    (completionSectionsProjection I (coherentStableKernelImage I α m) n).hom
    (E.map (H.obj.map (homOfLE hml).op)).hom
    (E.map (stableKernelImage_project I α m l hml)).hom _
    (hi l) (hi m) (hr l) (hr m) (hp l (hm.trans hml)) (hp m hm)
    (hq l).1 (hq m).1 (hq l).2 (hq m).2 ?_ ?_ ?_
  · have ht : affineLevelProjection Y J H l ≫ E.map (H.obj.map (homOfLE hml).op) =
        affineLevelProjection Y J H m :=
      congrArg (fun z => (globalSectionsComparison Y J H).hom ≫ z)
        (limit.w (globalSectionsSystem H) (homOfLE hml).op)
    exact congrArg (fun z => (ModuleCat.Hom.hom z).comp K₀.subtype) ht
  · exact congrArg (fun z => (E.map z).hom) (stableKernelImage_project_comp I α m l hml)
  · exact congrArg (fun z => (E.map z).hom)
      (stableKernelImageCompletion_project_projection I α m l hml n)


/-! ### Restriction along an open immersion -/

/-- **Restriction along an open immersion commutes with images**, compatibly with the inclusions
into the target. Restriction is exact: it preserves the cokernel and the kernel out of which the
abelian image of a morphism is built, and the abelian image agrees with the categorical one. -/
public theorem exists_restrictImageIso {Y Z : Scheme.{u}} (r : Y ⟶ Z) [IsOpenImmersion r]
    {M N : Z.Modules} (a : M ⟶ N) :
    ∃ e : (Scheme.Modules.restrictFunctor r).obj (image a) ≅
        image ((Scheme.Modules.restrictFunctor r).map a),
      e.hom ≫ image.ι ((Scheme.Modules.restrictFunctor r).map a) =
        (Scheme.Modules.restrictFunctor r).map (image.ι a) := by
  let T := Scheme.Modules.restrictFunctor r
  have hpc : PreservesColimitsOfSize.{u, u} T :=
    (Scheme.Modules.restrictAdjunction r).leftAdjoint_preservesColimits
  have hpl : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor r))
  refine ⟨(T.mapIso (Abelian.imageIsoImage a)).symm ≪≫ Abelian.PreservesImage.iso T a ≪≫
    Abelian.imageIsoImage (T.map a), ?_⟩
  have h1 : (Abelian.imageIsoImage a).inv ≫ kernel.ι (cokernel.π a) = image.ι a := by
    rw [← Abelian.imageIsoImage_hom_comp_image_ι a, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  show (T.map (Abelian.imageIsoImage a).inv ≫
      ((Abelian.PreservesImage.iso T a).hom ≫ (Abelian.imageIsoImage (T.map a)).hom)) ≫
    image.ι (T.map a) = T.map (image.ι a)
  rw [Category.assoc, Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι,
    Abelian.PreservesImage.iso_hom_ι, ← T.map_comp, h1]

/-- **Restriction identifies the levelwise kernel images of the restricted system.** Restriction
preserves kernels, so the morphism whose image is the kernel image at level `l` restricts to the
corresponding morphism for the restricted system up to an isomorphism of its source; two
morphisms into a common object which factor through one another have the same image. -/
public theorem kernelImageAt_restrictIso {Y Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData) {H K : CoherentAdicSystems J}
    (α : H ⟶ K) (m l : ℕ) (h : m ≤ l) :
    ∃ e : (Scheme.Modules.restrictFunctor r).obj (kernelImageAt J α m l h) ≅
        kernelImageAt (J.comap r) ((restrictFunctor J r).map α) m l h,
      e.hom ≫ kernelImageAtIncl (J.comap r) ((restrictFunctor J r).map α) m l h =
        (Scheme.Modules.restrictFunctor r).map (kernelImageAtIncl J α m l h) := by
  let T := Scheme.Modules.restrictFunctor r
  have hpl : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor r))
  let a := kernel.ι (α.hom.app (op l)) ≫ H.obj.map (homOfLE h).op
  let b := kernel.ι (T.map (α.hom.app (op l))) ≫ T.map (H.obj.map (homOfLE h).op)
  let eK := PreservesKernel.iso T (α.hom.app (op l))
  have heK : eK.hom ≫ b = T.map a := by
    dsimp only [eK, b, a]
    rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι, T.map_comp]
  obtain ⟨e, he⟩ := imageIsoOfMutualFactors (T.map a) b ⟨eK.hom, heK⟩
    ⟨eK.inv, by rw [← heK, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]⟩
  obtain ⟨g, hg⟩ := exists_restrictImageIso r a
  refine ⟨g ≪≫ e, ?_⟩
  show (g.hom ≫ e.hom) ≫ image.ι b = T.map (image.ι a)
  rw [Category.assoc, he, hg]

/-- **The stabilized kernel images commute with restriction**, canonically over the restricted
term of `F`. Both sides are a kernel image computed from a level above both stabilization levels,
and `Stacks.Coherent.stableKernelImageIso` identifies each with the kernel image there. -/
public theorem stableKernelImage_restrictIso {Y Z : Scheme.{u}} [IsNoetherian Y]
    [IsNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    {H K : CoherentAdicSystems J} (α : H ⟶ K) (m : ℕ) :
    ∃ e : (Scheme.Modules.restrictFunctor r).obj (stableKernelImage J α m) ≅
        stableKernelImage (J.comap r) ((restrictFunctor J r).map α) m,
      e.hom ≫ stableKernelImageIncl (J.comap r) ((restrictFunctor J r).map α) m =
        (Scheme.Modules.restrictFunctor r).map (stableKernelImageIncl J α m) := by
  let α' := (restrictFunctor J r).map α
  let l := max (kernelStableLevel J α m) (kernelStableLevel (J.comap r) α' m)
  have hJ : kernelStableLevel J α m ≤ l := le_max_left _ _
  have hJ' : kernelStableLevel (J.comap r) α' m ≤ l := le_max_right _ _
  let e₁ := stableKernelImageIso J α m l hJ
  let e₂ := stableKernelImageIso (J.comap r) α' m l hJ'
  obtain ⟨e₀, he₀⟩ := kernelImageAt_restrictIso r J α m l
    ((le_kernelStableLevel J α m).trans hJ)
  refine ⟨((Scheme.Modules.restrictFunctor r).mapIso e₁).symm ≪≫ e₀ ≪≫ e₂, ?_⟩
  have he₂ : e₂.hom ≫ stableKernelImageIncl (J.comap r) α' m =
      kernelImageAtIncl (J.comap r) α' m l ((le_kernelStableLevel (J.comap r) α' m).trans hJ') :=
    stableKernelImageIso_hom_comp (J.comap r) α' m l hJ'
  have he₁ : e₁.inv ≫ kernelImageAtIncl J α m l ((le_kernelStableLevel J α m).trans hJ) =
      stableKernelImageIncl J α m :=
    stableKernelImageIso_inv_comp J α m l hJ
  show ((Scheme.Modules.restrictFunctor r).map e₁.inv ≫ e₀.hom ≫ e₂.hom) ≫
    stableKernelImageIncl (J.comap r) α' m =
      (Scheme.Modules.restrictFunctor r).map (stableKernelImageIncl J α m)
  rw [Category.assoc, Category.assoc, he₂, he₀]
  exact ((Scheme.Modules.restrictFunctor r).map_comp e₁.inv
      (kernelImageAtIncl J α m l ((le_kernelStableLevel J α m).trans hJ))).symm.trans
    (congrArg (Scheme.Modules.restrictFunctor r).map he₁)

/-- **Completion commutes with restriction to an open**, termwise and compatibly with the
canonical projections: the `n`-th term of the completion of `M|_Y` along `ℐ|_Y` is the
restriction of the `n`-th term of the completion of `M` along `ℐ`. -/
public theorem completion_restrictIso {Y Z : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    ∃ e : ((Stacks.Algebraization.completionFunctor Y (J.comap r)).obj
          (Stacks.Algebraization.restrictCoherentModules r M)).obj.obj (op n) ≅
        (Scheme.Modules.restrictFunctor r).obj
          (((Stacks.Algebraization.completionFunctor Z J).obj M).obj.obj (op n)),
      Stacks.Algebraization.completionProjection Y (J.comap r)
          (Stacks.Algebraization.restrictCoherentModules r M) n ≫ e.hom =
        (Scheme.Modules.restrictFunctor r).map
          (Stacks.Algebraization.completionProjection Z J M n) := by
  have hMq : M.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj).1
  have hinner : Stacks.Algebraization.completionProjection Y (J.comap r)
        (Stacks.Algebraization.restrictCoherentModules r M) n ≫
      eqToHom (Stacks.Algebraization.completionFunctor_obj Y (J.comap r)
        (Stacks.Algebraization.restrictCoherentModules r M) n) =
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (J.comap r) (n + 1)
        (Stacks.Algebraization.restrictCoherentModules r M).obj).ι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => cokernel.π (Stacks.Algebraization.idealPowerMultiple (J.comap r)
            (n + 1) (Stacks.Algebraization.restrictCoherentModules r M).obj).ι ≫ z)
          ((eqToHom_trans
              (Stacks.Algebraization.completionFunctor_obj Y (J.comap r)
                (Stacks.Algebraization.restrictCoherentModules r M) n).symm
              (Stacks.Algebraization.completionFunctor_obj Y (J.comap r)
                (Stacks.Algebraization.restrictCoherentModules r M) n)).trans
            (eqToHom_refl _ _))).trans (Category.comp_id _))
  refine ⟨eqToIso (Stacks.Algebraization.completionFunctor_obj Y (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r M) n) ≪≫
    Stacks.Algebraization.restrictIdealPowerQuotientIso r J (n + 1) M.obj ≪≫
    (Scheme.Modules.restrictFunctor r).mapIso
      (eqToIso (Stacks.Algebraization.completionFunctor_obj Z J M n)).symm, ?_⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫
      ((Stacks.Algebraization.restrictIdealPowerQuotientIso r J (n + 1) M.obj).hom ≫
        (Scheme.Modules.restrictFunctor r).map
          (eqToHom (Stacks.Algebraization.completionFunctor_obj Z J M n).symm)))
    hinner).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor r).map
      (eqToHom (Stacks.Algebraization.completionFunctor_obj Z J M n).symm))
    (Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso r J (n + 1)
      M.obj)).trans ?_
  exact ((Scheme.Modules.restrictFunctor r).map_comp _ _).symm

/-- **Completion respects an isomorphism of coherent modules**, termwise and compatibly with the
canonical projections. -/
public theorem completion_iso {Y : Scheme.{u}} [IsLocallyNoetherian Y] (J : Y.IdealSheafData)
    (M N : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (e : M.obj ≅ N.obj)
    (n : ℕ) :
    ∃ a : ((Stacks.Algebraization.completionFunctor Y J).obj M).obj.obj (op n) ≅
        ((Stacks.Algebraization.completionFunctor Y J).obj N).obj.obj (op n),
      Stacks.Algebraization.completionProjection Y J M n ≫ a.hom =
        e.hom ≫ Stacks.Algebraization.completionProjection Y J N n :=
  ⟨((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso
      ((Stacks.Algebraization.completionFunctor Y J).mapIso
        (ObjectProperty.isoMk _ e))).app (op n),
    Stacks.Algebraization.completionFunctor_map_quotient Y J
      (ObjectProperty.isoMk _ e).hom n⟩

/-- **The completion of the stabilized kernel image commutes with restriction**, compatibly with
both the inclusion into the term of `F` and the canonical projection onto the adic quotient. -/
public theorem stableKernelImageCompletion_restrictIso {Y Z : Scheme.{u}} [IsNoetherian Y]
    [IsNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    {H K : CoherentAdicSystems J} (α : H ⟶ K) (n m : ℕ) :
    ∃ (s : (Scheme.Modules.restrictFunctor r).obj (stableKernelImage J α m) ≅
        stableKernelImage (J.comap r) ((restrictFunctor J r).map α) m)
      (e : (Scheme.Modules.restrictFunctor r).obj
          ((stableKernelImageCompletion J α m).obj.obj (op n)) ≅
        (stableKernelImageCompletion (J.comap r) ((restrictFunctor J r).map α) m).obj.obj
          (op n)),
      s.hom ≫ stableKernelImageIncl (J.comap r) ((restrictFunctor J r).map α) m =
          (Scheme.Modules.restrictFunctor r).map (stableKernelImageIncl J α m) ∧
        (Scheme.Modules.restrictFunctor r).map
            (Stacks.Algebraization.completionProjection Z J
              (coherentStableKernelImage J α m) n) ≫ e.hom =
          s.hom ≫ Stacks.Algebraization.completionProjection Y (J.comap r)
            (coherentStableKernelImage (J.comap r) ((restrictFunctor J r).map α) m) n := by
  obtain ⟨s, hs⟩ := stableKernelImage_restrictIso r J α m
  obtain ⟨a, ha⟩ := completion_restrictIso r J (coherentStableKernelImage J α m) n
  obtain ⟨b, hb⟩ := completion_iso (J.comap r)
    (Stacks.Algebraization.restrictCoherentModules r (coherentStableKernelImage J α m))
    (coherentStableKernelImage (J.comap r) ((restrictFunctor J r).map α) m) s n
  refine ⟨s, a.symm ≪≫ b, hs, ?_⟩
  refine (congrArg (fun z => (Scheme.Modules.restrictFunctor r).map
      (Stacks.Algebraization.completionProjection Z J
        (coherentStableKernelImage J α m) n) ≫ z) (Iso.trans_hom a.symm b)).trans ?_
  refine (congrArg (fun z => z ≫ (a.inv ≫ b.hom)) ha.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r
        (coherentStableKernelImage J α m)) n ≫ z) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r
        (coherentStableKernelImage J α m)) n ≫ (z ≫ b.hom)) a.hom_inv_id).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r
        (coherentStableKernelImage J α m)) n ≫ z) (Category.id_comp b.hom)).trans hb

/-- **The comparison with the restricted completions transports invertibility of the canonical
transitions.** If the transition of the completed stable kernel images of the restricted system
is an isomorphism, so is the restriction of the transition of the original system.

The two are conjugate: the identifications of
`Stacks.Coherent.stableKernelImageCompletion_restrictIso` commute with the transitions, which is
checked after the projections out of the stable kernel images — epimorphisms, preserved by
restriction — and, for the stable kernel images themselves, before their inclusions into the
terms of `F`, which are monomorphisms. -/
public theorem stableKernelImageCompletion_restrictMap_isIso {Y Z : Scheme.{u}} [IsNoetherian Y]
    [IsNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    {H K : CoherentAdicSystems J} (α : H ⟶ K) (n m l : ℕ) (hml : m ≤ l)
    (h : IsIso ((stableKernelImageCompletion_project (J.comap r) ((restrictFunctor J r).map α)
      m l hml).hom.app (op n))) :
    IsIso ((Scheme.Modules.restrictFunctor r).map
      ((stableKernelImageCompletion_project J α m l hml).hom.app (op n))) := by
  let T := Scheme.Modules.restrictFunctor r
  let α' := (restrictFunctor J r).map α
  let j := stableKernelImage_project J α m l hml
  let j' := stableKernelImage_project (J.comap r) α' m l hml
  let g := (stableKernelImageCompletion_project J α m l hml).hom.app (op n)
  let g' := (stableKernelImageCompletion_project (J.comap r) α' m l hml).hom.app (op n)
  obtain ⟨sl, el, hsl, hel⟩ := stableKernelImageCompletion_restrictIso r J α n l
  obtain ⟨sm, em, hsm, hem⟩ := stableKernelImageCompletion_restrictIso r J α n m
  have hj : T.map j ≫ sm.hom = sl.hom ≫ j' := by
    have hmono : Mono (stableKernelImageIncl (J.comap r) α' m) :=
      mono_stableKernelImageIncl (J.comap r) α' m
    refine (cancel_mono (stableKernelImageIncl (J.comap r) α' m)).mp ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => T.map j ≫ z) hsm).trans ?_
    refine (T.map_comp j (stableKernelImageIncl J α m)).symm.trans ?_
    refine (congrArg T.map (stableKernelImage_project_comp J α m l hml)).trans ?_
    refine (T.map_comp _ _).trans ?_
    refine (congrArg (fun z => z ≫ T.map (H.obj.map (homOfLE hml).op)) hsl.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => sl.hom ≫ z)
      (stableKernelImage_project_comp (J.comap r) α' m l hml).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  have hpe : T.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction r)
  have hql : Epi (C := Z.Modules) (Stacks.Algebraization.completionProjection Z J
      (coherentStableKernelImage J α l) n) := by
    have h1 : Epi (cokernel.π (C := Z.Modules) (Stacks.Algebraization.idealPowerMultiple J (n + 1)
        (coherentStableKernelImage J α l).obj).ι) :=
      Stacks.Algebraization.epi_cokernel_π_submodule_ι _
    have h2 : Epi (C := Z.Modules) (eqToHom (Stacks.Algebraization.completionFunctor_obj Z J
        (coherentStableKernelImage J α l) n).symm) := inferInstance
    exact epi_comp' h1 h2
  have hTql : Epi (T.map (Stacks.Algebraization.completionProjection Z J
      (coherentStableKernelImage J α l) n)) := hpe.preserves _
  have hg : T.map g ≫ em.hom = el.hom ≫ g' := by
    refine (cancel_epi (T.map (Stacks.Algebraization.completionProjection Z J
      (coherentStableKernelImage J α l) n))).mp ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ em.hom)
      (T.map_comp (Stacks.Algebraization.completionProjection Z J
        (coherentStableKernelImage J α l) n) g).symm).trans ?_
    refine (congrArg (fun z => T.map z ≫ em.hom)
      (stableKernelImageCompletion_project_projection J α m l hml n)).trans ?_
    refine (congrArg (fun z => z ≫ em.hom) (T.map_comp j
      (Stacks.Algebraization.completionProjection Z J
        (coherentStableKernelImage J α m) n))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => T.map j ≫ z) hem).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ Stacks.Algebraization.completionProjection Y (J.comap r)
      (coherentStableKernelImage (J.comap r) α' m) n) hj).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => sl.hom ≫ z)
      (stableKernelImageCompletion_project_projection (J.comap r) α' m l hml n).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ g') hel.symm).trans ?_
    exact Category.assoc _ _ _
  have heq : T.map g = el.hom ≫ (g' ≫ em.inv) :=
    (Category.comp_id (T.map g)).symm.trans
      ((congrArg (fun z => T.map g ≫ z) em.hom_inv_id.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ em.inv) hg).trans (Category.assoc _ _ _))))
  have hg' : IsIso g' := h
  have hiso : IsIso (el.hom ≫ (g' ≫ em.inv)) := inferInstance
  exact Eq.mpr (congrArg (fun z => IsIso z) heq) hiso

/-- **The second stabilization on an affine spectrum.** On `Spec R` with `R` Noetherian, there is
a constant `c` such that every transition of the completed stable kernel images at quotient level
`n` above image level `n + c` is an isomorphism: by
`Stacks.Coherent.affineStableKernelImageQuotientMap_bijective` it is bijective on global
sections, and a morphism of quasi-coherent modules on a spectrum which is bijective on global
sections is an isomorphism. -/
public theorem specStableKernelImageQuotientMap_isIso (R : CommRingCat.{u}) [IsNoetherianRing R]
    (J : (Spec R).IdealSheafData) {H K : CoherentAdicSystems J} (α : H ⟶ K) (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso ((stableKernelImageCompletion_project J α m l hml).hom.app (op n)) := by
  have hring : IsNoetherianRing Γ(Spec R, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
  obtain ⟨J, rfl⟩ := (Scheme.IdealSheafData.equivOfIsAffine (X := Spec R)).symm.surjective J
  obtain ⟨c, hc⟩ := affineStableKernelImageQuotientMap_bijective (Spec R) J α n
  refine ⟨c, fun m hm l hml => ?_⟩
  show IsIso ((stableKernelImageCompletion_project (Scheme.IdealSheafData.ofIdealTop J)
    α m l hml).hom.app (op n))
  have hcoh : ∀ k : ℕ, ((stableKernelImageCompletion (Scheme.IdealSheafData.ofIdealTop J)
      α k).obj.obj (op n)).IsCoherent := fun k =>
    (stableKernelImageCompletion (Scheme.IdealSheafData.ofIdealTop J) α k).property.isCoherent n
  have hqc : ∀ k : ℕ, ((stableKernelImageCompletion (Scheme.IdealSheafData.ofIdealTop J)
      α k).obj.obj (op n)).IsQuasicoherent := fun k =>
    have := hcoh k
    isQuasicoherent_of_isCoherent _
  have := hqc l
  have := hqc m
  exact isIso_of_bijective_evaluation_top _ (hc m hm l hml)

/-- **The second stabilization of Tag 087X.** For a morphism `α : F ⟶ G` of coherent adic systems
on a Noetherian scheme and a quotient level `n`, there is a constant `c` such that every
transition of the slice diagram `Stacks.Coherent.stableKernelImageQuotientDiagram` at `n` between
image levels above `n + c` is an isomorphism. Together with
`Stacks.Coherent.stableKernelImageQuotientDiagram_eventuallyConstant` this makes the slice
diagram eventually constant, so the limit system has the stable kernel images' adic quotients as
its terms.

Being an isomorphism is local, and a Noetherian scheme has a finite cover by Noetherian affine
spectra, on each of which
`Stacks.Coherent.specStableKernelImageQuotientMap_isIso` supplies a local constant; the maximum
of those finitely many constants works globally. -/
public theorem stableKernelImageQuotientMap_eventually_isIso (α : F ⟶ G) (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso ((stableKernelImageQuotientDiagram I α n).map (homOfLE hml).op) := by
  classical
  let V := X.affineCover.finiteSubcover
  have hlocal : ∀ i : V.I₀, ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso ((Scheme.Modules.restrictFunctor (V.f i)).map
        ((stableKernelImageCompletion_project I α m l hml).hom.app (op n))) := by
    intro i
    let A : CommRingCat.{u} := X.affineOpenCover.X (X.affineCover.idx i.val)
    have hoi : IsOpenImmersion (show Spec A ⟶ X from V.f i) := V.map_prop i
    have hA : IsNoetherianRing A :=
      isLocallyNoetherian_Spec.mp (show IsLocallyNoetherian (V.X i) from inferInstance)
    have hoiV : IsOpenImmersion (V.f i) := V.map_prop i
    have hN : IsNoetherian (show Scheme.{u} from Spec A) := inferInstance
    have hNV : IsNoetherian (V.X i) := hN
    obtain ⟨c, hc⟩ := specStableKernelImageQuotientMap_isIso A (I.comap (V.f i))
      ((restrictFunctor I (V.f i)).map α) n
    exact ⟨c, fun m hm l hml =>
      stableKernelImageCompletion_restrictMap_isIso (V.f i) I α n m l hml (hc m hm l hml)⟩
  choose c hc using hlocal
  let d := Finset.univ.sup c
  refine ⟨d, fun m hm l hml => ?_⟩
  have key : IsIso ((stableKernelImageCompletion_project I α m l hml).hom.app (op n)) :=
    isIso_of_isIso_restrictFunctor_map V _ fun i =>
      hc i m (by have := Finset.le_sup (f := c) (Finset.mem_univ i); omega) l hml
  exact Eq.mpr (congrArg (fun z => IsIso z)
    (stableKernelImageQuotientDiagram_map I α n m l hml)) key

end Stacks.Coherent

end
