module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex

/-!
# Left exactness of the internal Hom in its first variable, on a ringed site

Stacks 03EN asserts that `𝓗om_𝒪(-, 𝒢)` is left exact.  This file proves the half of it that a
presentation consumes: if `𝓕` is the cokernel of `a : 𝓠 ⟶ 𝓟`, then

  `𝓗om_𝒪(𝓕, 𝒢) ⟶ 𝓗om_𝒪(𝓟, 𝒢) ⟶ 𝓗om_𝒪(𝓠, 𝒢)`

exhibits `𝓗om_𝒪(𝓕, 𝒢)` as the kernel of the dual of `a`.

The statement is made for `AlgebraicGeometry.RingedSite.internalHomSheaf` on an arbitrary
`AlgebraicGeometry.RingedSite`, with the universes of the site objects, the site morphisms, the
sections of the structure sheaf and the sections of the modules all independent.  That is what
the small étale ringed site of a scheme needs: it is a `RingedSite.{u + 1, u, u}`, so the
internal Hom of two `SheafOfModules.{u}` lands in `SheafOfModules.{u + 1}`, and the only form of
03EN the library had — `Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel` in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable` — is stated over
a ring sheaf `Sheaf J CommRingCat.{max u v}` on a site `C : Type u` with `Category.{v} C`, which
there would demand a `CommRingCat.{u + 1}`-valued structure sheaf.  Nothing here constrains the
universes against each other.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomSectionsEquiv`: the sections of the internal Hom over
  an object are the morphisms of modules on the slice there, and
  `AlgebraicGeometry.RingedSite.internalHomSectionsEquiv_internalHomPre`: the first-variable
  action is precomposition on them.
* `AlgebraicGeometry.RingedSite.internalHomPre_comp_internalHomPre`: the dual of `a` kills the
  dual of `b`, when `a ≫ b = 0`.
* `AlgebraicGeometry.RingedSite.isIso_kernelLift_internalHomPre`: **the comparison of
  `𝓗om_𝒪(𝓕, 𝒢)` with the kernel of the dual of `a` is an isomorphism.**
* `AlgebraicGeometry.RingedSite.isLimit_kernelFork_internalHomPre`: **Stacks 03EN, the cokernel
  half** — the dual of `b` is a kernel of the dual of `a`.

## Implementation notes

The whole proof is one observation about sections, and both halves of it are definitional.  The
sections of `internalHomSheaf Z A G` over an object `V` *are* the morphisms
`(A.over V).val ⟶ (G.over V).val` of presheaves of modules on the slice at `V` —
`internalHomSectionsEquiv` is full faithfulness of `CategoryTheory.SheafOfModules.forget` and
nothing else — and `AlgebraicGeometry.RingedSite.internalHomPre` acts on them by precomposition,
on the nose (`AlgebraicGeometry.RingedSite.internalHomPre_val_app`, proved by `rfl`).  So the
sections of `𝓗om_𝒪(𝓕, 𝒢)` over `V` are the morphisms out of `𝓕.over V`, which the universal
property of a cokernel identifies with the morphisms out of `𝓟.over V` killed by `a.over V` —
and that is the submodule of sections of the kernel.  The comparison is therefore bijective on
the sections over every object, hence an isomorphism of presheaves of modules, hence an
isomorphism of sheaves of modules by full faithfulness again.

**That `𝓕.over V` is a cokernel of `a.over V` is a hypothesis, `hb`, not derived here.** It says
that restriction to a slice carries the presentation, which is true because restriction is a left
adjoint, but the library's statement of that,
`Stacks.SheafOfModules.overFunctor_preservesColimits`, is available only for a module universe of
the form `max u v w t` — it needs sheafification of `AddCommGrpCat`-valued presheaves on the
slice, whose objects live in `max u v`. On the small étale site of a scheme the module universe
is `u` while `max u v` is `u + 1`, so that statement does not apply there and the preservation
comes instead from essential smallness of the site.  Taking the restricted presentation as the
hypothesis keeps this file free of that question;
`AlgebraicGeometry.RingedSite.isColimitCokernelCoforkOver` discharges it from
`CategoryTheory.Limits.PreservesColimit` whenever that is available.

`CategoryTheory.Limits.HasKernel` of the dual of `a` is likewise a hypothesis: whether the
category of modules at the larger universe has kernels is a sheafification question about the
ambient site which this statement does not need to settle.

Monomorphisms of sheaves of modules are injective on sections here by
`AlgebraicGeometry.RingedSite.injective_val_app_of_mono`, proved through
`CategoryTheory.SheafOfModules.evaluation`; the library's two existing statements of that fact,
`Stacks.SheafOfModules.injective_val_app_of_mono_evaluation` and
`Stacks.SheafOfModules.injective_app_kernel_ι`, both tie the module universe to the universe of
the sections of the structure sheaf and so do not apply.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe m t u v w

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, v, w})

/-! ### The sections of the internal Hom, and the first-variable action on them -/

/-- **The sections of the internal Hom over an object are the morphisms of modules on the slice
there.**  This is full faithfulness of `CategoryTheory.SheafOfModules.forget` on the slice at
`V`; the two sides are the same type, and the equivalence only names which API a term belongs
to. -/
public noncomputable def internalHomSectionsEquiv
    (A G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (V : Z.Cᵒᵖ) :
    ((internalHomSheaf Z A G).val.obj V) ≃ (A.over V.unop ⟶ G.over V.unop) :=
  ((SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V.unop)).homEquiv
    (X := A.over V.unop) (Y := G.over V.unop)).symm

/-- Forgetting the module structure of the morphism `internalHomSectionsEquiv Z A G V x` gives
back the section `x`. -/
@[simp]
public theorem forget_map_internalHomSectionsEquiv
    (A G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (V : Z.Cᵒᵖ) (x : (internalHomSheaf Z A G).val.obj V) :
    (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V.unop)).map
        (internalHomSectionsEquiv Z A G V x) = x :=
  (SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V.unop)).map_preimage _

/-- `internalHomSectionsEquiv` sends the zero section to the zero morphism. -/
@[simp]
public theorem internalHomSectionsEquiv_zero
    (A G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (V : Z.Cᵒᵖ) : internalHomSectionsEquiv Z A G V 0 = 0 := by
  apply
    (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V.unop)).map_injective
  rw [forget_map_internalHomSectionsEquiv, Functor.map_zero]
  rfl

/-- **The first-variable action of the internal Hom is precomposition on sections**, on the
nose. -/
public theorem internalHomPre_val_app
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
    (G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (f : A ⟶ B) (V : Z.Cᵒᵖ)
    (g : (internalHomSheaf Z B G).val.obj V) :
    ((internalHomPre Z f).val.app V g : (A.over V.unop).val ⟶ (G.over V.unop).val)
      = (SheafOfModules.Hom.over f V.unop).val ≫ g :=
  rfl

/-- The first-variable action, read through `internalHomSectionsEquiv`: it is precomposition
with the restriction of `f` to the slice. -/
public theorem internalHomSectionsEquiv_internalHomPre
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
      (G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (f : A ⟶ B)
    (V : Z.Cᵒᵖ) (g : (internalHomSheaf Z B G).val.obj V) :
    internalHomSectionsEquiv Z A G V ((internalHomPre Z f).val.app V g)
      = SheafOfModules.Hom.over f V.unop ≫ internalHomSectionsEquiv Z B G V g := by
  apply
    (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V.unop)).map_injective
  rw [Functor.map_comp, forget_map_internalHomSectionsEquiv,
    forget_map_internalHomSectionsEquiv]
  exact internalHomPre_val_app Z G f V g

/-- A section is killed by the first-variable action of `f` iff its morphism on the slice is
killed by the restriction of `f`. -/
private theorem internalHomPre_val_app_eq_zero_iff
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
    (G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (f : A ⟶ B)
    (V : Z.Cᵒᵖ) (x : (internalHomSheaf Z B G).val.obj V) :
    (internalHomPre Z f).val.app V x = 0 ↔
      SheafOfModules.Hom.over f V.unop ≫ internalHomSectionsEquiv Z B G V x = 0 := by
  rw [← (internalHomSectionsEquiv Z A G V).apply_eq_iff_eq,
    internalHomSectionsEquiv_internalHomPre, internalHomSectionsEquiv_zero]

/-- A monomorphism of sheaves of modules is injective on the sections over every object:
evaluation at an object preserves limits, hence monomorphisms, and a monomorphism of modules is
an injective map.  Stated with the module universe free of the universe of the sections of the
sheaf of rings, which is what the internal Hom needs. -/
public theorem injective_val_app_of_mono
    {N₁ N₂ : SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
    (φ : N₁ ⟶ N₂) [Mono φ] (V : Z.Cᵒᵖ) : Function.Injective (φ.val.app V) := by
  have :
    (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact (ModuleCat.mono_iff_injective _).mp
    ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).map_mono φ)

/-! ### The cokernel half of Stacks 03EN -/

section

variable {M P Q : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
  (G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  {a : Q ⟶ P} {b : P ⟶ M}

/-- The restriction of a relation to a slice is still a relation. -/
public theorem over_comp_over_eq_zero (hab : a ≫ b = 0) (V : Z.C) :
    SheafOfModules.Hom.over a V ≫ SheafOfModules.Hom.over b V = 0 := by
  rw [SheafOfModules.Hom.over, SheafOfModules.Hom.over, ← Functor.map_comp, hab]
  simp

/-- Restriction to a slice carries the presentation of `M` to a presentation of `M.over V`,
whenever restriction preserves the colimit in question. -/
public noncomputable def isColimitCokernelCoforkOver (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) (V : Z.C)
    [PreservesColimit (parallelPair a 0) (SheafOfModules.overFunctor.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V)] :
    IsColimit (CokernelCofork.ofπ (SheafOfModules.Hom.over b V)
      (over_comp_over_eq_zero Z hab V)) :=
  isColimitCoforkMapOfIsColimit'
    (SheafOfModules.overFunctor.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V) hab hb

/-- **The dual of `a` kills the dual of `b`.**  On sections both are precomposition, so the
composite is precomposition with the restriction of `a ≫ b`, which is zero. -/
public theorem internalHomPre_comp_internalHomPre (hab : a ≫ b = 0) :
    internalHomPre Z b (C := G) ≫ internalHomPre Z a = 0 := by
  have key : ∀ (V : Z.Cᵒᵖ) (g : (internalHomSheaf Z M G).val.obj V),
      (internalHomPre Z a (C := G)).val.app V
        ((internalHomPre Z b (C := G)).val.app V g) = 0 := by
    intro V g
    rw [internalHomPre_val_app_eq_zero_iff Z G a, internalHomSectionsEquiv_internalHomPre,
      ← Category.assoc, over_comp_over_eq_zero Z hab V.unop, zero_comp]
  apply (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  exact key V g

section Presentation

variable (hab : a ≫ b = 0)
  (hb : ∀ V : Z.C, IsColimit (CokernelCofork.ofπ (SheafOfModules.Hom.over b V)
    (over_comp_over_eq_zero Z hab V)))

include hb in
/-- **The dual of `b` is injective on the sections over every object**: the sections of the
internal Hom are the morphisms on the slice, where it is precomposition with the projection of a
cokernel. -/
public theorem injective_internalHomPre_val_app (V : Z.Cᵒᵖ) :
    Function.Injective ((internalHomPre Z b (C := G)).val.app V) := by
  intro g₁ g₂ hg
  apply (internalHomSectionsEquiv Z M G V).injective
  refine Cofork.IsColimit.hom_ext (hb V.unop) ?_
  rw [show (CokernelCofork.ofπ (SheafOfModules.Hom.over b V.unop)
      (over_comp_over_eq_zero Z hab V.unop)).π = SheafOfModules.Hom.over b V.unop from rfl,
    ← internalHomSectionsEquiv_internalHomPre Z G b V g₁,
    ← internalHomSectionsEquiv_internalHomPre Z G b V g₂, hg]

include hb in
/-- **A section of `𝓗om_𝒪(𝓟, 𝒢)` killed by the dual of `a` comes from a section of
`𝓗om_𝒪(𝓕, 𝒢)`**: it is a morphism out of `𝓟.over V` killed by the relation, so it factors
through the cokernel. -/
public theorem exists_internalHomPre_val_app_eq (V : Z.Cᵒᵖ)
    (x : (internalHomSheaf Z P G).val.obj V)
    (hx : (internalHomPre Z a (C := G)).val.app V x = 0) :
    ∃ g, (internalHomPre Z b (C := G)).val.app V g = x := by
  obtain ⟨g, hg⟩ := Cofork.IsColimit.desc' (hb V.unop) (internalHomSectionsEquiv Z P G V x)
    (((internalHomPre_val_app_eq_zero_iff Z G a V x).mp hx).trans zero_comp.symm)
  refine ⟨(internalHomSectionsEquiv Z M G V).symm g, ?_⟩
  apply (internalHomSectionsEquiv Z P G V).injective
  rw [internalHomSectionsEquiv_internalHomPre, Equiv.apply_symm_apply]
  exact hg

variable [HasKernel (internalHomPre Z a (C := G))]

include hb in
/-- **The comparison of `𝓗om_𝒪(𝓕, 𝒢)` with the kernel of the dual of `a` is an isomorphism.**
Over every object it is the bijection between the morphisms out of a cokernel and the morphisms
out of its source killed by the relation. -/
public theorem isIso_kernelLift_internalHomPre :
    IsIso (kernel.lift (internalHomPre Z a (C := G)) (internalHomPre Z b)
      (internalHomPre_comp_internalHomPre Z G hab)) := by
  set φ := kernel.lift (internalHomPre Z a (C := G)) (internalHomPre Z b)
    (internalHomPre_comp_internalHomPre Z G hab) with hφ
  have hfac : φ ≫ kernel.ι (internalHomPre Z a (C := G)) = internalHomPre Z b := by
    rw [hφ]; exact kernel.lift_ι _ _ _
  have hcomp : ∀ (V : Z.Cᵒᵖ) (x : (internalHomSheaf Z M G).val.obj V),
      (kernel.ι (internalHomPre Z a (C := G))).val.app V (φ.val.app V x)
        = (internalHomPre Z b (C := G)).val.app V x := by
    intro V x
    rw [← hfac]
    rfl
  have hbij : ∀ V : Z.Cᵒᵖ, IsIso (φ.val.app V) := by
    intro V
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
    · intro x y hxy
      refine injective_internalHomPre_val_app Z G hab hb V ?_
      rw [← hcomp V x, ← hcomp V y, hxy]
    · intro y
      have hx : (internalHomPre Z a (C := G)).val.app V
          ((kernel.ι (internalHomPre Z a (C := G))).val.app V y) = 0 := by
        have hk := congrArg
          (fun ψ : kernel (internalHomPre Z a (C := G)) ⟶ internalHomSheaf Z Q G =>
            ψ.val.app V y) (kernel.condition (internalHomPre Z a (C := G)))
        exact hk
      obtain ⟨g, hg⟩ := exists_internalHomPre_val_app_eq Z G hab hb V _ hx
      refine ⟨g, injective_val_app_of_mono Z (kernel.ι (internalHomPre Z a (C := G))) V ?_⟩
      rw [hcomp V g]
      exact hg
  have hval : IsIso
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map φ) := by
    let e := PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ (φ.val.app V) (hbij V))
      (fun {V W} s => φ.val.naturality s)
    have hiso : e.hom = φ.val := by
      apply PresheafOfModules.hom_ext
      intro V
      rfl
    rw
      [show (SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map φ = φ.val from rfl, ← hiso]
    exact Iso.isIso_hom e
  exact
    (SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).isIso_of_isIso_map φ

include hb in
/-- **Stacks 03EN, the cokernel half.**  If `𝓕` is the cokernel of `a : 𝓠 ⟶ 𝓟`, then
`𝓗om_𝒪(𝓕, 𝒢)` is the kernel of the dual `𝓗om_𝒪(𝓟, 𝒢) ⟶ 𝓗om_𝒪(𝓠, 𝒢)` of `a`. -/
public noncomputable def isLimit_kernelFork_internalHomPre :
    IsLimit (KernelFork.ofι (internalHomPre Z b (C := G))
      (internalHomPre_comp_internalHomPre Z G hab)) := by
  haveI := isIso_kernelLift_internalHomPre Z G hab hb
  refine IsLimit.ofIsoLimit (kernelIsKernel (internalHomPre Z a (C := G)))
    (Fork.ext (asIso (kernel.lift (internalHomPre Z a (C := G)) (internalHomPre Z b)
      (internalHomPre_comp_internalHomPre Z G hab))).symm ?_)
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact (kernel.lift_ι _ _ _).symm

end Presentation

end

end AlgebraicGeometry.RingedSite

end
