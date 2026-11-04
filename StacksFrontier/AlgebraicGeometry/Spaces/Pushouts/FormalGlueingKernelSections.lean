module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional

/-!
# Sections of the module of Stacks 0AEX over an étale chart

In the formal glueing situation of Stacks 0AEV, the functor of Stacks 0AEX sends a glueing triple
`t = (H, G, φ)` to `Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`.  This file computes its sections over an
étale chart `W` of `X`: they are the fibre product of the sections of `j_*H` and of `f_*G` over
`W`, over the sections of `(f ∘ j')_*(G|_V)` over `W`, through the two canonical maps of
Stacks 0AEX, and the identification is the pair of the two projections.  When `X` is represented
by an affine scheme `V` and `W` is the identity chart, this is the description of the global
sections of the glueing kernel in terms of the sections of `t.left` over `U` and of `t.right`
over `Y`.

## Main definitions

* `CategoryTheory.Limits.moduleFibreProduct`: the fibre product `{(a, b) | ρ₁ a = ρ₂ b}` of two
  maps of modules, as a submodule of `A × B`.
* `CategoryTheory.Limits.isPullbackFibreProductEquiv`: a pullback square of modules exhibits its
  corner as that fibre product, as a linear equivalence; `isPullbackTypeEquiv` is the same on
  underlying types.
* `AlgebraicGeometry.Space.FormalGlueingSituation.sectionsAt`: sections over an étale chart `W`
  of the value at a glueing triple `t`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelSectionsTypeEquiv`: the sections
  over `W` of the module of Stacks 0AEX at `t` are the fibre product of the sections of `j_*H`
  and of `f_*G` over `W`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_sections`: the module
  of Stacks 0AEX with its two projections is a pullback on sections over every étale chart.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_glueingKernelSectionsEquiv`: the
  identification of the sections with the fibre product is linear over `𝒪_X(W)`, with the two
  projections as its components.
* `glueingKernelFst_sections_naturality` and `glueingKernelSnd_sections_naturality` (in the same
  namespace): the two projections are natural in the glueing triple.

## Implementation notes

The linear form is stated as an existence statement with the formula of the equivalence, and the
type-level form as a definition.  A definition whose type is a linear map or a linear
equivalence of these concrete modules of sections is accepted by the elaborator and then
exhausts the kernel's heartbeat budget; propositions with the same terms, and definitions valued
in plain types, check at once.  The pullback square is obtained from
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel` by evaluation, which
preserves finite limits, so no biproduct or kernel instance of the functor category is
re-synthesized here.

## References

* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

universe v w

variable {R : Type w} [Ring R] {K A B C : ModuleCat.{v} R} {p₁ : K ⟶ A} {p₂ : K ⟶ B}
    {ρ₁ : A ⟶ C} {ρ₂ : B ⟶ C} (h : IsPullback p₁ p₂ ρ₁ ρ₂)

/-- The fibre product submodule `{(a, b) | ρ₁ a = ρ₂ b}` of `A × B`. -/
abbrev moduleFibreProduct (ρ₁ : A ⟶ C) (ρ₂ : B ⟶ C) : Submodule R (A × B) :=
  LinearMap.ker (ρ₁.hom ∘ₗ LinearMap.fst R A B - ρ₂.hom ∘ₗ LinearMap.snd R A B)

/-- Membership in `CategoryTheory.Limits.moduleFibreProduct`. -/
theorem mem_moduleFibreProduct_iff (z : A × B) :
    z ∈ moduleFibreProduct ρ₁ ρ₂ ↔ ρ₁.hom z.1 = ρ₂.hom z.2 := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- The two projections of a pullback square of modules, as a linear map into the fibre
product `CategoryTheory.Limits.moduleFibreProduct`. -/
def isPullbackFibreProductMap : K →ₗ[R] moduleFibreProduct ρ₁ ρ₂ :=
  LinearMap.codRestrict _ (LinearMap.prod p₁.hom p₂.hom) fun x => by
    rw [mem_moduleFibreProduct_iff]
    exact congrArg (fun q => q.hom x) h.w

/-- The first component of `isPullbackFibreProductMap h x` is `p₁ x`. -/
@[simp]
theorem isPullbackFibreProductMap_apply_fst (x : K) :
    (isPullbackFibreProductMap h x).1.1 = p₁.hom x :=
  rfl

/-- The second component of `isPullbackFibreProductMap h x` is `p₂ x`. -/
@[simp]
theorem isPullbackFibreProductMap_apply_snd (x : K) :
    (isPullbackFibreProductMap h x).1.2 = p₂.hom x :=
  rfl

/-- The two projections of a pullback square of modules are jointly a bijection onto the fibre
product. -/
theorem isPullbackFibreProductMap_bijective : Function.Bijective (isPullbackFibreProductMap h) := by
  have hT := h.map (CategoryTheory.forget (ModuleCat.{v} R))
  refine ⟨fun x y hxy => Types.ext_of_isPullback hT ?_ ?_, fun ⟨⟨a, b⟩, hab⟩ => ?_⟩
  · exact congrArg (fun z => z.1.1) hxy
  · exact congrArg (fun z => z.1.2) hxy
  · obtain ⟨x, hx1, hx2⟩ := Types.exists_of_isPullback hT a b
      ((mem_moduleFibreProduct_iff _).1 hab)
    exact ⟨x, Subtype.ext (Prod.ext hx1 hx2)⟩

/-- **A pullback of modules is the fibre product.**  For a pullback square `p₁, p₂, ρ₁, ρ₂` in
`ModuleCat R`, the corner `K` is `{(a, b) ∈ A × B | ρ₁ a = ρ₂ b}` through the two projections. -/
noncomputable def isPullbackFibreProductEquiv : K ≃ₗ[R] moduleFibreProduct ρ₁ ρ₂ :=
  LinearEquiv.ofBijective _ (isPullbackFibreProductMap_bijective h)

/-- `isPullbackFibreProductEquiv h` agrees with `isPullbackFibreProductMap h`. -/
@[simp]
theorem isPullbackFibreProductEquiv_apply (x : K) :
    isPullbackFibreProductEquiv h x = isPullbackFibreProductMap h x :=
  rfl

/-- The fibre product `{(a, b) | ρ₁ a = ρ₂ b}` of the underlying types. -/
def typeFibreProduct (ρ₁ : A ⟶ C) (ρ₂ : B ⟶ C) : Type v :=
  {z : A × B // ρ₁.hom z.1 = ρ₂.hom z.2}

/-- A pullback square of modules exhibits its corner as the fibre product of underlying types. -/
noncomputable def isPullbackTypeEquiv : K ≃ typeFibreProduct ρ₁ ρ₂ :=
  Equiv.ofBijective (fun x => ⟨(p₁.hom x, p₂.hom x), congrArg (fun q => q.hom x) h.w⟩) (by
    have hT := h.map (CategoryTheory.forget (ModuleCat.{v} R))
    refine ⟨fun x y hxy => Types.ext_of_isPullback hT ?_ ?_, fun ⟨⟨a, b⟩, hab⟩ => ?_⟩
    · exact congrArg (fun z => z.1.1) hxy
    · exact congrArg (fun z => z.1.2) hxy
    · obtain ⟨x, hx1, hx2⟩ := Types.exists_of_isPullback hT a b hab
      exact ⟨x, Subtype.ext (Prod.ext hx1 hx2)⟩)

/-- `isPullbackTypeEquiv h x` is the pair `(p₁ x, p₂ x)`. -/
@[simp]
theorem isPullbackTypeEquiv_apply (x : K) :
    (isPullbackTypeEquiv h x).1 = (p₁.hom x, p₂.hom x) :=
  rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- Sections over an étale chart `W` of `X` of the value at a glueing triple `t`, as a functor on
the functors from glueing triples to `𝒪_X`-modules.  Its type is left to be inferred: spelling
the target ring out changes the ring instance of the modules of sections. -/
def sectionsAt (t : D.moduleGlueingComma) (W : SmallEtale B S hS D.spaceX.1) :=
  (evaluation D.moduleGlueingComma (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)).obj t ⋙
    SheafOfModules.evaluation.{u} (structureRingSheaf B S hS D.spaceX) (op W)

/-- `sectionsAt t W` preserves finite limits. -/
instance (t : D.moduleGlueingComma) (W : SmallEtale B S hS D.spaceX.1) :
    PreservesFiniteLimits (D.sectionsAt t W) :=
  inferInstanceAs (PreservesFiniteLimits ((evaluation _ _).obj t ⋙
    SheafOfModules.evaluation.{u} (structureRingSheaf B S hS D.spaceX) (op W)))

variable (t : D.moduleGlueingComma) (W : SmallEtale B S hS D.spaceX.1)

/-- The value of `sectionsAt t W` is the module of sections over `W` of the value at `t`. -/
theorem sectionsAt_obj (M : D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.sectionsAt t W).obj M = (M.obj t).val.obj (op W) :=
  rfl

/-- `sectionsAt t W` of a natural transformation is its component at `t` on sections over `W`. -/
theorem sectionsAt_map_apply
    {M N : D.moduleGlueingComma ⥤ Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2} (φ : M ⟶ N)
    (x : (D.sectionsAt t W).obj M) :
    ((D.sectionsAt t W).map φ).hom x = ((φ.app t).val.app (op W)).hom x :=
  rfl

/-- **The module of Stacks 0AEX is a pullback on sections.**  Over every étale chart `W` of `X`,
the sections of the module of Stacks 0AEX at a glueing triple, with its two projections, are the
pullback of the two canonical maps on sections. -/
theorem isPullback_glueingKernel_sections :
    IsPullback ((D.sectionsAt t W).map D.glueingKernelFst)
      ((D.sectionsAt t W).map D.glueingKernelSnd)
      ((D.sectionsAt t W).map D.restrictionOverlapMap)
      ((D.sectionsAt t W).map D.ambientOverlapMap) :=
  D.isPullback_glueingKernel.map _

/-- **The sections of the module of Stacks 0AEX over an étale chart are a fibre product.**  For a
glueing triple `t = (H, G, φ)` and an étale chart `W` of `X`, the sections over `W` of
`Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))` are, linearly over `𝒪_X(W)`, the pairs of a section of
`j_*H` and a section of `f_*G` over `W` with the same image in the sections of
`(f ∘ j')_*(G|_V)`; the identification is the pair of the two projections. -/
theorem exists_glueingKernelSectionsEquiv :
    ∃ e : (D.sectionsAt t W).obj D.glueingKernelDiagram
        ≃ₗ[(structureRingSheaf B S hS D.spaceX).obj.obj (op W)]
      moduleFibreProduct ((D.sectionsAt t W).map D.restrictionOverlapMap)
        ((D.sectionsAt t W).map D.ambientOverlapMap),
      ∀ x, (e x).1 = (((D.sectionsAt t W).map D.glueingKernelFst).hom x,
        ((D.sectionsAt t W).map D.glueingKernelSnd).hom x) :=
  ⟨isPullbackFibreProductEquiv (D.isPullback_glueingKernel_sections t W), fun _ => rfl⟩

/-- The sections over `W` of the module of Stacks 0AEX at `t`, as a type, are the fibre product
of the sections of `j_*H` and of `f_*G` over `W` over the sections of `(f ∘ j')_*(G|_V)`; the
forward map is the pair of the two projections (`CategoryTheory.Limits.isPullbackTypeEquiv_apply`),
and it is linear by `exists_glueingKernelSectionsEquiv`. -/
def glueingKernelSectionsTypeEquiv :=
  isPullbackTypeEquiv (D.isPullback_glueingKernel_sections t W)

/-- The first projection on sections is natural in the glueing triple. -/
theorem glueingKernelFst_sections_naturality {s : D.moduleGlueingComma} (a : t ⟶ s)
    (x : (D.sectionsAt t W).obj D.glueingKernelDiagram) :
    ((D.sectionsAt s W).map D.glueingKernelFst).hom
        (((D.glueingKernelDiagram.map a).val.app (op W)).hom x) =
      ((D.restrictionDirectImage.map a).val.app (op W)).hom
        (((D.sectionsAt t W).map D.glueingKernelFst).hom x) :=
  congrArg (fun q => (q.val.app (op W)).hom x) (D.glueingKernelFst.naturality a)

/-- The second projection on sections is natural in the glueing triple. -/
theorem glueingKernelSnd_sections_naturality {s : D.moduleGlueingComma} (a : t ⟶ s)
    (x : (D.sectionsAt t W).obj D.glueingKernelDiagram) :
    ((D.sectionsAt s W).map D.glueingKernelSnd).hom
        (((D.glueingKernelDiagram.map a).val.app (op W)).hom x) =
      ((D.ambientDirectImage.map a).val.app (op W)).hom
        (((D.sectionsAt t W).map D.glueingKernelSnd).hom x) :=
  congrArg (fun q => (q.val.app (op W)).hom x) (D.glueingKernelSnd.naturality a)

/-- At a glueing triple of the glueing data, the sections of the value of the hypothesis-free
functor of Stacks 0AEX are those of `glueingKernelDiagram` at the underlying triple. -/
theorem glueingKernelFunctor_obj_sections (t : D.moduleGlueingData) :
    ((D.glueingKernelFunctor.obj t).obj.val.obj (op W) : Type u) =
      (D.sectionsAt t.obj W).obj D.glueingKernelDiagram :=
  rfl

end AlgebraicGeometry.Space.FormalGlueingSituation

end
