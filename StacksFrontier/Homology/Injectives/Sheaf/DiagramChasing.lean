module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
import StacksCore.Tactic.StacksAttribute

/-!
# Diagram chasing in the category of abelian sheaves on a site

Diagram chasing in the category `Ab(𝒞)` of abelian sheaves on a site `𝒞`, with coefficients
`AddCommGrpCat.{max u v}` for `𝒞 : Type u` with `Category.{v} 𝒞`, either with sections over
objects or on the level of stalks.

*Sections.* The sections functors `Γ(U, -) : Ab(𝒞) ⥤ Ab`, one for each object `U` of `𝒞`, are
jointly faithful and each is left exact. A morphism of abelian sheaves is a monomorphism exactly
when it is injective on sections over every object, a cone of abelian sheaves is a limit as soon
as it is a limit on sections over every object, and finite limits — in particular kernels — are
computed sectionwise. A morphism is an epimorphism exactly when every section of the target lifts
along the arrows of some covering sieve.

*Stalks.* If `{p_i}` is a conservative family of points, then a short complex of abelian sheaves
is exact if and only if its image under every stalk functor `(-)_{p_i}` is exact.

## Main results

* `Stacks.Injectives.mono_iff_forall_injective_app`: a morphism of abelian sheaves is a
  monomorphism if and only if it is injective on sections over every object.
* `Stacks.Injectives.epi_iff_forall_exists_local_lift`: a morphism of abelian sheaves is an
  epimorphism if and only if every section of the target lifts along the arrows of some
  covering sieve.
* `Stacks.Injectives.preservesFiniteLimits_sheafSections`: finite limits of abelian sheaves are
  computed sectionwise.
* `Stacks.Injectives.isLimit_of_forall_isLimit_sheafSections`: a cone of abelian sheaves which
  is a limit sectionwise is a limit.
* `Stacks.Injectives.exact_iff_forall_sheafFiber_exact`: for a conservative family of points, a
  short complex of abelian sheaves is exact if and only if all of its stalks are exact.
* `Stacks.Injectives.exists_conservativeFamily_exact_iff`: the same statement for a site which
  has a conservative family of points.

## References

* [Stacks Project, Tag 05PP](https://stacks.math.columbia.edu/tag/05PP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### Diagram chasing with sections over objects -/

/-- Finite limits of abelian sheaves are computed sectionwise: taking sections over a fixed
object is left exact. -/
@[stacks 05PP "diagram chasing: sections"]
theorem preservesFiniteLimits_sheafSections (U : Cᵒᵖ) :
    PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{max u v}).obj U) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J _).symm

/-- Taking sections over an object preserves monomorphisms. -/
theorem preservesMonomorphisms_sheafSections (U : Cᵒᵖ) :
    ((sheafSections J AddCommGrpCat.{max u v}).obj U).PreservesMonomorphisms :=
  have := preservesFiniteLimits_sheafSections J U
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

/-- The sections functors of abelian sheaves are jointly faithful: two morphisms of sheaves
which agree on sections over every object are equal. -/
theorem jointlyFaithful_sheafSections :
    JointlyFaithful (fun U : Cᵒᵖ => (sheafSections J AddCommGrpCat.{max u v}).obj U) where
  map_injective h := Sheaf.hom_ext (NatTrans.ext (funext h))

/-- A cone of abelian sheaves which becomes a limit cone after taking sections over every object
is a limit cone. -/
@[stacks 05PP "diagram chasing: sections"]
noncomputable def isLimit_of_forall_isLimit_sheafSections {T : Type*} [Category T]
    {K : T ⥤ Sheaf J AddCommGrpCat.{max u v}} (c : Cone K)
    (h : ∀ U : Cᵒᵖ,
      IsLimit (((sheafSections J AddCommGrpCat.{max u v}).obj U).mapCone c)) :
    IsLimit c :=
  isLimitOfReflects (sheafToPresheaf J _)
    (evaluationJointlyReflectsLimits _ fun U ↦
      (IsLimit.equivIsoLimit (Cone.ext (Iso.refl _) (by simp))) (h U))

/-- A morphism of abelian sheaves is a monomorphism if and only if it is injective on sections
over every object. -/
@[stacks 05PP "diagram chasing: sections"]
theorem mono_iff_forall_injective_app {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    Mono f ↔ ∀ U : Cᵒᵖ, Function.Injective (f.hom.app U) := by
  have := fun U ↦ preservesMonomorphisms_sheafSections J (C := C) U
  rw [(jointlyFaithful_sheafSections J).jointlyReflectMonomorphisms.mono_iff f]
  exact forall_congr' fun U ↦ AddCommGrpCat.mono_iff_injective _

/-- A morphism of abelian sheaves `f : F ⟶ G` is an epimorphism if and only if every section of
`G` over an object `U` lifts along `f` on the arrows of some covering sieve of `U`. -/
@[stacks 05PP "diagram chasing: sections"]
theorem epi_iff_forall_exists_local_lift {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    Epi f ↔ ∀ (U : C) (s : ToType (G.obj.obj (op U))),
      ∃ R : Sieve U, R ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), R g →
        ∃ t : ToType (F.obj.obj (op V)), f.hom.app (op V) t = G.obj.map g.op s := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun hf U s ↦ ⟨Presheaf.imageSieve f.hom s, Presheaf.imageSieve_mem (J := J) f.hom s,
    fun V g hg ↦ hg⟩, fun h ↦ ⟨fun {U} s ↦ ?_⟩⟩
  obtain ⟨R, hR, hlift⟩ := h U s
  exact J.superset_covering (fun V g hg ↦ hlift g hg) hR

/-- Composition of morphisms of abelian sheaves is computed sectionwise. -/
private theorem comp_hom_app_apply {J : GrothendieckTopology C}
    {F G H : Sheaf J AddCommGrpCat.{max u v}} {f : F ⟶ G} {g : G ⟶ H} {k : F ⟶ H}
    (e : f ≫ g = k) (U : Cᵒᵖ) (x : ToType (F.obj.obj U)) :
    g.hom.app U (f.hom.app U x) = k.hom.app U x := by
  simpa using congrArg (fun ψ : F ⟶ H ↦ ψ.hom.app U x) e

/-- A short complex of abelian sheaves is exact as soon as every section of its middle term
annihilated by the second map lifts along the first map on the arrows of some covering sieve. -/
@[stacks 05PP "diagram chasing: sections", sga "4½ Arcata 1.6.3" "partial"]
theorem exact_of_forall_exists_local_lift {S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})}
    (h : ∀ (U : C) (a : ToType (S.X₂.obj.obj (op U))), S.g.hom.app (op U) a = 0 →
      ∃ R : Sieve U, R ∈ J U ∧ ∀ ⦃V : C⦄ (φ : V ⟶ U), R φ →
        ∃ b : ToType (S.X₁.obj.obj (op V)),
          S.f.hom.app (op V) b = S.X₂.obj.map φ.op a) :
    S.Exact := by
  have hinj : ∀ V : Cᵒᵖ, Function.Injective ((kernel.ι S.g).hom.app V) :=
    (mono_iff_forall_injective_app J (kernel.ι S.g)).1 inferInstance
  rw [S.exact_iff_epi_kernel_lift, epi_iff_forall_exists_local_lift]
  intro U t
  have hga : S.g.hom.app (op U) ((kernel.ι S.g).hom.app (op U) t) = 0 :=
    (comp_hom_app_apply (kernel.condition S.g) _ t).trans (by simp)
  obtain ⟨R, hR, hlift⟩ := h U _ hga
  refine ⟨R, hR, fun V φ hφ ↦ ?_⟩
  obtain ⟨b, hb⟩ := hlift φ hφ
  refine ⟨b, hinj (op V) ?_⟩
  have hfac := comp_hom_app_apply (kernel.lift_ι S.g S.f S.zero) (op V) b
  rw [hfac, hb, ← NatTrans.naturality_apply (kernel.ι S.g).hom φ.op t]

/-! ### Diagram chasing on stalks -/

variable {J}

/-- The stalk functor of abelian sheaves at a point is additive. -/
instance sheafFiber_additive (Φ : GrothendieckTopology.Point.{max u v} J) :
    (Φ.sheafFiber (A := AddCommGrpCat.{max u v})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk functor of abelian sheaves at a point preserves homology. -/
instance sheafFiber_preservesHomology (Φ : GrothendieckTopology.Point.{max u v} J) :
    (Φ.sheafFiber (A := AddCommGrpCat.{max u v})).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Let `{p_i}` be a conservative family of points of a site. A short complex of abelian sheaves
is exact if and only if the short complex of stalks at `p_i` is exact for every `i`. -/
@[stacks 05PP "diagram chasing: stalks"]
theorem exact_iff_forall_sheafFiber_exact
    {P : ObjectProperty (GrothendieckTopology.Point.{max u v} J)}
    (hP : P.IsConservativeFamilyOfPoints)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    S.Exact ↔ ∀ Φ : P.FullSubcategory,
      (S.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{max u v}))).Exact := by
  refine ⟨fun h Φ ↦ h.map _, fun h ↦ ?_⟩
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
  refine (hP.jointlyFaithful AddCommGrpCat.{max u v}).map_injective fun Φ ↦ ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1
    ((S.leftHomologyData.exact_map_iff Φ.obj.sheafFiber).1 (h Φ))

/-- On a site which has a conservative family of points
(`CategoryTheory.GrothendieckTopology.HasConservativeFamily`) there is a conservative family of
points on whose stalks the exactness of short complexes of abelian sheaves can be tested. -/
@[stacks 05PP "diagram chasing: stalks"]
theorem exists_conservativeFamily_exact_iff (J : GrothendieckTopology C)
    (h : GrothendieckTopology.HasConservativeFamily.{max u v} J) :
    ∃ P : ObjectProperty (GrothendieckTopology.Point.{max u v} J),
      P.IsConservativeFamilyOfPoints ∧
      ∀ S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}),
        (S.Exact ↔ ∀ Φ : P.FullSubcategory,
          (S.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{max u v}))).Exact) := by
  obtain ⟨P, hP⟩ := (GrothendieckTopology.hasConservativeFamily_iff_exists J).1 h
  exact ⟨P, hP, fun S ↦ exact_iff_forall_sheafFiber_exact hP S⟩

end Stacks.Injectives
