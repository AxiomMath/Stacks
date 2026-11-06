module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Colimits
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Biproducts
public import StacksFrontier.Algebra.Module.Adequate.Colimit
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import StacksCore.Tactic.StacksAttribute

/-!
# The adequate functors are a coreflective subcategory

The inclusion `i` of the adequate module-valued functors on the commutative `A`-algebras into all
module-valued functors is fully faithful and exact, and it has a right adjoint `Q`: the
construction of [Stacks, Tag 06Z6]. Being a right adjoint, `Q` is left exact, and since `i` is
exact, `Q` carries injective objects to injective objects.

The right adjoint is obtained from the special adjoint functor theorem rather than from the
colimit of the source's construction. Its hypotheses are exactly the two facts about adequate
functors that the source uses: they are closed under arbitrary colimits ([Stacks, Tag 06V4]), and
every adequate functor is a quotient of a direct sum of linearly adequate functors
([Stacks, Tag 06UX]), so that the linearly adequate functors form a small separating family.

## Main definitions

* `AdequateFunctor.LinearPresentation` — the index type of the small family of linearly adequate
  functors, a map of finite free `A`-modules together with its two ranks.
* `AdequateFunctor.adequateCoreflection` — the functor `Q` of [Stacks, Tag 06Z6].

## Main results

* `AdequateFunctor.fullyFaithful_adequateInclusion`,
  `AdequateFunctor.preservesFiniteLimits_adequateInclusion` and
  `AdequateFunctor.preservesFiniteColimits_adequateInclusion` — `i` is fully faithful and exact,
  two of the three assertions of part (1) of [Stacks, Tag 06Z7].
* `AdequateFunctor.adequate_isWeakSerreClass_of_isClosedUnderExtensions` — the third assertion of
  part (1) of [Stacks, Tag 06Z7], reduced to closure under extensions.
* `AdequateFunctor.isSeparating_adequateOfLinearPresentation` — the linearly adequate functors
  form a separating family for the adequate functors.
* `AdequateFunctor.exists_adequate_homEquiv` — [Stacks, Tag 06Z6]: every module-valued functor
  `F` admits a morphism from an adequate functor through which every morphism from an adequate
  functor factors uniquely.
* `AdequateFunctor.adequateCoreflectionAdjunction` and
  `AdequateFunctor.preservesFiniteLimits_adequateCoreflection` — part (3) of
  [Stacks, Tag 06Z7]: `Q` is a right adjoint to `i`, hence left exact.
* `AdequateFunctor.preservesInjectiveObjects_adequateCoreflection` — part (4) of
  [Stacks, Tag 06Z7]: `Q` transforms injectives into injectives.

## Implementation notes

The third assertion of part (1) of [Stacks, Tag 06Z7], that the image of `i` is a weak Serre
subcategory, is reduced here to closure under extensions, which is [Stacks, Tag 06V8]: by
`CategoryTheory.ObjectProperty.IsWeakSerreClass` the other closure conditions are already
available. The unconditional statement is `AdequateFunctor.adequate_isWeakSerreClass`, at the
universes in which `AdequateFunctor.isAdequate_of_shortExact` is available; the reduction holds
at the universes of this file, which are the ones the adjunction needs.

The adjunction is stated for values in a universe strictly larger than the one carrying the
algebras. The special adjoint functor theorem requires the ambient category to be locally small
relative to the universe of the shapes of the colimits it admits, and the module-valued functors
on *all* commutative `A`-algebras have morphism types one universe above the algebra carriers
while admitting only the colimits of shapes bounded by the universe of the values. No such
condition appears in the source, where the algebras of `Alg_A` form a set.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
* [Stacks Project, Tag 06Z6](https://stacks.math.columbia.edu/tag/06Z6)
* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-! ## Full faithfulness and exactness of the inclusion -/

/-- **Stacks Project, Tag 06Z7**, part (1), the full faithfulness of `i`. The adequate functors
form a full subcategory of the module-valued functors, so their inclusion is fully faithful. -/
@[stacks 06Z7 "part (1), i is fully faithful"]
public noncomputable def fullyFaithful_adequateInclusion :
    (adequate.{u, v, max u v w} A).ι.FullyFaithful :=
  (adequate.{u, v, max u v w} A).fullyFaithfulι

/-- **Stacks Project, Tag 06Z7**, part (1), the left exactness of `i`. The adequate functors are
closed under kernels, so a kernel of adequate functors is already the kernel of the underlying
module-valued functors. -/
@[stacks 06Z7 "part (1), i is left exact"]
public lemma preservesFiniteLimits_adequateInclusion :
    PreservesFiniteLimits (adequate.{u, v, max u v w} A).ι :=
  have {X Y : (adequate.{u, v, max u v w} A).FullSubcategory} (f : X ⟶ Y) :=
    (adequate.{u, v, max u v w} A).preservesKernels_ι f
  (adequate.{u, v, max u v w} A).ι.preservesFiniteLimits_of_preservesKernels

/-- **Stacks Project, Tag 06Z7**, part (1), the right exactness of `i`. The adequate functors are
closed under cokernels, so a cokernel of adequate functors is already the cokernel of the
underlying module-valued functors. -/
@[stacks 06Z7 "part (1), i is right exact"]
public lemma preservesFiniteColimits_adequateInclusion :
    PreservesFiniteColimits (adequate.{u, v, max u v w} A).ι :=
  have {X Y : (adequate.{u, v, max u v w} A).FullSubcategory} (f : X ⟶ Y) :=
    (adequate.{u, v, max u v w} A).preservesCokernels_ι f
  have : HasFiniteCoproducts (ModuleValuedFunctor.{max u v w, v, u} A) :=
    have : HasFiniteColimits (ModuleValuedFunctor.{max u v w, v, u} A) :=
      PresheafOfModules.Finite.hasFiniteColimits _
    hasFiniteCoproducts_of_hasFiniteColimits _
  (adequate.{u, v, max u v w} A).ι.preservesFiniteColimits_of_preservesCokernels

/-- The image of `i` is a weak Serre subcategory as soon as the adequate functors are closed
under extensions. This is the third assertion of part (1) of [Stacks, Tag 06Z7], reduced to
closure under extensions: the adequate functors contain zero and are closed under isomorphisms,
kernels and cokernels, which are four of the five closure conditions of
`CategoryTheory.ObjectProperty.IsWeakSerreClass`, and the fifth is [Stacks, Tag 06V8]. -/
public lemma adequate_isWeakSerreClass_of_isClosedUnderExtensions
    [(adequate.{u, v, max u v w} A).IsClosedUnderExtensions] :
    (adequate.{u, v, max u v w} A).IsWeakSerreClass where

/-! ## Cocompleteness and a small separating family -/

/-- Adequacy is stable under arbitrary colimits of module-valued functors, by
[Stacks, Tag 06V4].

Deliberately not an instance: the universe of the values is forced to be the universe of the
shapes, and instance search then fails with an unsolvable universe constraint whenever it meets
this closure property at any other pair of universes. -/
public lemma adequate_isClosedUnderColimitsOfShape (J : Type (max u v w))
    [Category.{max u v w} J] :
    (adequate.{u, v, max u v w} A).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact IsAdequate.of_iso (isAdequate_colimit p.diag p.prop_diag_obj)
      (IsColimit.coconePointUniqueUpToIso p.isColimit (colimit.isColimit p.diag))

/-- The data presenting a linearly adequate functor: a map of finite free `A`-modules, together
with the two ranks. The resulting family of functors is a *set*, which is what makes it usable
as a separating family. -/
public abbrev LinearPresentation (A : Type u) [CommRing A] : Type (max u w) :=
  Σ n m : ℕ, (finiteFreeModule.{max u w} A n ⟶ finiteFreeModule.{max u w} A m)

/-- The linearly adequate functor presented by a map of finite free `A`-modules. -/
public noncomputable def ofLinearPresentation (d : LinearPresentation.{u, max u v w} A) :
    ModuleValuedFunctor.{max u v w, v} A :=
  kernel ((moduleExtensionFunctor.{max u v w, v} A).map d.2.2)

/-- A functor presented by a map of finite free modules is adequate, being a kernel of a map of
module extensions. -/
public lemma isAdequate_ofLinearPresentation (d : LinearPresentation.{u, max u v w} A) :
    IsAdequate (𝟭 _) (ofLinearPresentation.{u, v, w} A d) :=
  isAdequate_kernel _ (isAdequate_moduleExtension _) (isAdequate_moduleExtension _)

/-- Every linearly adequate functor is isomorphic to one presented by a map of finite free
modules, so the family `AdequateFunctor.ofLinearPresentation` exhausts them up to
isomorphism. -/
public lemma exists_iso_ofLinearPresentation {F : ModuleValuedFunctor.{max u v w, v} A}
    (hF : IsLinearlyAdequate (𝟭 _) F) :
    ∃ d : LinearPresentation.{u, max u v w} A,
      Nonempty (F ≅ ofLinearPresentation.{u, v, w} A d) := by
  obtain ⟨n, m, f, hpres⟩ := (isLinearlyAdequate_iff_exists_module_map (A := A) (F := F)).mp hF
  exact ⟨⟨n, m, f⟩, (isKernelPresentation_iff F f).mp hpres⟩

/-- The linearly adequate functor presented by a map of finite free modules, as an object of the
category of adequate functors. -/
public noncomputable def adequateOfLinearPresentation (d : LinearPresentation.{u, max u v w} A) :
    (adequate.{u, v, max u v w} A).FullSubcategory :=
  ⟨ofLinearPresentation.{u, v, w} A d, isAdequate_ofLinearPresentation.{u, v, w} A d⟩

/-- The linearly adequate functors form a separating family for the adequate functors: by
[Stacks, Tag 06UX] every adequate functor is a pointwise quotient of a direct sum of linearly
adequate functors, and each summand is isomorphic to one of the chosen family. -/
@[stacks 06UX "the linearly adequate functors separate the adequate functors"]
public lemma isSeparating_adequateOfLinearPresentation :
    (ObjectProperty.ofObj (adequateOfLinearPresentation.{u, v, w} A)).IsSeparating := by
  classical
  intro X Y f g hfg
  apply ObjectProperty.hom_ext
  let R := algebraRingDiagram.{v} A
  obtain ⟨J, L, hL, cover, hcover⟩ :=
    exists_coproduct_linearlyAdequate_surjective (A := A) X.obj X.property
  let eX : (presheafOfModulesUliftFunctor.{max u v, max u v w} R).obj X.obj ≅ X.obj :=
    presheafOfModulesUliftIso.{max u v, max u v w} R X.obj
  let cover' : (∐ L) ⟶ X.obj := cover ≫ eX.hom
  have hcover' : ∀ Z, Function.Surjective (cover'.app Z) := by
    intro Z y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (eX.hom.app Z)) y
    obtain ⟨x, hx⟩ := hcover Z z
    exact ⟨x, by simp [cover', hx, hz]⟩
  have : Epi cover' := PresheafOfModules.epi_of_surjective hcover'
  rw [← cancel_epi cover']
  apply colimit.hom_ext
  intro i
  obtain ⟨i⟩ := i
  obtain ⟨d, ⟨e⟩⟩ := exists_iso_ofLinearPresentation.{u, v, w} A (hL i)
  let h₀ : adequateOfLinearPresentation.{u, v, w} A d ⟶ X :=
    ObjectProperty.homMk (X := adequateOfLinearPresentation.{u, v, w} A d) (Y := X)
      (e.inv ≫ Sigma.ι L i ≫ cover')
  have key := hfg (adequateOfLinearPresentation.{u, v, w} A d)
    (ObjectProperty.ofObj_apply _ d) h₀
  have key' : (e.inv ≫ Sigma.ι L i ≫ cover') ≫ f.hom =
      (e.inv ≫ Sigma.ι L i ≫ cover') ≫ g.hom := congrArg InducedCategory.Hom.hom key
  change Sigma.ι L i ≫ cover' ≫ f.hom = Sigma.ι L i ≫ cover' ≫ g.hom
  rw [← cancel_epi e.inv]
  simpa using key'

/-! ## The right adjoint

The values are taken in a universe above the algebra carriers, so that the module-valued functors
are locally small for the universe of the shapes of the colimits they admit.
-/

/-- The inclusion of the adequate functors into all module-valued functors has a right adjoint,
by the special adjoint functor theorem: the adequate functors are cocomplete and have a small
separating family, and the inclusion preserves colimits. -/
public lemma isLeftAdjoint_adequateInclusion :
    (adequate.{u, v, max (u + 1) (v + 1) w} A).ι.IsLeftAdjoint := by
  have := adequate_isClosedUnderFiniteProducts.{u, v, max (u + 1) (v + 1) w} A
  have hsep := isSeparating_adequateOfLinearPresentation.{u, v, max (u + 1) (v + 1) w} A
  have : WellPowered.{max (u + 1) (v + 1) w}
      ((adequate.{u, v, max (u + 1) (v + 1) w} A).FullSubcategory) :=
    wellPowered_of_isDetecting hsep.isDetecting
  have h (J : Type (max (u + 1) (v + 1) w)) [Category.{max (u + 1) (v + 1) w} J] :=
    adequate_isClosedUnderColimitsOfShape.{u, v, max (u + 1) (v + 1) w} A J
  have : HasColimitsOfSize.{max (u + 1) (v + 1) w, max (u + 1) (v + 1) w}
      ((adequate.{u, v, max (u + 1) (v + 1) w} A).FullSubcategory) :=
    ⟨fun J _ => have := h J; inferInstance⟩
  have : PreservesColimitsOfSize.{max (u + 1) (v + 1) w, max (u + 1) (v + 1) w}
      (adequate.{u, v, max (u + 1) (v + 1) w} A).ι :=
    ⟨fun {J} _ => have := h J; inferInstance⟩
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating hsep _

/-- **Stacks Project, Tag 06Z6.** The functor `Q`, right adjoint to the inclusion of the adequate
module-valued functors into all module-valued functors. -/
public noncomputable def adequateCoreflection :
    ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A ⥤
      (adequate.{u, v, max (u + 1) (v + 1) w} A).FullSubcategory :=
  have := isLeftAdjoint_adequateInclusion.{u, v, w} A
  (adequate.{u, v, max (u + 1) (v + 1) w} A).ι.rightAdjoint

/-- **Stacks Project, Tag 06Z7**, part (3), the adjunction itself: the functor `Q` of
[Stacks, Tag 06Z6] is a right adjoint to the inclusion `i` of the adequate module-valued
functors into all module-valued functors. -/
@[stacks 06Z7 "part (3), Q is a right adjoint to i"]
public noncomputable def adequateCoreflectionAdjunction :
    (adequate.{u, v, max (u + 1) (v + 1) w} A).ι ⊣ adequateCoreflection.{u, v, w} A :=
  have := isLeftAdjoint_adequateInclusion.{u, v, w} A
  Adjunction.ofIsLeftAdjoint _

/-- **Stacks Project, Tag 06Z6.** For every module-valued functor `F` there is an adequate
functor `Q F` and a morphism `Q F ⟶ F` of module-valued functors such that every morphism to `F`
from an adequate functor factors uniquely through it. -/
@[stacks 06Z6]
public lemma exists_adequate_homEquiv
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) :
    ∃ (QF : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
      (_ : IsAdequate (𝟭 _) QF) (q : QF ⟶ F),
      ∀ (G : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A), IsAdequate (𝟭 _) G →
        ∀ φ : G ⟶ F, ∃! ψ : G ⟶ QF, ψ ≫ q = φ := by
  let adj := adequateCoreflectionAdjunction.{u, v, w} A
  let Q := adequateCoreflection.{u, v, w} A
  refine ⟨(Q.obj F).obj, (Q.obj F).property, adj.counit.app F, ?_⟩
  intro G hG φ
  let G' : (adequate.{u, v, max (u + 1) (v + 1) w} A).FullSubcategory := ⟨G, hG⟩
  refine ⟨(adj.homEquiv G' F φ).hom, ?_, ?_⟩
  · have h := adj.homEquiv_symm_apply (X := G') (Y := F) (g := adj.homEquiv G' F φ)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro ψ hψ
    have h := adj.homEquiv_symm_apply (X := G') (Y := F)
      (g := ObjectProperty.homMk (X := G') (Y := Q.obj F) ψ)
    have h2 : (adj.homEquiv G' F).symm
        (ObjectProperty.homMk (X := G') (Y := Q.obj F) ψ) = φ := by
      rw [h]; exact hψ
    have h3 : ObjectProperty.homMk (X := G') (Y := Q.obj F) ψ = adj.homEquiv G' F φ := by
      rw [← h2, Equiv.apply_symm_apply]
    exact congrArg InducedCategory.Hom.hom h3

/-- **Stacks Project, Tag 06Z7**, part (3), the left exactness: a right adjoint preserves all
limits, in particular the finite ones. -/
@[stacks 06Z7 "part (3), Q is left exact"]
public lemma preservesFiniteLimits_adequateCoreflection :
    PreservesFiniteLimits (adequateCoreflection.{u, v, w} A) := by
  have : (adequateCoreflection.{u, v, w} A).IsRightAdjoint :=
    ⟨_, ⟨adequateCoreflectionAdjunction.{u, v, w} A⟩⟩
  infer_instance

/-- **Stacks Project, Tag 06Z7**, part (4). The functor `Q` transforms injectives into
injectives: it is right adjoint to the exact functor `i`, so [Stacks, Tag 015Z] applies. -/
@[stacks 06Z7 "part (4)"]
public lemma preservesInjectiveObjects_adequateCoreflection :
    (adequateCoreflection.{u, v, w} A).PreservesInjectiveObjects := by
  have := adequate_isClosedUnderFiniteProducts.{u, v, max (u + 1) (v + 1) w} A
  let adj := adequateCoreflectionAdjunction.{u, v, w} A
  have := adj.right_adjoint_additive
  exact preservesInjectiveObjects_of_isExact _ _ adj
    ⟨preservesFiniteLimits_adequateInclusion.{u, v, max (u + 1) (v + 1) w} A,
      preservesFiniteColimits_adequateInclusion.{u, v, max (u + 1) (v + 1) w} A⟩

end AdequateFunctor

end
