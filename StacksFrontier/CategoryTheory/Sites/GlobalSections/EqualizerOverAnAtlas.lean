module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections

/-!
# Global sections as an equalizer over a single covering object

Let `(C, J)` be a site, let `U` be an object whose one-element family covers the final object,
and let `a, b : V ⟶ U` be a pair of morphisms through which *every* pair of morphisms into `U`
factors. Then for every sheaf of sets `F` on `C` the evaluation map

`Γ(C, F) ⟶ F(U) ⇉ F(V)`

is an equalizer: a global section is determined by its value at `U`, and a section `x ∈ F(U)`
with `a^* x = b^* x` comes from a global section.

This is the shape of the statement of Stacks 0792, with that lemma's hypothesis — the final
sheaf is the coequalizer of `h_V^# ⇉ h_U^#` — replaced by two conditions one can check directly
on the site:

* `J.CoversTop (fun _ : Unit => U)`, i.e. for every object `X` the sieve of morphisms factoring
  through `U` covers `X`; this is what makes a global section determined by its value at `U`;
* the factorization property of the pair `a, b`, i.e. any two morphisms `f, g : Z ⟶ U` are
  `h ≫ a` and `h ≫ b` for a common `h : Z ⟶ V`; this is what upgrades the single equation
  `a^* x = b^* x` to the compatibility of `x` with itself along *all* pairs of morphisms into
  `U`, which is what the sheaf axiom glues.

Both conditions hold at the site one meets in practice: `U` an étale chart of an atlas of an
algebraic space, `V` the fibre product `U ×_F U` — which is a scheme because the atlas is
representable — and `a, b` its two projections, the factorization being the universal property
of that fibre product, available because the morphisms of the site are morphisms *over* `F`.

## Main definitions

* `CategoryTheory.Presheaf.globalSectionsEval`: the value of a global section at an object,
  i.e. the map `Γ(C, F) → F(U)`.
* `CategoryTheory.Presheaf.globalSectionsEquivEqualizer`: the main result, as a bijection of
  `Γ(C, F)` with the set of `x ∈ F(U)` satisfying `a^* x = b^* x`.

## Main results

* `CategoryTheory.Presheaf.globalSectionsEval_injective`: a global section is determined by its
  value at `U`.
* `CategoryTheory.Presheaf.exists_globalSectionsEval_eq`: a compatible section over `U` is the
  value of a global section.

## References

* [Stacks Project, Tag 06UN](https://stacks.math.columbia.edu/tag/06UN)
* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
-/

@[expose] public section

namespace CategoryTheory.Presheaf

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The value at an object `U` of a global section of a presheaf of sets, in the sense of
Stacks 06UN: a global section is a compatible family of sections by
`CategoryTheory.Presheaf.globalSectionsEquivSections`, and this is that family's value at `U`. -/
noncomputable def globalSectionsEval (F : Cᵒᵖ ⥤ Type w) (U : C) (s : globalSections F) :
    F.obj (op U) :=
  (globalSectionsEquivSections F s).1 (op U)

/-- Unfolding lemma for `CategoryTheory.Presheaf.globalSectionsEval`. -/
theorem globalSectionsEval_def (F : Cᵒᵖ ⥤ Type w) (U : C) (s : globalSections F) :
    globalSectionsEval F U s = (globalSectionsEquivSections F s).1 (op U) :=
  rfl

/-- The values of a global section at the objects of `C` are compatible with the restriction
maps of the presheaf. -/
theorem globalSectionsEval_map (F : Cᵒᵖ ⥤ Type w) {U U' : C} (g : U' ⟶ U)
    (s : globalSections F) :
    F.map g.op (globalSectionsEval F U s) = globalSectionsEval F U' s :=
  (globalSectionsEquivSections F s).2 g.op

section

variable (F : Cᵒᵖ ⥤ Type w) {U V : C} {a b : V ⟶ U}

/-- The factorization property of a pair `a, b : V ⟶ U`: every pair of morphisms into `U` from
a common source is obtained from `a` and `b` by precomposition with a single morphism.

At `U` an étale chart of an algebraic space `F` and `V = U ×_F U` with `a, b` the projections
this is the universal property of the fibre product, available because the morphisms of the
site are morphisms over `F`. -/
def FactorsPairs (a b : V ⟶ U) : Prop :=
  ∀ (Z : C) (f g : Z ⟶ U), ∃ h : Z ⟶ V, h ≫ a = f ∧ h ≫ b = g

/-- A section over `U` equalizing `a^*` and `b^*` is, as a one-element family of elements on
objects, compatible in the sense of
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`.

This is where the factorization property of the pair is used: compatibility quantifies over
*all* pairs of morphisms into `U`, and each such pair comes from `a, b`. -/
theorem isCompatible_const_of_eq (hrel : FactorsPairs a b) {x : F.obj (op U)}
    (hx : F.map a.op x = F.map b.op x) :
    FamilyOfElementsOnObjects.IsCompatible (F := F) (Y := fun _ : Unit => U) (fun _ => x) := by
  intro Z _ _ f g
  obtain ⟨h, rfl, rfl⟩ := hrel Z f g
  simp only [op_comp, Functor.map_comp_apply, hx]

variable (hF : IsSheaf J F) (hU : J.CoversTop (fun _ : Unit => U))

include hF hU

/-- **A global section is determined by its value at a single covering object.** -/
theorem globalSectionsEval_injective : Function.Injective (globalSectionsEval F U) := by
  intro s t hst
  apply (globalSectionsEquivSections F).injective
  refine hU.sections_ext ⟨F, hF⟩ fun _ => hst

/-- **A section over a covering object which equalizes `a^*` and `b^*` is the value of a global
section.** -/
theorem exists_globalSectionsEval_eq (hrel : FactorsPairs a b) (x : F.obj (op U))
    (hx : F.map a.op x = F.map b.op x) :
    ∃ s : globalSections F, globalSectionsEval F U s = x := by
  refine ⟨(globalSectionsEquivSections F).symm
    ((isCompatible_const_of_eq F hrel hx).section_ hU hF), ?_⟩
  rw [globalSectionsEval_def, Equiv.apply_symm_apply]
  exact FamilyOfElementsOnObjects.IsCompatible.section_apply _ hU hF ()

/-- **Global sections as an equalizer over a single covering object.** For a sheaf of sets `F`
on a site `(C, J)`, an object `U` whose one-element family covers the final object, and a pair
`a, b : V ⟶ U` through which every pair of morphisms into `U` factors, the global sections
`Γ(C, F)` of Stacks 06UN are the sections over `U` equalizing `a^*` and `b^*`, the bijection
being evaluation at `U`.

This is the conclusion of Stacks 0792, derived from conditions on the site rather than from
that lemma's coequalizer hypothesis; see the module documentation. -/
noncomputable def globalSectionsEquivEqualizer (hrel : FactorsPairs a b) :
    globalSections F ≃ {x : F.obj (op U) // F.map a.op x = F.map b.op x} :=
  Equiv.ofBijective
    (fun s => ⟨globalSectionsEval F U s, by
      rw [globalSectionsEval_map F a s, globalSectionsEval_map F b s]⟩)
    ⟨fun _ _ hst => globalSectionsEval_injective F hF hU (congrArg Subtype.val hst),
      fun x => by
        obtain ⟨s, hs⟩ := exists_globalSectionsEval_eq F hF hU hrel x.1 x.2
        exact ⟨s, Subtype.ext hs⟩⟩

/-- The bijection `CategoryTheory.Presheaf.globalSectionsEquivEqualizer` is evaluation at `U`. -/
@[simp] theorem globalSectionsEquivEqualizer_apply_coe (hrel : FactorsPairs a b)
    (s : globalSections F) :
    (globalSectionsEquivEqualizer F hF hU hrel s).1 = globalSectionsEval F U s :=
  rfl

end

end CategoryTheory.Presheaf
