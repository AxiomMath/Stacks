module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonLinearity

/-!
# The displayed map of Stacks 0EG2 from the comparison at one neighbourhood

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `ℱ` be a coherent
module on `U`. The comparison

`Stacks.Algebraization.comparisonMap : colim_V Γ(V, ℱ) ⟶ lim_n Γ(U, ℱ/Iⁿℱ)`

is always injective, by `Stacks.Algebraization.mono_comparisonMap`. This file records what the
surjectivity of the comparison **at a single neighbourhood** `V` adds to that:

* the displayed map is an isomorphism;
* the colimit inclusion `Γ(V, ℱ) ⟶ colim_W Γ(W, ℱ)` is onto, so the colimit is a quotient of the
  sections on `V` — which is what carries a finiteness statement about `Γ(V, ℱ)` over to the
  colimit.

Neither needs the injectivity of the comparison at `V`, which is what
`Stacks.Algebraization.isIso_comparisonMap_of_surjective_comparisonAt` asks for in order to make
the colimit inclusion an isomorphism; the weaker conclusions here are reached from the
unconditional injectivity of the displayed map.

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_surjective_comparisonAt'` — the displayed map is
  an isomorphism.
* `Stacks.Algebraization.surjective_colimit_ι_of_surjective_comparisonAt` — the colimit inclusion
  of `V` is onto.
* `Stacks.Algebraization.sectionsAtModule`, `Stacks.Algebraization.colimitιModuleMap` — the
  sections on `V` as an `A`-module, and the colimit inclusion as an `A`-linear map.
* `Stacks.Algebraization.finite_sectionsNearVanishingColimit_of_surjective_comparisonAt` — the
  colimit is a finite `A`-module as soon as the sections on `V` are.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-! ### The displayed map, and the colimit inclusion -/

variable [IsNoetherianRing A] [F.IsCoherent] {V : OpensNearVanishing A I a}

/-- The displayed map sends the colimit inclusion of a section on `V` to its comparison at `V`. -/
private theorem comparisonMap_colimit_ι_apply {B : Type u} [CommRing B] (J b : Ideal B)
    (G : (complementZeroLocus B b : Scheme).Modules) {W : OpensNearVanishing B J b}
    (t : ToType ((sectionsNearVanishing B J b G).obj W)) :
    ConcreteCategory.hom (comparisonMap B J b G)
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing B J b G) W) t) =
      ConcreteCategory.hom (comparisonAt B J b G W) t := by
  rw [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap]

/-- **The displayed map of Stacks 0EG2 is an isomorphism once the comparison at one neighbourhood
is onto.** Injectivity is `Stacks.Algebraization.mono_comparisonMap`, which holds with no
hypothesis beyond `A` Noetherian and `ℱ` coherent; surjectivity is immediate from the
factorization of the comparison at `V` through the colimit inclusion. -/
public theorem isIso_comparisonMap_of_surjective_comparisonAt'
    (hsurj : Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V))) :
    IsIso (comparisonMap A I a F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(AddCommGrpCat.mono_iff_injective _).1 (mono_comparisonMap A I a F), fun s => ?_⟩
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t, ?_⟩
  exact (comparisonMap_colimit_ι_apply I a F t).trans ht

/-- **The colimit inclusion of a neighbourhood at which the comparison is onto is itself onto.**
A class in the colimit has the same image under the displayed map as the comparison at `V` of
some section on `V`, and the displayed map is injective. -/
public theorem surjective_colimit_ι_of_surjective_comparisonAt
    (hsurj : Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V))) :
    Function.Surjective
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V)) := by
  intro z
  obtain ⟨t, ht⟩ := hsurj (ConcreteCategory.hom (comparisonMap A I a F) z)
  refine ⟨t, (AddCommGrpCat.mono_iff_injective _).1 (mono_comparisonMap A I a F) ?_⟩
  exact (comparisonMap_colimit_ι_apply I a F t).trans ht

/-! ### The sections on one neighbourhood as an `A`-module -/

section Module

variable {A I a F}

/-- Multiplication by `A` on the sections of `ℱ` over a single neighbourhood of the formal
locus. -/
public def sectionsAtSmul (V : OpensNearVanishing A I a) :
    A →+* End ((sectionsNearVanishing A I a F).obj V) where
  toFun r := End.of ((smulSectionsNearVanishing A I a F r).app V)
  map_one' := End.ext (congrArg
    (fun α : sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a F => α.app V)
    (smulSectionsNearVanishing_one A I a F))
  map_mul' r s := End.ext (congrArg
    (fun α : sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a F => α.app V)
    (smulSectionsNearVanishing_mul A I a F r s))
  map_zero' := End.ext (congrArg
    (fun α : sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a F => α.app V)
    (smulSectionsNearVanishing_zero A I a F))
  map_add' r s := End.ext (congrArg
    (fun α : sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a F => α.app V)
    (smulSectionsNearVanishing_add A I a F r s))

/-- **The sections of `ℱ` over a single neighbourhood of the formal locus, as an `A`-module.** -/
public def sectionsAtModule (V : OpensNearVanishing A I a) : ModuleCat.{u} A :=
  ModuleCat.mkOfSMul (sectionsAtSmul (F := F) V)

/-- **The colimit inclusion of a neighbourhood is `A`-linear.** -/
public def colimitιModuleMap (V : OpensNearVanishing A I a) :
    sectionsAtModule (F := F) V ⟶ sectionsNearVanishingColimit A I a F :=
  ModuleCat.homMk (colimit.ι (sectionsNearVanishing A I a F) V) fun r =>
    (ι_colimMap (smulSectionsNearVanishing A I a F r) V).trans
      (congrArg (fun φ : (sectionsNearVanishing A I a F).obj V ⟶
        (sectionsNearVanishing A I a F).obj V => φ ≫
          colimit.ι (sectionsNearVanishing A I a F) V) rfl)

omit [IsNoetherianRing A] [F.IsCoherent] in
/-- The linear map `colimitιModuleMap V` acts on sections as the colimit inclusion of `V`. -/
public theorem colimitιModuleMap_apply (V : OpensNearVanishing A I a)
    (x : ToType ((sectionsNearVanishing A I a F).obj V)) :
    ModuleCat.Hom.hom (colimitιModuleMap (F := F) V) x =
      ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) x :=
  rfl

variable [IsNoetherianRing A] [F.IsCoherent] {V : OpensNearVanishing A I a}

/-- **The colimit of the sections near the formal locus is a finite `A`-module** as soon as the
sections on one neighbourhood at which the comparison is onto are: the colimit inclusion of that
neighbourhood is an `A`-linear surjection. -/
public theorem finite_sectionsNearVanishingColimit_of_surjective_comparisonAt
    [Module.Finite A (sectionsAtModule (F := F) V)]
    (hsurj : Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V))) :
    Module.Finite A (sectionsNearVanishingColimit A I a F) :=
  Module.Finite.of_surjective (ModuleCat.Hom.hom (colimitιModuleMap (F := F) V))
    fun z => by
      obtain ⟨t, ht⟩ := surjective_colimit_ι_of_surjective_comparisonAt A I a F hsurj z
      exact ⟨t, (colimitιModuleMap_apply V t).trans ht⟩

/-- **The formal sections are a finite `A`-module** as soon as the sections on one neighbourhood
at which the comparison is onto are: the displayed map is then an `A`-linear isomorphism. -/
public theorem finite_formalSectionsLimit_of_surjective_comparisonAt
    [Module.Finite A (sectionsAtModule (F := F) V)]
    (hsurj : Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V))) :
    Module.Finite A (formalSectionsLimit A I a F) := by
  let : Module.Finite A (sectionsNearVanishingColimit A I a F) :=
    finite_sectionsNearVanishingColimit_of_surjective_comparisonAt hsurj
  let : IsIso (comparisonModuleMap A I a F) :=
    (isIso_comparisonModuleMap_iff A I a F).2
      (isIso_comparisonMap_of_surjective_comparisonAt' A I a F hsurj)
  exact Module.Finite.of_surjective (ModuleCat.Hom.hom (comparisonModuleMap A I a F))
    (ConcreteCategory.bijective_of_isIso (comparisonModuleMap A I a F)).2

end Module

end Stacks.Algebraization

end
