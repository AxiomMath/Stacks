module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence

/-!
# Local sections of the conormal sheaf

The conormal sheaf `I/I²` of a presentation `φ : A ⟶ B` of sheaves of commutative rings is the
associated sheaf of the objectwise conormal presheaf `U ↦ I(U)/I(U)²`, so a section of it over
an object is *not* the class of a section of the kernel ideal; it is only locally one. This
file proves that the conormal class of a section of the kernel ideal depends only on its class
modulo the square of the ideal, and that every section of the conormal sheaf is locally such a
class.

## Main results

* `Stacks.Sites.Conormal.conormalClass_eq_of_sub_mem_sq`: two sections of the kernel ideal
  differing by a section of its square have the same conormal class.
* `Stacks.Sites.Conormal.conormalClass_eq_zero_of_mem_sq`: a section of the square of the kernel
  ideal has vanishing conormal class.
* `Stacks.Sites.Conormal.exists_covering_conormalClass_eq`: **a section of the conormal sheaf
  is, on a covering sieve, the conormal class of a section of the kernel ideal.**

## Implementation notes

The second statement is local surjectivity of the module sheafification unit, read on one
section.  The unit's underlying morphism of presheaves of abelian groups is
`CategoryTheory.toSheafify` on the nose — `PresheafOfModules.toPresheaf_map_toSheafify` and
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app` are both `rfl` — so its
local surjectivity is the Mathlib instance for that morphism, quoted through `inferInstanceAs`
rather than re-derived.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation, whose degree `-1` comparison reads the conormal
  sheaf on local sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of presheaves of additive commutative groups on an essentially small site. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially small site, a morphism of presheaves of additive commutative groups
becomes an isomorphism after sheafification exactly when it is locally bijective. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two sections of the kernel ideal differing by a section of its square have the same
conormal class. -/
theorem conormalClass_eq_of_sub_mem_sq (X : Cᵒᵖ) (x y : kernelIdeal φ.hom X)
    (h : (x : A.obj.obj X) - (y : A.obj.obj X) ∈ kernelIdeal φ.hom X ^ 2) :
    conormalClass.{v, u, w, z} J R A B a φ X x =
      conormalClass.{v, u, w, z} J R A B a φ X y := by
  exact congrArg (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X)
    ((Ideal.toCotangent_eq _).mpr h)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A section of the square of the kernel ideal has vanishing conormal class. -/
theorem conormalClass_eq_zero_of_mem_sq (X : Cᵒᵖ) (x : kernelIdeal φ.hom X)
    (h : (x : A.obj.obj X) ∈ kernelIdeal φ.hom X ^ 2) :
    conormalClass.{v, u, w, z} J R A B a φ X x = 0 := by
  refine Eq.trans (congrArg
    (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X)
    ((Ideal.toCotangent_eq_zero (kernelIdeal φ.hom X) x).mpr h)) ?_
  exact map_zero (((PresheafOfModules.sheafificationAdjunction.{max w u v z}
    (quotientToRingSheaf J A B φ)).unit.app
      ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom))).app X).hom

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A section of the conormal sheaf over `X` is, on a covering sieve of `X`, the conormal class
of a section of the kernel ideal. -/
theorem exists_covering_conormalClass_eq (X : C)
    (c : (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.obj (op X)) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g →
      ∃ x : kernelIdeal φ.hom (op Y),
        conormalClass.{v, u, w, z} J R A B a φ (op Y) x =
          (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.map g.op c := by
  set f := (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction.{max w u v z}
      (quotientToRingSheaf J A B φ)).unit.app
      ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom)))
  have hls : Presheaf.IsLocallySurjective J f :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J
      ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom)).presheaf))
  refine ⟨_, Presheaf.imageSieve_mem J f c, fun Y g hg ↦ ?_⟩
  obtain ⟨y, hy⟩ := hg
  obtain ⟨x, hx⟩ := (kernelIdeal φ.hom (op Y)).toCotangent_surjective y.down
  exact ⟨x, Eq.trans (congrArg (fun t ↦ f.app (op Y) t) (congrArg ULift.up hx)) hy⟩

end Stacks.Sites.Conormal

end
