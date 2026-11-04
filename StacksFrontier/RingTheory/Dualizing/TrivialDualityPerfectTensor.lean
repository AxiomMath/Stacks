module

public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolution
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlatBundleFree

/-!
# Trivial duality for a perfect algebra: derived Hom as a tensor functor

Let `R → A` be a homomorphism of commutative rings with `A` perfect as an `R`-module. Stacks 0BZE
says that derived coextension of scalars `R Hom(A, -) : D(R) ⥤ D(A)` of Stacks 0A70 is the derived
tensor product `K ↦ K ⊗ᴸ_R M` with the single object `M = R Hom(A, R)` of `D(A)`. The statement is
made in Situation 0BZB, which fixes the ring map together with a differential graded `R`-algebra
`E` and a quasi-isomorphism `E → A`; the conclusion mentions `E` only through the equivalence
`- ⊗_E^𝐋 A : D(E, d) ⥤ D(A)`. The tag itself is proved unconditionally in
`StacksFrontier/RingTheory/Dualizing/DerivedHomPerfectTensor.lean`, through a Tate resolution;
what this file contributes is one step of the independent K-flat route.

`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces Stacks 0BZE to invertibility
of one morphism, `Stacks0BZE.comparison`, at the K-flat complexes: the transpose under Stacks 0A70
of the derived counit `R Hom(A, R) ⟶ R` tensored with a K-flat complex. That invertibility is the
remaining mathematical content and is **not** proved here either; it is carried as the explicit
hypothesis `hiso` below, and it is where the perfectness hypothesis is destined to be spent,
through the derived tensor--Hom diagonal of Stacks 0ATK. The hypothesis is a pointwise statement
about one named morphism on a resolving class, while the conclusion is an isomorphism of functors
on all of `D(R)`; the passage between the two is the descent along K-flat resolutions of
Stacks 0BZE's reduction file.

What this file adds to that reduction is the unit case, computed without the chain-level fraction
that the construction of `Stacks0BZE.tensorCounit` chooses. The free module of rank one in degree
zero is K-flat, so the comparison exists there, and at that complex the tensored counit *is* the
derived counit of Stacks 0A70 at `R[0]`, up to the left unitor of the tensor product of complexes.
This is the identification of the tensor factor `M` with `R Hom(A, R)` at the generator of `D(R)`,
and it is what any proof of the remaining invertibility has to establish first.

## Main definitions

* `Stacks0BZE.unitLeftUnitorIso`: the left unitor `R[0] ⊗_R L ≅ L` of the tensor product of
  cochain complexes of `R`-modules, at a module universe above the ring's.

## Main results

* `Stacks0BZE.kFlat_unitComplex`: the free module of rank one in degree zero is K-flat.
* `Stacks0BZE.tensorCounit_unitComplex`: at the free module of rank one in degree zero,
  `Stacks0BZE.tensorCounit` is the left unitor followed by the derived counit of Stacks 0A70 —
  a formula in which the chosen fraction no longer occurs.
* `Stacks0BZE.restrictedComparison_unitComplex`: the same formula read on
  `Stacks0BZE.restrictedComparison`.

## Implementation notes

The left unitor is spelled out rather than taken from `Stacks0BZE.unitorIso`, which is the *right*
unitor; both are needed, and the only point at which they meet is
`CategoryTheory.MonoidalCategory.unitors_equal` at the unit object, which is exactly the step that
removes the fraction. The monoidal structure is the lifted one on `ModuleCat.{max v u} R`, whose
tensor unit is the free module of rank one on a lifted carrier; Mathlib's own monoidal structure on
`ModuleCat` exists only when the module universe agrees with the ring's.

**Where the perfectness hypothesis does and does not work.** In
`Stacks0BZE.cardIso` of `TrivialDualityKFlat` and in Situation 0BZB
it is *decorative*: the descent along K-flat resolutions that proves those two does not use it, and
it is recorded only because it is the hypothesis of Stacks 0BZE and because the carried
invertibility of `Stacks0BZE.comparison` is where the source spends it. It is spent for real in
`Dualizing.exists_derivedHom_iso_derivedTensor`, through the compactness of the resolving bimodule.

The two rings live in one universe `u` and the modules in an independent universe above it, which
is the generality of the reduction file.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), the statement.
* [The Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation.
* [The Stacks Project, Tag 0BZC](https://stacks.math.columbia.edu/tag/0BZC), derived Hom through
  the resolution.
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70) for `R Hom(A, -)`,
  [Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) for the derived tensor product,
  [Tag 064K](https://stacks.math.columbia.edu/tag/064K) for K-flatness of a bounded above complex
  of flat modules and [Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK) for the derived
  tensor--Hom diagonal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.DerivedTensor DifferentialGradedModule

-- `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` installs a locally small model of
-- `D(Mod R)` as a global instance, and the imported statements of this chapter are all read at the
-- standard model; the priority settles which of the two a bare `DerivedCategory (ModuleCat R)`
-- written below means.
attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-! ### The left unitor, and K-flatness of the unit complex -/

/-- The left unitor of the tensor product of cochain complexes of `R`-modules: tensoring a complex
on the left with the free module of rank one in degree zero gives the complex back.
`Stacks0BZE.unitorIso` is the right unitor of the same tensor product. -/
def unitLeftUnitorIso (L : CochainComplex (ModuleCat.{max v u} R) ℤ) :
    ((tensorBifunctor.{u, v} R).obj (unitComplex.{u, v} R)).obj L ≅ L :=
  let : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  MonoidalCategoryStruct.leftUnitor L

/-- The left unitor `Stacks0BZE.unitLeftUnitorIso` is natural in the complex. -/
lemma unitLeftUnitorIso_naturality {L M : CochainComplex (ModuleCat.{max v u} R) ℤ} (a : L ⟶ M) :
    ((tensorBifunctor.{u, v} R).obj (unitComplex.{u, v} R)).map a ≫
        (unitLeftUnitorIso.{u, v} M).hom =
      (unitLeftUnitorIso.{u, v} L).hom ≫ a :=
  let : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  MonoidalCategory.leftUnitor_naturality a

/-- At the unit complex the left and the right unitor agree. -/
lemma unitLeftUnitorIso_unitComplex :
    (unitLeftUnitorIso.{u, v} (unitComplex.{u, v} R)).hom =
      (unitorIso.{u, v} (unitComplex.{u, v} R)).hom :=
  let : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  MonoidalCategory.unitors_equal

/-- **The unit complex is K-flat.** The free module of rank one on a lifted carrier is flat and
the complex is concentrated in degree zero, so Stacks 064K applies. -/
lemma kFlat_unitComplex : CochainComplex.KFlat.{u, max v u} (unitComplex.{u, v} R) := by
  have hflat : ∀ n : ℤ, Module.Flat R ((unitComplex.{u, v} R).X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact Module.Flat.of_linearEquiv
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (ModuleCat.of R (ULift.{max v u} R))).toLinearEquiv.trans ULift.moduleEquiv)
    · have hz : IsZero ((unitComplex.{u, v} R).X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      let _ := ModuleCat.isZero_iff_subsingleton.mp hz
      rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
      intro N N' _ _ _ _ g _
      exact fun x y _ => Subsingleton.elim x y
  let _ := hflat
  let _ : (unitComplex.{u, v} R).IsStrictlyLE 0 :=
    inferInstanceAs
      (((CochainComplex.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (ULift.{max v u} R))).IsStrictlyLE 0)
  exact CochainComplex.KFlat.kFlat_of_flat (unitComplex.{u, v} R) 0

/-! ### The comparison at the unit complex -/

/-- **The tensored counit at the unit complex, without the fraction.** `Stacks0BZE.tensorCounit`
is constructed from a chain-level right fraction for the derived counit `R Hom(A, R) ⟶ R` of
Stacks 0A70, because tensoring with a K-flat complex is only defined on chain maps. At the unit
complex the construction collapses: the result is the left unitor followed by that derived counit
itself, so the chosen fraction does not appear.

Both unitors occur in the proof, the right one inside `Stacks0BZE.tensorCounit` and the left one in
the statement; they are compared by `Stacks0BZE.unitLeftUnitorIso_unitComplex`, which is the one
place where the numerator of the fraction is released. -/
theorem tensorCounit_unitComplex
    (hU : CochainComplex.KFlat.{u, max v u} (unitComplex.{u, v} R)) :
    tensorCounit.{u, v} f (unitComplex.{u, v} R) hU =
      DerivedCategory.Q.map (unitLeftUnitorIso.{u, v} (dualRestricted.{u, v} f)).hom ≫
        dualCounit.{u, v} f := by
  have hdeniso : IsIso (DerivedCategory.Q.map (fraction.{u, v} f).den) :=
    (fraction.{u, v} f).den_isIso
  have hnat : ∀ {M : CochainComplex (ModuleCat.{max v u} R) ℤ} (g : (fraction.{u, v} f).source ⟶ M)
      (e : ((tensorBifunctor.{u, v} R).obj (unitComplex.{u, v} R)).obj M ⟶ M),
      e = (unitLeftUnitorIso.{u, v} M).hom →
      DerivedCategory.Q.map (((tensorBifunctor.{u, v} R).obj (unitComplex.{u, v} R)).map g) ≫
          DerivedCategory.Q.map e =
        DerivedCategory.Q.map (unitLeftUnitorIso.{u, v} (fraction.{u, v} f).source).hom ≫
          DerivedCategory.Q.map g := by
    rintro M g _ rfl
    rw [← Functor.map_comp, ← Functor.map_comp, unitLeftUnitorIso_naturality]
  have hnat1 := hnat (fraction.{u, v} f).den _ rfl
  have hnat2 := hnat (fraction.{u, v} f).num _ unitLeftUnitorIso_unitComplex.symm
  rw [tensorCounit_eq, Iso.inv_comp_eq, tensorDenIso_hom, ← Category.assoc, hnat1,
    (fraction.{u, v} f).fac, Category.assoc]
  rw [IsIso.hom_inv_id_assoc]
  exact hnat2

/-- **The restricted comparison at the unit complex.** Reading
`Stacks0BZE.tensorCounit_unitComplex` through the three structural comparisons of the derived
change-of-rings bundle: the restriction to `R` of the comparison of Stacks 0BZE at the free module
of rank one in degree zero is the derived counit of Stacks 0A70, up to the left unitor. -/
theorem restrictedComparison_unitComplex
    (hU : CochainComplex.KFlat.{u, max v u} (unitComplex.{u, v} R)) :
    restrictedComparison.{u, v} f (unitComplex.{u, v} R) hU =
      (underlyingNatTrans.{u, v} f).app (unitComplex.{u, v} R) ≫
        DerivedCategory.Q.map (unitLeftUnitorIso.{u, v} (dualRestricted.{u, v} f)).hom ≫
          dualCounit.{u, v} f := by
  rw [restrictedComparison_eq, tensorCounit_unitComplex.{u, v} f hU]
  rfl

end Stacks0BZE

end
