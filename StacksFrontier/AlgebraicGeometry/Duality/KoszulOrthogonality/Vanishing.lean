module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.RingTheory.Koszul.Truncation.DerivedKoszulObject

/-!
# Vanishing in the derived category from acyclicity of a complex

The hypothesis `hKzero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/OpenImmersion.lean` asks that the
Koszul object of [Stacks, Tag 09IR] restricts to zero on the open subscheme. That is a statement
in the derived category, and this file reduces it to a statement about an honest complex: a
complex whose image under the localization functor `Q` must be a zero object is exactly an
acyclic one, and an exact functor may be moved past `Q`.

The point of doing this separately is that acyclicity of a complex of sheaves of modules is a
*local* condition, testable on stalks by
`AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic`
(`StacksFrontier/Topology/Sheaves/Modules/StalkAcyclic.lean`), whereas vanishing in the derived
category is not directly. So the reduction below is the step that makes the geometric input of
[Stacks, Tag 09IR] approachable at all: on the principal open `D(f_i)` the entry `f_i` of the
sequence becomes invertible, and `Koszul.acyclic_seqComplex_of_isUnit`
(`StacksFrontier/RingTheory/Koszul/PowerLift/UnitEntry.lean`) says the Koszul complex of a sequence
with an invertible entry is acyclic.

## Main results

* `CategoryTheory.DerivedCategory.isZero_Q_obj_of_acyclic` — an acyclic complex becomes a zero
  object of the derived category.
* `CategoryTheory.Functor.isZero_mapDerivedCategory_obj_Q_obj_of_acyclic` — the same after an
  exact functor, which is moved past `Q` by `Functor.mapDerivedCategoryFactors`.
* `Stacks.Duality.OpenImmersion.isZero_derivedRestrict_Q_obj_of_acyclic` — the form the open
  immersion `j^*` of
  `StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictAdjunction.lean` takes.
* `Stacks.Koszul.Truncation.isZero_derivedRestrict_koszulObject_of_acyclic` — the hypothesis
  `hKzero` for the sheafified Koszul object, reduced to acyclicity of the restriction to
  `⋃ᵢ D(f_i)` of the termwise sheafified Koszul complex.

## Implementation notes

Only the direction "acyclic implies zero" is proved. The converse holds and is not needed; it
would require the characterisation of zero objects of `DerivedCategory C` by vanishing homology,
which this repository has only as a `private` declaration, three times over —
`StacksFrontier/Homology/DerivedComplete/AdicKoszulCompletion.lean:439`,
`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean:778` and
`StacksFrontier/Homology/DerivedComplete/DerivedHomCompletionVanishing.lean:2355`. The proof here
avoids it: an acyclic complex `K` has the zero morphism `K ⟶ 0` as a quasi-isomorphism, because
both homologies vanish in every degree, so `Q.map 0` is invertible and `Q.obj K` is isomorphic to
`Q.obj 0`, which is zero because `Q` is additive.

No `@[stacks]` attribute is attached; nothing here is a tagged statement.

Everything is stated at a free `[HasDerivedCategory.{w} _]`, never at
`CategoryTheory.HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **An acyclic complex becomes a zero object of the derived category.** The zero morphism from
an acyclic complex to the zero complex is a quasi-isomorphism — in every degree both sides have
vanishing homology, so any morphism between them is invertible — hence `Q` sends it to an
isomorphism, and `Q` of the zero complex is zero because `Q` is additive. -/
theorem isZero_Q_obj_of_acyclic (K : CochainComplex C ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  have hzero : ∀ i : ℤ, IsZero ((0 : CochainComplex C ℤ).homology i) := fun i =>
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)
  have hq : QuasiIso (0 : K ⟶ (0 : CochainComplex C ℤ)) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hK i).isZero_homology.isIso (hzero i) _
  exact ((DerivedCategory.Q (C := C)).map_isZero (isZero_zero (CochainComplex C ℤ))).of_iso
    (asIso (DerivedCategory.Q.map (0 : K ⟶ (0 : CochainComplex C ℤ))))

end CategoryTheory.DerivedCategory

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor sends the class of an acyclic complex to zero.** By
`CategoryTheory.Functor.mapDerivedCategoryFactors` the object
`F.mapDerivedCategory.obj (Q.obj K)` is isomorphic to `Q.obj ((F.mapHomologicalComplex _).obj K)`,
so the hypothesis to check is acyclicity of the complex obtained by applying `F` degreewise. -/
theorem isZero_mapDerivedCategory_obj_Q_obj_of_acyclic (K : CochainComplex C₁ ℤ)
    (hK : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) :
    IsZero (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
  (DerivedCategory.isZero_Q_obj_of_acyclic _ hK).of_iso (F.mapDerivedCategoryFactors.app K)

end CategoryTheory.Functor

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **`j^*` kills the class of a complex whose restriction along `j` is acyclic.** This is the
shape in which the hypothesis `hKzero` of
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_iff` is to be
discharged, and through it the hypothesis `hunit` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion`: restriction
along an open immersion is exact, so the question is whether the restricted complex of sheaves of
modules is acyclic, and that is a stalkwise condition.

The route through `…isWeakTriangulatedGenerator_biprod_of_detection` is not available: its
hypothesis `hdet` is quantified over all of
`D(𝒪_Y)` and is false, as the docstring of
`Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` records with a
discrete-valuation-ring counterexample. The quasi-coherent form that is true and tagged is
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`
(registered for 09IR, implication (2) to (1)), which discharges `hKzero` itself. -/
theorem isZero_derivedRestrict_Q_obj_of_acyclic (K : CochainComplex Y.Modules ℤ)
    (hK : (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) :
    IsZero ((derivedRestrict j).obj (DerivedCategory.Q.obj K)) :=
  (Scheme.Modules.restrictFunctor j).isZero_mapDerivedCategory_obj_Q_obj_of_acyclic K hK

end Stacks.Duality.OpenImmersion

namespace Stacks.Koszul.Truncation

open Stacks.Duality.OpenImmersion

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
  [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules]
  [HasDerivedCategory.{w} (openComplement f).toScheme.Modules]

/-- **The hypothesis `hKzero` of [Stacks, Tag 09IR], reduced to an acyclicity statement.** The
sheafified Koszul object of a finite sequence `f₁, …, f_r` in `A` restricts to zero on the open
complement `⋃ᵢ D(f_i)` of the common zero locus as soon as the termwise sheafified Koszul
complex, restricted to that open, is acyclic.

What remains is local and algebraic, and both halves of it are already available: acyclicity of
a complex of sheaves of modules is tested on stalks by
`AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic`, a point of `⋃ᵢ D(f_i)` lies
in some `D(f_i)`, and the Koszul complex of a sequence one of whose entries is invertible is
acyclic by `Koszul.acyclic_seqComplex_of_isUnit`. -/
theorem isZero_derivedRestrict_koszulObject_of_acyclic
    (hf : (((Scheme.Modules.restrictFunctor (openComplement f).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat))).Acyclic) :
    IsZero ((derivedRestrict (openComplement f).ι).obj (koszulObject f)) :=
  isZero_derivedRestrict_Q_obj_of_acyclic (openComplement f).ι _ hf

end Stacks.Koszul.Truncation

end
