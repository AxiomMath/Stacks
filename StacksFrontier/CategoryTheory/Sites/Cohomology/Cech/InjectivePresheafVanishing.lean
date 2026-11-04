module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an injective abelian presheaf

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of
whose finite nonempty fibre products exist. The positive-degree Čech cohomology of an
*injective* presheaf of abelian groups with respect to `E` vanishes.

The proof is the one in the source. By Stacks 03AS, the Čech complex of a presheaf `F` is
the complex of morphisms from the integral Čech complex into `F`; by Stacks 03AT the
integral Čech complex is exact in positive degrees. Mapping an exact complex into an
injective object preserves exactness, because `Hom(-, I)` is exact for injective `I`, so
the Čech complex of an injective presheaf is exact in positive degrees, which is the
vanishing of its cohomology there.

## Main results

* `Stacks.CechSite.injective_presheaf_cechCohomology_isZero`: the positive-degree Čech
  cohomology of an injective abelian presheaf vanishes.

## Implementation notes

This is the content of Stacks 03OR, whose home in the Stacks Project is the chapter on
cohomology of stacks rather than this one. It is proved here, next to the integral Čech
complex it is proved from, and it carries the tag. It used to be left untagged, on the view
that the tag belonged with the chapter that states it, and the chapter module held a one-line
restatement to carry it; that restatement was a duplicate of this theorem, so the tag moved
here, onto the declaration that covers the content.

The coefficient universe contains the object, morphism and family-index universes, so that
the free abelian presheaves making up the integral Čech complex live in the same presheaf
category as the injective object. The `ULift` applied to `I` in the proof is the
identification of the Čech complex of Stacks 03AM with the universe-lifted one appearing in
the comparison isomorphism of Stacks 03AS.

## References

* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
* [Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
-/

@[expose] public section

universe w v u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (I : Cᵒᵖ ⥤ AddCommGrpCat.{max w u' u v}) [Injective I]

/-- **Stacks Project, Tag 03OR.** The positive-degree Čech cohomology of an injective
presheaf of abelian groups vanishes. -/
@[stacks 03OR]
theorem injective_presheaf_cechCohomology_isZero (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E I p) := by
  have : (preadditiveYoneda.obj I).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj I).1 inferInstance
  have : (preadditiveYoneda.obj I).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hHom :
      ((homComplexFunctor.{v, u, max w u' u}
        (integralCechComplex.{w, v, u, max w u' u} E)).obj I).ExactAt p :=
    ShortComplex.Exact.map ((HomologicalComplex.exactAt_iff_isZero_homology _ p).2
      (integralCechComplex_homology_isZero.{w, v, u, max w u' u} E p hp)).op
      (preadditiveYoneda.obj I)
  let η : I ≅ I ⋙ AddCommGrpCat.uliftFunctor.{u, max v (max w u' u)} :=
    NatIso.ofComponents (fun _ => AddEquiv.ulift.symm.toAddCommGrpIso)
      (by intro U V f; ext x; rfl)
  have hLift' :
    ((cechComplexFunctor E).obj
        (I ⋙ AddCommGrpCat.uliftFunctor.{u, max v (max w u' u)})).ExactAt p := by
    simpa [liftedCechComplexFunctor, cechComplex] using hHom.of_iso
      ((homIntegralCechComplexIso.{w, v, u, max w u' u} E).app I)
  exact (hLift'.of_iso ((cechComplexFunctor E).mapIso η).symm).isZero_homology

end Stacks.CechSite

end
