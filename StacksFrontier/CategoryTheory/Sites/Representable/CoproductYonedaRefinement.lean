module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc

/-!
# Refining a jointly locally surjective family of representable presheaves

A family of morphisms `f i : h_{U i} ⟶ X` of presheaves on a site is *jointly locally
surjective* when the induced morphism `∐ᵢ h_{U i} ⟶ X` is locally surjective, that is, when it
becomes an epimorphism after sheafification. Replacing each `U i` by a covering family of it
leaves the family jointly locally surjective, because the induced morphism of the two
coproducts is itself locally surjective.

## Main results

* `CategoryTheory.Presheaf.exists_sigmaι_app_eq`: a section of a coproduct of presheaves of
  types comes from one of the summands.
* `CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_refinement`: refining each member of a
  jointly locally surjective family of morphisms from representable presheaves by a covering
  family of its source leaves the family jointly locally surjective.

## Implementation notes

Local surjectivity of the comparison `∐_{i, j} h_{V i j} ⟶ ∐ᵢ h_{U i}` is proved directly: a
section of the target comes from one summand, and the covering sieve witnessing local
surjectivity of that summand's own coproduct morphism (Stacks 00WT) refines to one witnessing it
for the comparison. The conclusion is then local surjectivity of a composite.

## References

* [Stacks Project, Tag 00WT](https://stacks.math.columbia.edu/tag/00WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- A section of a coproduct of presheaves of types over an object of the site comes from one of
the summands: the coproduct of presheaves of types is computed objectwise. -/
theorem exists_sigmaι_app_eq {I : Type v} (F : I → Cᵒᵖ ⥤ Type v) (T : Cᵒᵖ) (s : (∐ F).obj T) :
    ∃ (i : I) (t : (F i).obj T), (Sigma.ι F i).app T t = s := by
  classical
  let e := sigmaObjIso F T ≪≫ Limits.Types.coproductIso fun i ↦ (F i).obj T
  rcases h : e.hom s with ⟨i, t⟩
  refine ⟨i, t, e.toEquiv.injective ?_⟩
  show e.hom ((Sigma.ι F i).app T t) = e.hom s
  rw [h]
  show ((Sigma.ι F i).app T ≫ e.hom) t = _
  simp [e]

/-- **Refining a jointly locally surjective family of morphisms from representable presheaves.**
If each source of such a family is covered by a family of morphisms of the site, the composites
again form a jointly locally surjective family. -/
theorem isLocallySurjective_sigmaDesc_refinement (J : GrothendieckTopology C) {I : Type v}
    (U : I → C) {X : Cᵒᵖ ⥤ Type v} (f : ∀ i, yoneda.obj (U i) ⟶ X)
    {K : I → Type v} (V : ∀ i, K i → C) (q : ∀ i j, V i j ⟶ U i)
    (hcover : ∀ i, Sieve.generate (Presieve.ofArrows (V i) (q i)) ∈ J (U i))
    (hlocal : IsLocallySurjective J (Sigma.desc f)) :
    IsLocallySurjective J
      (Sigma.desc fun ij : Σ i, K i ↦ yoneda.map (q ij.1 ij.2) ≫ f ij.1) := by
  classical
  let F : I → Cᵒᵖ ⥤ Type v := fun i ↦ yoneda.obj (U i)
  let G : (Σ i, K i) → Cᵒᵖ ⥤ Type v := fun ij ↦ yoneda.obj (V ij.1 ij.2)
  let r : (∐ G) ⟶ (∐ F) := Sigma.desc fun ij ↦ yoneda.map (q ij.1 ij.2) ≫ Sigma.ι F ij.1
  have hr : IsLocallySurjective J r := by
    refine ⟨fun {T} a ↦ ?_⟩
    obtain ⟨i, t, ht⟩ := exists_sigmaι_app_eq F (op T) a
    let ri : (∐ fun j ↦ yoneda.obj (V i j)) ⟶ yoneda.obj (U i) :=
      Sigma.desc fun j ↦ yoneda.map (q i j)
    have hri : IsLocallySurjective J ri := by
      simpa only [coprodYonedaDesc, ri] using
        isLocallySurjective_coprodYonedaDesc J (fun j ↦ V i j) (U i) (fun j ↦ q i j) (hcover i)
    refine J.superset_covering ?_ (hri.imageSieve_mem t)
    rintro W g ⟨s, hs⟩
    obtain ⟨j, v, hv⟩ := exists_sigmaι_app_eq (fun j ↦ yoneda.obj (V i j)) (op W) s
    have hqv : (yoneda.map (q i j)).app (op W) v = (yoneda.obj (U i)).map g.op t := by
      rw [← hv] at hs
      simpa only [← NatTrans.comp_app_apply, ri, Sigma.ι_desc] using hs
    refine ⟨(Sigma.ι G ⟨i, j⟩).app (op W) v, ?_⟩
    calc
      r.app (op W) ((Sigma.ι G ⟨i, j⟩).app (op W) v) =
          (Sigma.ι F i).app (op W) ((yoneda.map (q i j)).app (op W) v) := by
        simp only [← NatTrans.comp_app_apply, r, Sigma.ι_desc]
      _ = (∐ F).map g.op ((Sigma.ι F i).app (op T) t) := by
            rw [hqv]
            exact NatTrans.naturality_apply (Sigma.ι F i) g.op t
      _ = (∐ F).map g.op a := by rw [← ht]
  have hfactor : r ≫ Sigma.desc f =
      Sigma.desc fun ij : Σ i, K i ↦ yoneda.map (q ij.1 ij.2) ≫ f ij.1 :=
    Sigma.hom_ext _ _ fun ij ↦ by
      rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
  rw [← hfactor]
  infer_instance

end CategoryTheory.Presheaf

end
