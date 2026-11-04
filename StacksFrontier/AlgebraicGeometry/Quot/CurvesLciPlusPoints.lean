module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus

/-!
# Points of `Curves^{lci+}` are represented by proper curves over fields

A point of `|Curves^{lci+}|` is represented by a family of curves over the spectrum of a field
`k`. Its total space is a scheme `X` (Stacks 0ADD), proper of dimension at most one over `k`
(`AlgebraicGeometry.CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq`), and by Stacks 0DZX,
part (3), `X` is a local complete intersection over `k` smooth except at finitely many points.

This is stated in every algebraic stack `𝒳` identified with the category of families of curves
by an equivalence over the site, and specialized to the small model
`AlgebraicGeometry.curvesAlgebraicStack B hZ h`, which takes `h`, the algebraicity of the stack of
curves (Stacks 0D5A).

## Main results

* `exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus_of_equivalence`: every point
  of `|Curves^{lci+}| ⊆ |𝒳|` is the class of a field-valued point of `𝒳` mapping to the image of
  the family classifying a proper scheme over a field which is a local complete intersection
  smooth away from finitely many points.
* `exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus`: every point of
  `|Curves^{lci+}|` is the class of a field-valued point mapping to the point classifying a proper
  scheme over a field which is a local complete intersection smooth away from finitely many
  points.

## References

* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The points of `|Curves^{lci+}|` come from proper curves over fields**, in any algebraic
stack `𝒳` identified with the category of families of curves by an equivalence `E` over the site.
Every point `x` of `|Curves^{lci+}| ⊆ |𝒳|` is the class of a field-valued point `q` of `𝒳` whose
object maps to the image under `E` of the family classifying a proper scheme `X` of dimension at
most one over a field `k`, where `X` is a local complete intersection over `k` smooth except at
finitely many points (Stacks 0DZX, part (3)). -/
theorem exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus_of_equivalence
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ) (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (x : Stack.AlgebraicStacks.points B integerBase hZ 𝒳)
    (hx : x ∈ (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
      hE).1.pointSet B integerBase hZ) :
    ∃ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
      (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1),
      IsLocalCompleteIntersectionMorphism X.hom ∧ (X.hom.smoothLocus : Set X.left)ᶜ.Finite ∧
      ∃ q : Stack.FieldValuedPoint B integerBase hZ 𝒳.val.val,
        Stack.pointClass B integerBase hZ _ 𝒳.val.property q = x ∧
        Nonempty (q.obj ⟶ E.functor.obj (curveFamilyOfScheme X B hZ hk hdim)) := by
  obtain ⟨p, hp, rfl⟩ := (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ x).1 hx
  have hK := Stack.contains_spectrum_fieldValuedPoint B integerBase hZ p
  have hspec : Stack.spectrumSiteObject B integerBase hZ p = integerSiteObject B hZ hK :=
    congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  -- the family `F₀` of the object of `p`, over the base of `p`
  let F₀ : CurveFamily B hZ := E.inverse.obj p.obj
  let β : integerSiteObject B hZ hK ⟶ F₀.base :=
    eqToHom hspec.symm ≫ (Stack.spectrumSiteObjectIso B integerBase hZ p).hom ≫
      eqToHom p.over.symm ≫ 𝒳.val.val.p.map (E.counitIso.inv.app p.obj) ≫
      eqToHom (Functor.congr_obj hE F₀)
  -- its pullback `F` to the field spectrum of the site
  obtain ⟨F, ψ, hψ⟩ := (curvesFiberedCategory B hZ).property.exists_lift β F₀ rfl
  have hF : F.base = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq (curvesFiberedCategory B hZ).val.p β ψ
  obtain ⟨X, _, hdim, ⟨e⟩⟩ := CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq hK F hF
  -- the family `F` lies in `Curves^{lci+}`, hence so does the family of `X`
  have hFP : IsLciPlusFamily B hZ F := (isOpenCurvesLocus_lciPlus B hZ).prop_of_hom ψ
    ((curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse B hZ _ 𝒳 E hE p.obj).1 hp)
  have := (curvesLciPlus_isOpenSubstack B hZ).1
  obtain ⟨hlci, hfin⟩ := (isLciPlusFamily_curveFamilyOfScheme_iff B hZ _ hK X hdim).1
    (ObjectProperty.prop_of_iso (IsLciPlusFamily B hZ) e hFP)
  -- the field-valued point with object `E F` represents the same point as `p`
  let q : Stack.FieldValuedPoint B integerBase hZ 𝒳.val.val :=
    { carrier := p.carrier
      base := integerSiteObject B hZ hK
      isSpec := Iso.refl _
      obj := E.functor.obj F
      «over» := (Functor.congr_obj hE F).trans hF }
  exact ⟨p.carrier, inferInstance, hK, X, inferInstance, hdim, hlci, hfin, q,
    ((Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ p q).2
      ⟨q, ⟨E.functor.map ψ ≫ E.counitIso.hom.app p.obj⟩, ⟨𝟙 _⟩⟩).symm, ⟨E.functor.map e.hom⟩⟩

/-- **The points of `|Curves^{lci+}|` come from proper curves over fields.** Every point `x` of
`|Curves^{lci+}|` is the class of a field-valued point `q` of the small model of the stack of
curves whose object maps to the point classifying a proper scheme `X` of dimension at most one
over a field `k`, where `X` is a local complete intersection morphism over `k` smooth except at
finitely many points (Stacks 0DZX, part (3)). -/
theorem exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus
    (x : Stack.AlgebraicStacks.points B integerBase hZ (curvesAlgebraicStack B hZ h))
    (hx : x ∈ (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
      B integerBase hZ) :
    ∃ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
      (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1),
      IsLocalCompleteIntersectionMorphism X.hom ∧ (X.hom.smoothLocus : Set X.left)ᶜ.Finite ∧
      ∃ q : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val,
        Stack.pointClass B integerBase hZ _ (curvesAlgebraicStack B hZ h).val.property q = x ∧
        Nonempty (q.obj ⟶
          (curvesSmallEquivalence B hZ h).functor.obj (curveFamilyOfScheme X B hZ hk hdim)) :=
  exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h) x hx

end AlgebraicGeometry

end
