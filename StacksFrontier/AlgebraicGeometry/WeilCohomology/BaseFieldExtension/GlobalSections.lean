module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Graded
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Divisor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange

/-!
# Axiom (A8) descends along a field extension

For a smooth projective scheme `X` over `k` and a field extension `k'/k`, the spectrum of
`Γ(X_{k'}, 𝒪)` is the base change of the spectrum of `Γ(X, 𝒪)`, compatibly with the canonical
morphisms `X ⟶ Spec Γ(X, 𝒪)` (flat base change for `H^0` of the structure sheaf, Tag 02KH,
`AlgebraicGeometry.isPullback_specMap_appTop_of_flat`). Through the comparison isomorphisms of
Tag 0FVT this makes axiom (A8) for `(H')^*` imply axiom (A8) for `H^*`, by the linear algebra of
the proof of axiom (A1): an `F`-linear map is bijective once its extension of scalars to `F'` is.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.specGlobalSectionsBaseChangeIso`:
  `Spec Γ(X_{k'}, 𝒪) ≅ (Spec Γ(X, 𝒪))_{k'}`.

## Main results

* `toSpecGlobalSections_comp_specGlobalSectionsBaseChangeIso_hom`: the isomorphism is
  compatible with the canonical morphisms.
* `Stacks.WeilCohomology.FieldExtensionComparison.globalSectionsAxiom`: **axiom (A8) descends**.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The structure morphism of `Spec Γ(X, 𝒪_X)` over `k` is `Spec Γ(X, 𝒪_X) ⟶ Spec Γ(Spec k, 𝒪)
= Spec k`. -/
theorem specΓToBase_eq (X : (SmoothProjectiveScheme k).FullSubcategory) :
    specΓToBase X.obj.hom = (specGlobalSections X).obj.hom := by
  rw [specΓToBase, Scheme.isoSpec_Spec_inv]
  change _ = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop)
  rw [Spec.map_comp]

variable (k') in
/-- **`Spec Γ(X_{k'}, 𝒪) = Spec Γ(X, 𝒪) ×_{Spec k} Spec k'`** (flat base change in degree zero). -/
theorem isPullback_specGlobalSections (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback (Spec.map (baseChangeProj (k' := k') X).appTop)
      (specGlobalSections ((baseChange k k').obj X)).obj.hom
      (specGlobalSections X).obj.hom (ArtinSchreier.specExt k k') := by
  have := (isProjective X).isProper
  have : QuasiSeparatedSpace ((toScheme k).obj X) :=
    quasiSeparatedSpace_of_quasiSeparated X.obj.hom
  have H := isPullback_specMap_appTop_of_flat (isPullback_baseChangeProj (k' := k') X)
  rw [specΓToBase_eq] at H
  refine H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp)
    (by simp)
  simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact specΓToBase_eq ((baseChange k k').obj X)

/-- **`Spec Γ(X_{k'}, 𝒪) ≅ (Spec Γ(X, 𝒪))_{k'}`** as smooth projective schemes over `k'`. -/
def specGlobalSectionsBaseChangeIso (X : (SmoothProjectiveScheme k).FullSubcategory) :
    specGlobalSections ((baseChange k k').obj X) ≅
      (baseChange k k').obj (specGlobalSections X) where
  hom := homMk (isPullback_specGlobalSections k' X).isoPullback.hom
    (IsPullback.isoPullback_hom_snd _)
  inv := homMk (isPullback_specGlobalSections k' X).isoPullback.inv
    (IsPullback.isoPullback_inv_snd _)
  hom_inv_id := hom_ext' (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (isPullback_specGlobalSections k' X).isoPullback.hom_inv_id)
  inv_hom_id := hom_ext' (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (isPullback_specGlobalSections k' X).isoPullback.inv_hom_id)

/-- **The canonical morphisms commute with the base change**: `X_{k'} ⟶ Spec Γ(X_{k'}, 𝒪) ≅
(Spec Γ(X, 𝒪))_{k'}` is the base change of `X ⟶ Spec Γ(X, 𝒪)`. -/
theorem toSpecGlobalSections_comp_specGlobalSectionsBaseChangeIso_hom
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    toSpecGlobalSections ((baseChange k k').obj X) ≫ (specGlobalSectionsBaseChangeIso X).hom =
      (baseChange k k').map (toSpecGlobalSections X) := by
  apply hom_ext'
  rw [CategoryTheory.Functor.map_comp]
  apply (isPullback_baseChangeProj (k' := k') (specGlobalSections X)).hom_ext
  · rw [Category.assoc, baseChangeProj_naturality]
    change _ ≫ (isPullback_specGlobalSections k' X).isoPullback.hom ≫ pullback.fst _ _ = _
    rw [IsPullback.isoPullback_hom_fst]
    exact (Scheme.toSpecΓ_naturality _).symm
  · rw [Category.assoc, w, w, w]

end SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- Pullback along an isomorphism is bijective on each graded piece. -/
theorem bijective_pull_grade_of_iso {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (e : X ≅ Y) (n : ℤ) :
    Bijective fun a : 𝔇.grade Y n =>
      (⟨𝔇.pull e.hom a, 𝔇.pull_grade e.hom n a.1 a.2⟩ : 𝔇.grade X n) := by
  have hcomp : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} {f : X ⟶ Y}
      {g : Y ⟶ X}, f ≫ g = 𝟙 X → ∀ a : 𝔇.H X, 𝔇.pull f (𝔇.pull g a) = a := fun h a => by
    rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, h, 𝔇.pull_id]
    rfl
  refine ⟨fun a b hab => Subtype.ext ?_, fun b => ⟨⟨𝔇.pull e.inv b, 𝔇.pull_grade _ n _ b.2⟩,
    Subtype.ext (hcomp e.hom_inv_id b)⟩⟩
  simpa only [comp_apply, hcomp e.inv_hom_id] using
    congrArg (𝔇.pull e.inv ∘ Subtype.val) hab

end FirstChernClassData

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

open SmoothProjectiveScheme

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

include Φ in
/-- **Axiom (A8) descends**: if `(H')^0(Spec Γ(X', 𝒪)) ⟶ (H')^0(X')` is an isomorphism for every
smooth projective `X'` over `k'`, then `H^0(Spec Γ(X, 𝒪)) ⟶ H^0(X)` is an isomorphism for every
smooth projective `X` over `k`. -/
theorem globalSectionsAxiom (h : 𝔇'.GlobalSectionsAxiom) : 𝔇.GlobalSectionsAxiom := by
  intro X
  set X' := (baseChange k k').obj X
  set S := specGlobalSections X
  set e := specGlobalSectionsBaseChangeIso (k' := k') X
  let g : 𝔇.grade S 0 →ₗ[F] 𝔇.grade X 0 :=
    LinearMap.restrict (𝔇.pull (toSpecGlobalSections X)).toLinearMap
      fun a ha => 𝔇.pull_grade _ 0 a ha
  let g' : 𝔇'.grade ((baseChange k k').obj S) 0 → 𝔇'.grade X' 0 := fun a =>
    ⟨𝔇'.pull ((baseChange k k').map (toSpecGlobalSections X)) a, 𝔇'.pull_grade _ 0 a.1 a.2⟩
  have hg' : Bijective g' := by
    have : g' = (fun a : 𝔇'.grade (specGlobalSections X') 0 =>
        (⟨𝔇'.pull (toSpecGlobalSections X') a, 𝔇'.pull_grade _ 0 a.1 a.2⟩ : 𝔇'.grade X' 0)) ∘
        fun a : 𝔇'.grade ((baseChange k k').obj S) 0 =>
          (⟨𝔇'.pull e.hom a, 𝔇'.pull_grade e.hom 0 a.1 a.2⟩ : 𝔇'.grade _ 0) := by
      funext a
      refine Subtype.ext ?_
      simp only [g', Function.comp_apply,
        ← toSpecGlobalSections_comp_specGlobalSectionsBaseChangeIso_hom, 𝔇'.pull_comp,
        AlgHom.comp_apply]
      rfl
    rw [this]
    exact (h X').comp (𝔇'.bijective_pull_grade_of_iso e 0)
  have hcomm : ∀ x, Φ.gradeEquiv X 0 (g.baseChange F' x) = g' (Φ.gradeEquiv S 0 x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c a =>
      refine Subtype.ext ?_
      rw [LinearMap.baseChange_tmul, coe_gradeEquiv_tmul]
      simp only [g', coe_gradeEquiv_tmul]
      rw [Φ.iso_tmul X c, Φ.iso_tmul S c, map_smul]
      exact congrArg (c • ·) (Φ.iso_natural _ (a : 𝔇.H S))
    | add x y hx hy =>
      refine Subtype.ext ?_
      have hx' := congrArg Subtype.val hx
      have hy' := congrArg Subtype.val hy
      simp only [map_add, Submodule.coe_add, g'] at hx' hy' ⊢
      rw [hx', hy']
  have hb : Bijective (g.baseChange F') := by
    have : ⇑(g.baseChange F') = (Φ.gradeEquiv X 0).symm ∘ g' ∘ Φ.gradeEquiv S 0 := by
      funext x
      simp [← hcomm]
    rw [this]
    exact (Φ.gradeEquiv X 0).symm.bijective.comp (hg'.comp (Φ.gradeEquiv S 0).bijective)
  exact bijective_of_bijective_baseChange F' g hb

end FieldExtensionComparison

end Stacks.WeilCohomology
