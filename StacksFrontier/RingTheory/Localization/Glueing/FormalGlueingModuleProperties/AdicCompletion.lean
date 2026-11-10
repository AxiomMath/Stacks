module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties.PrincipalLocalization

/-!
# Formal glueing of finitely generated modules along an adic completion

## Main definitions

* `FormalGlueing.finiteExtensionOfScalars`: extension of scalars on finitely generated modules.
* `FormalGlueing.adicCompletionFunctor`: adic completion as a functor on module categories.
* `FormalGlueing.finiteAdicCompletion`: adic completion restricted to finitely generated modules
  over a Noetherian ring.

## Main results

* `FormalGlueing.exists_adicCompletionGlueingEquivalence`: the canonical equivalence from
  finitely generated modules to the categorical pullback of the two localized module categories.

## Implementation notes

In the adic setting the comparison is normalized on the images of elements of the original
module; the functors allow independent ring and module universes, and the tensor-product
comparison uses a module universe containing the completed ring.

## References

* [Stacks Project, Tag 05ET](https://stacks.math.columbia.edu/tag/05ET)
-/

/-! ### Formal glueing of finitely generated modules along an adic completion -/

section

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- Extension of scalars, restricted to finitely generated modules. -/
public noncomputable def finiteExtensionOfScalars
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    FGModuleCat.{max v w} R ⥤ FGModuleCat.{max v w} S where
  obj M := FGModuleCat.of S (TensorProduct R S M)
  map g := FGModuleCat.ofHom (g.hom.hom.baseChange S)
  map_id M := by
    apply FGModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp g h := by
    apply FGModuleCat.hom_ext
    exact LinearMap.baseChange_comp _ _

/-- Adic completion of modules, functorial for linear maps. -/
public noncomputable def adicCompletionFunctor
    (R : Type u) [CommRing R] (I : Ideal R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (AdicCompletion I R) where
  obj M := ModuleCat.of _ (AdicCompletion I M)
  map g := ModuleCat.ofHom (AdicCompletion.map I g.hom)
  map_id M := by ext; simp
  map_comp g h := by ext; simp

/-- The canonical tensor equivalence with independent ring and module universes. Shrinking is
used only to apply Mathlib's same-universe bijectivity result. -/
public noncomputable def adicCompletionTensorEquiv
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TensorProduct R (AdicCompletion I R) M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct I M) (by
    have : Small.{u} M := Module.Finite.small R M
    let e := Shrink.linearEquiv R M
    apply (Function.Bijective.of_comp_iff _
      (e.baseChange R (AdicCompletion I R) (Shrink.{u} M) M).bijective).mp
    change Function.Bijective
      (AdicCompletion.ofTensorProduct I M ∘ₗ e.toLinearMap.baseChange (AdicCompletion I R))
    rw [LinearMap.baseChange, ← AdicCompletion.ofTensorProduct_naturality]
    exact (AdicCompletion.congr I e).bijective.comp
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (Shrink.{u} M)).bijective)

/-- Adic completion, restricted to finitely generated modules over a Noetherian ring. -/
public noncomputable def finiteAdicCompletion
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    FGModuleCat.{v} R ⥤ FGModuleCat.{v} (AdicCompletion I R) :=
  (ModuleCat.isFG (AdicCompletion I R)).lift
    ((ModuleCat.isFG R).ι ⋙ adicCompletionFunctor R I)
    (fun M ↦ by
      rw [ModuleCat.isFG_iff]
      let _ : Module.Finite R M.obj := M.property
      exact Module.Finite.equiv
        (adicCompletionTensorEquiv R I M.obj))

/-- The canonical identification of finite adic completion with extension of scalars, as in
Stacks 00MA. Its inverse is `AdicCompletion.ofTensorProduct`, with bijectivity supplied by
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
@[ega "0 7.3.3", ega "0 7.7.8" "special case"]
public noncomputable def finiteAdicCompletionIsoExtensionOfScalars
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    finiteAdicCompletion.{u, max u v} R I ≅
      finiteExtensionOfScalars.{u, u, v} R (AdicCompletion I R) :=
  (NatIso.ofComponents
    (fun M ↦ by
      let _ : Module.Finite (AdicCompletion I R) (AdicCompletion I M) :=
        ((finiteAdicCompletion R I).obj M).property
      exact (adicCompletionTensorEquiv R I M).toFGModuleCatIso)
    (fun {M N} g ↦ by
      apply FGModuleCat.hom_ext
      exact (AdicCompletion.ofTensorProduct_naturality I g.hom.hom).symm)).symm

/-- The canonical completion comparison sends the image of `m` to `1 ⊗ₜ m`. -/
@[simp]
public theorem finiteAdicCompletionIsoExtensionOfScalars_hom_app_of
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : FGModuleCat.{max u v} R) (m : M) :
    (finiteAdicCompletionIsoExtensionOfScalars R I).hom.app M (AdicCompletion.of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  change (adicCompletionTensorEquiv R I M).symm (AdicCompletion.of I M m) = _
  apply (adicCompletionTensorEquiv R I M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (one_smul (AdicCompletion I R) (AdicCompletion.of I M m)).symm

/-- The inverse comparison is the canonical map from the tensor product to the completion. -/
@[simp]
public theorem finiteAdicCompletionIsoExtensionOfScalars_inv_app_tmul
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : FGModuleCat.{max u v} R) (r : AdicCompletion I R) (m : M) :
    (finiteAdicCompletionIsoExtensionOfScalars R I).inv.app M (r ⊗ₜ[R] m) =
      r • AdicCompletion.of I M m :=
  rfl

end FormalGlueing
end

end

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace FormalGlueing

universe u v w

/-- Scalar extension expressed using the supplied algebra action. -/
private noncomputable def extendScalarsOfAlgebra (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] :
    ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} S where
  obj M := ModuleCat.of S (TensorProduct R S M)
  map g := ModuleCat.ofHom (g.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.baseChange_comp _ _)

private theorem extendScalars_eq_extendScalarsOfAlgebra (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] :
    ModuleCat.extendScalars.{u,v,max v w} (algebraMap R S) =
      extendScalarsOfAlgebra.{u,v,w} R S := by
  have h : ModuleCat.extendScalars.{u,v,max v w} (algebraMap R S) =
      @extendScalarsOfAlgebra.{u,v,w} R S _ _ (algebraMap R S).toAlgebra := by
    apply CategoryTheory.Functor.hext
    · intro M; rfl
    · intro M N g
      apply heq_of_eq
      apply ModuleCat.hom_ext
      ext x
      rfl
  rw [h, toAlgebra_algebraMap]

private theorem isFG_extendScalarsOfAlgebra (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (M : FGModuleCat.{max v w} R) :
    ModuleCat.isFG S ((extendScalarsOfAlgebra R S).obj M.obj) :=
  inferInstanceAs (Module.Finite S (TensorProduct R S M))

private theorem exists_fg_baseChange_surjective
    {R : Type u} {S : Type v} {M : Type w} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module.Finite S (TensorProduct R S M)] :
    ∃ N : Submodule R M, N.FG ∧
      Function.Surjective (N.subtype.baseChange S) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := TensorProduct R S M)
  obtain ⟨N, hN, h⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (s : Set (TensorProduct R S M)) s.finite_toSet
  refine ⟨N, Module.Finite.iff_fg.mp hN, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  exact h

private theorem baseChange_subtype_surjective_of_le
    {R : Type u} {S : Type v} {M : Type w} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] {N P : Submodule R M} (h : N ≤ P)
    (hs : Function.Surjective (N.subtype.baseChange S)) :
    Function.Surjective (P.subtype.baseChange S) := by
  have he : N.subtype = P.subtype.comp (Submodule.inclusion h) := rfl
  rw [he, LinearMap.baseChange_comp] at hs
  exact Function.Surjective.of_comp hs

private theorem finite_of_faithful_glueing
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    {C : Type*} [Category C] (F : ModuleCat.{u} S ⥤ C) (G : ModuleCat.{u} T ⥤ C)
    (e : extendScalarsOfAlgebra R S ⋙ F ≅
      extendScalarsOfAlgebra R T ⋙ G)
    (hf : ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      F G (ModuleCat.{u} R)).obj
      ⟨extendScalarsOfAlgebra R S,
        extendScalarsOfAlgebra R T, e⟩).Faithful)
    (M : ModuleCat.{u} R)
    [Module.Finite S (TensorProduct R S M)] [Module.Finite T (TensorProduct R T M)] :
    Module.Finite R M := by
  obtain ⟨N, hN, hs⟩ := exists_fg_baseChange_surjective (R := R) (S := S) (M := M)
  obtain ⟨P, hP, ht⟩ := exists_fg_baseChange_surjective (R := R) (S := T) (M := M)
  let Q := N ⊔ P
  have : Module.Finite R Q := Module.Finite.iff_fg.mpr (hN.sup hP)
  let i : ModuleCat.of R Q ⟶ M := ModuleCat.ofHom Q.subtype
  let H := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      F G (ModuleCat.{u} R)).obj
      ⟨extendScalarsOfAlgebra R S,
        extendScalarsOfAlgebra R T, e⟩
  have : H.Faithful := hf
  have : Epi (H.map i).fst := (ModuleCat.epi_iff_surjective _).mpr
    (baseChange_subtype_surjective_of_le (S := S) le_sup_left hs)
  have : Epi (H.map i).snd := (ModuleCat.epi_iff_surjective _).mpr
    (baseChange_subtype_surjective_of_le (S := T) le_sup_right ht)
  have : Epi (H.map i) := ⟨fun g h eq ↦ by
    apply CategoricalPullback.hom_ext
    · apply (cancel_epi (H.map i).fst).mp
      exact congrArg CategoricalPullback.Hom.fst eq
    · apply (cancel_epi (H.map i).snd).mp
      exact congrArg CategoricalPullback.Hom.snd eq⟩
  have : Epi i := H.epi_of_epi_map inferInstance
  exact Module.Finite.of_surjective Q.subtype ((ModuleCat.epi_iff_surjective i).mp inferInstance)

section Restriction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  (P : ObjectProperty A) (Q : ObjectProperty B) (T : ObjectProperty C)
  (F : A ⥤ C) (G : B ⥤ C)
  (hF : ∀ X : P.FullSubcategory, T (F.obj X.obj))
  (hG : ∀ X : Q.FullSubcategory, T (G.obj X.obj))

private def pullbackInclusion :
    CategoricalPullback (T.lift (P.ι ⋙ F) hF) (T.lift (Q.ι ⋙ G) hG) ⥤
      CategoricalPullback F G where
  obj X := ⟨X.fst.obj, X.snd.obj, T.ι.mapIso X.iso⟩
  map f := ⟨f.fst.hom, f.snd.hom, congrArg (fun g ↦ g.hom) f.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private def pullbackInclusionFullyFaithful :
    (pullbackInclusion P Q T F G hF hG).FullyFaithful where
  preimage f := ⟨ObjectProperty.homMk f.fst, ObjectProperty.homMk f.snd,
    ObjectProperty.hom_ext _ f.w⟩

variable (U : ObjectProperty D) (K : D ⥤ A) (L : D ⥤ B)
  (hK : ∀ X : U.FullSubcategory, P (K.obj X.obj))
  (hL : ∀ X : U.FullSubcategory, Q (L.obj X.obj))
  (e : K ⋙ F ≅ L ⋙ G)

private def restrictedComparison :
    P.lift (U.ι ⋙ K) hK ⋙ T.lift (P.ι ⋙ F) hF ≅
      Q.lift (U.ι ⋙ L) hL ⋙ T.lift (Q.ι ⋙ G) hG :=
  NatIso.ofComponents (fun X ↦ T.isoMk (e.app X.obj))
    (fun f ↦ ObjectProperty.hom_ext _ (e.hom.naturality f.hom))

private theorem restricted_isEquivalence
    (he : ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback F G D).obj
      ⟨K, L, e⟩).IsEquivalence)
    (hdetect : ∀ X, P (K.obj X) → Q (L.obj X) → U X)
    (hP : ∀ {X Y}, (X ≅ Y) → P Y → P X)
    (hQ : ∀ {X Y}, (X ≅ Y) → Q Y → Q X) :
    ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (T.lift (P.ι ⋙ F) hF) (T.lift (Q.ι ⋙ G) hG) U.FullSubcategory).obj
        ⟨P.lift (U.ι ⋙ K) hK, Q.lift (U.ι ⋙ L) hL,
          restrictedComparison P Q T F G hF hG U K L hK hL e⟩).IsEquivalence := by
  let J := pullbackInclusion P Q T F G hF hG
  let H := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback F G D).obj
    ⟨K, L, e⟩
  let H' := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (T.lift (P.ι ⋙ F) hF) (T.lift (Q.ι ⋙ G) hG) U.FullSubcategory).obj
        ⟨P.lift (U.ι ⋙ K) hK, Q.lift (U.ι ⋙ L) hL,
          restrictedComparison P Q T F G hF hG U K L hK hL e⟩
  have : H.IsEquivalence := he
  have : J.Full := (pullbackInclusionFullyFaithful P Q T F G hF hG).full
  have : J.Faithful := (pullbackInclusionFullyFaithful P Q T F G hF hG).faithful
  have comm : H' ⋙ J ≅ U.ι ⋙ H := Iso.refl _
  have : H'.Full := Functor.Full.of_comp_faithful_iso comm
  have : H'.Faithful := Functor.Faithful.of_comp_iso comm
  have : H'.EssSurj := ⟨fun X ↦ by
    let Y := H.objPreimage (J.obj X)
    let i := H.objObjPreimageIso (J.obj X)
    have hy : U Y := hdetect Y
      (hP ((CategoricalPullback.π₁ F G).mapIso i) X.fst.property)
      (hQ ((CategoricalPullback.π₂ F G).mapIso i) X.snd.property)
    exact ⟨⟨Y, hy⟩, ⟨J.preimageIso i⟩⟩⟩
  exact { }

end Restriction

private abbrev HasCanonicalTensorGlueingEquivalence (R S T V : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing V]
    [Algebra R S] [Algebra R T] [Algebra S V] [Algebra T V] : Prop :=
    ∃ e : extendScalarsOfAlgebra R S ⋙ extendScalarsOfAlgebra S V ≅
        extendScalarsOfAlgebra R T ⋙ extendScalarsOfAlgebra T V,
      (∀ (M : ModuleCat.{u} R) (m : M),
        e.hom.app M ((1 : V) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) =
        (1 : V) ⊗ₜ[T] ((1 : T) ⊗ₜ[R] m)) ∧
      ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
        (extendScalarsOfAlgebra S V) (extendScalarsOfAlgebra T V) (ModuleCat.{u} R)).obj
        ⟨extendScalarsOfAlgebra R S, extendScalarsOfAlgebra R T, e⟩).IsEquivalence


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Stacks 05ET.** Over a Noetherian ring, finitely generated modules are equivalent to
finitely generated modules on the adic completion and on the complementary principal open,
identified over their common localization. -/
@[stacks 05ET]
public theorem exists_adicCompletionGlueingEquivalence
    (R : Type u) [CommRing R] [IsNoetherianRing R] (f : R) :
    let I := Ideal.span {f}
    let Rhat := AdicCompletion I R
    let Rf := Localization.Away f
    let Sf := Localization.Away (algebraMap R Rhat f)
    let ρ := FormalGlueing.principalLocalizationMap R Rhat f
    letI : Algebra Rf Sf := ρ.toAlgebra
    let completion := finiteAdicCompletion R I
    let localPiece := finiteExtensionOfScalars R Rf
    let completionOverlap := finiteExtensionOfScalars Rhat Sf
    let localOverlap := finiteExtensionOfScalars Rf Sf
    ∃ comparison : completion ⋙ completionOverlap ≅ localPiece ⋙ localOverlap,
      (∀ (M : FGModuleCat.{u} R) (m : M) (s : Sf),
        comparison.hom.app M
            (s ⊗ₜ[Rhat] AdicCompletion.of I M m) =
          s ⊗ₜ[Rf] ((1 : Rf) ⊗ₜ[R] m)) ∧
      ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
        completionOverlap localOverlap (FGModuleCat.{u} R)).obj
        { fst := completion
          snd := localPiece
          iso := comparison }).IsEquivalence := by
  let I := Ideal.span {f}
  let S := AdicCompletion I R
  let Rf := Localization.Away f
  let Sf := Localization.Away (algebraMap R S f)
  let : Algebra Rf Sf := (FormalGlueing.principalLocalizationMap R S f).toAlgebra
  have h : HasCanonicalTensorGlueingEquivalence R S Rf Sf := by
    have h := FormalGlueing.exists_canonicalModuleGlueingEquivalence.{u,u,u}
      R S f (AdicCompletion.flat_of_isNoetherian I)
      (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing)
    change @HasCanonicalTensorGlueingEquivalence R S Rf Sf _ _ _ _
      (algebraMap R S).toAlgebra (algebraMap R Rf).toAlgebra
      (algebraMap S Sf).toAlgebra (algebraMap Rf Sf).toAlgebra at h
    simpa +instances only [toAlgebra_algebraMap] using h
  obtain ⟨e, hc, he⟩ := h
  let efin : finiteExtensionOfScalars R S ⋙ finiteExtensionOfScalars S Sf ≅
      finiteExtensionOfScalars R Rf ⋙ finiteExtensionOfScalars Rf Sf :=
    restrictedComparison (ModuleCat.isFG S) (ModuleCat.isFG Rf) (ModuleCat.isFG Sf)
      (extendScalarsOfAlgebra S Sf) (extendScalarsOfAlgebra Rf Sf)
      (isFG_extendScalarsOfAlgebra S Sf) (isFG_extendScalarsOfAlgebra Rf Sf)
      (ModuleCat.isFG R) (extendScalarsOfAlgebra R S) (extendScalarsOfAlgebra R Rf)
      (isFG_extendScalarsOfAlgebra R S) (isFG_extendScalarsOfAlgebra R Rf) e
  have hef : ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (finiteExtensionOfScalars S Sf) (finiteExtensionOfScalars Rf Sf)
      (FGModuleCat.{u} R)).obj
      ⟨finiteExtensionOfScalars R S, finiteExtensionOfScalars R Rf, efin⟩).IsEquivalence := by
    apply restricted_isEquivalence (ModuleCat.isFG S) (ModuleCat.isFG Rf)
      (ModuleCat.isFG Sf) (extendScalarsOfAlgebra S Sf) (extendScalarsOfAlgebra Rf Sf)
      (isFG_extendScalarsOfAlgebra S Sf) (isFG_extendScalarsOfAlgebra Rf Sf)
      (ModuleCat.isFG R) (extendScalarsOfAlgebra R S) (extendScalarsOfAlgebra R Rf)
      (isFG_extendScalarsOfAlgebra R S) (isFG_extendScalarsOfAlgebra R Rf) e he
    · intro M hS hRf
      let H := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
        (extendScalarsOfAlgebra S Sf) (extendScalarsOfAlgebra Rf Sf) (ModuleCat.{u} R)).obj
        ⟨extendScalarsOfAlgebra R S, extendScalarsOfAlgebra R Rf, e⟩
      have : H.IsEquivalence := he
      have : Module.Finite S (TensorProduct R S M) := hS
      have : Module.Finite Rf (TensorProduct R Rf M) := hRf
      exact finite_of_faithful_glueing (extendScalarsOfAlgebra S Sf) (extendScalarsOfAlgebra Rf Sf)
        e (inferInstanceAs H.Faithful) M
    all_goals
      intro X Y i hY
      exact (Module.Finite.equiv_iff i.symm.toLinearEquiv).mp hY
  let c := CategoryTheory.Functor.isoWhiskerRight (finiteAdicCompletionIsoExtensionOfScalars R I)
    (finiteExtensionOfScalars S Sf) ≪≫ efin
  refine ⟨c, ?_, ?_⟩
  · intro M m s
    change e.hom.app M.obj (s ⊗ₜ[S]
      ((finiteAdicCompletionIsoExtensionOfScalars R I).hom.app M
        (AdicCompletion.of I M m))) = _
    rw [finiteAdicCompletionIsoExtensionOfScalars_hom_app_of]
    let φ : TensorProduct S Sf (TensorProduct R S M) →ₗ[Sf]
        TensorProduct Rf Sf (TensorProduct R Rf M) := (e.hom.app M.obj).hom
    change φ (s ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) = _
    have hc' : φ ((1 : Sf) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) =
        (1 : Sf) ⊗ₜ[Rf] ((1 : Rf) ⊗ₜ[R] m) := hc M.obj m
    simpa only [← φ.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      congrArg (fun x : TensorProduct Rf Sf (TensorProduct R Rf M) ↦ s • x) hc'
  · let T := CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (finiteExtensionOfScalars S Sf) (finiteExtensionOfScalars Rf Sf) (FGModuleCat.{u} R)
    have i : (T.obj ⟨finiteAdicCompletion R I, finiteExtensionOfScalars R Rf, c⟩) ≅
        T.obj ⟨finiteExtensionOfScalars R S, finiteExtensionOfScalars R Rf, efin⟩ :=
      T.mapIso (CategoricalPullback.CatCommSqOver.mkIso
        (finiteAdicCompletionIsoExtensionOfScalars R I) (Iso.refl _)
        (by simp [c]; rfl))
    have : (T.obj ⟨finiteExtensionOfScalars R S,
      finiteExtensionOfScalars R Rf, efin⟩).IsEquivalence := hef
    exact CategoryTheory.Functor.isEquivalence_of_iso i.symm

end FormalGlueing

end


end
