module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartedFunctor
public import StacksFrontier.RingTheory.ChartedFunctor.Tangent
public import StacksFrontier.AlgebraicGeometry.Size.Affine

/-!
# Affine objects over `T'` as spectra of bounded algebras

Let `T'` be an object of the big fppf site of `S` with affine underlying scheme and `A' = Γ(T')`.
This file identifies the affine objects of the site which matter to the functor
`AlgebraicGeometry.Space.OverAffine.chartedFunctor` with spectra of bounded `A'`-algebras: `T'`
itself with `Spec A'`, an affine `V` over `T'` with `Spec Γ(V)`, and an affine `T` closed in `T'`
with `Spec(A' ⧸ I)`. Through these identifications a section of a presheaf `X` over `T` lying over
the closed immersion `T ⟶ T'` is a section of the functor over `A' ⧸ I`, and a section of the
functor over `A'` lying over it is an extension of the given section to `T'`.

## Main definitions

* `AlgebraicGeometry.Space.OverAffine.baseAlg`: `A'` as a bounded `A'`-algebra.
* `AlgebraicGeometry.Space.OverAffine.algOf`: the global sections of an affine object over `T'`.
* `AlgebraicGeometry.Space.OverAffine.thickeningIdeal`: the ideal `I ⊆ A'` cutting out `T`.
* `AlgebraicGeometry.Space.OverAffine.specQuotToObj`: the isomorphism `Spec(A' ⧸ I) ≅ T` over `T'`.

## Main results

* `AlgebraicGeometry.Space.OverAffine.exists_specOverMap_eq`: morphisms of spectra over `T'` come
  from algebra maps.
* `AlgebraicGeometry.Space.OverAffine.exists_extension_of_chartedFunctor`: extensions of sections
  from lifts of sections of the functor.
-/

@[expose] public section

open CategoryTheory Opposite Cardinal Limits Stacks.ChartedFunctor

universe u

namespace AlgebraicGeometry.Space.OverAffine


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The global sections of `T'`, as a bounded algebra over themselves. -/
noncomputable abbrev baseAlg : BoundedAlg (sectionsRing T') B.cutoff :=
  BoundedAlg.of (sectionsRing T') (by
    have h : ((BigFppfOver.toScheme B S hS).obj T').size < B.cutoff := T'.left.2
    rw [Scheme.size_of_isAffine] at h
    exact lt_of_le_of_lt (le_max_right _ _) h)

/-- The structure morphism `Spec Γ(T') ⟶ T'` is an isomorphism. -/
instance isIso_specOverToBase_baseAlg : IsIso (specOverToBase T' (baseAlg T')) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map (specOverToBase T' (baseAlg T'))) := by
    rw [toScheme_map_specOverToBase, specToBase]
    have h : IsIso (CommRingCat.ofHom (algebraMap (sectionsRing T') (baseAlg T').obj)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 Function.bijective_id
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@instIsIsoSchemeMapOfCommRingCat _ _ _ h) inferInstance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)


/-! ### Affine objects over `T'` as spectra of bounded algebras -/

section AffineOver

variable {T'} (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (v : V ⟶ T')

/-- The global sections of an affine object of the site have cardinality below the cutoff. -/
lemma mk_sections_lt : #Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) < B.cutoff := by
  have h : ((BigFppfOver.toScheme B S hS).obj V).size < B.cutoff := V.left.2
  rw [Scheme.size_of_isAffine] at h
  exact lt_of_le_of_lt (le_max_right _ _) h

/-- The global sections of an affine object `V` over `T'`, as a bounded algebra over `Γ(T')`. -/
noncomputable def algOf : BoundedAlg (sectionsRing T') B.cutoff :=
  ⟨chartAlgebra V v, mk_sections_lt V⟩

/-- The canonical morphism `Spec Γ(V) ⟶ V` over `T'`. -/
noncomputable def specAlgOfHom : specOver T' (algOf V v) ⟶ V :=
  chartHom (P := algOf V v) V v (𝟙 _)

/-- The morphism `Spec Γ(V) ⟶ V` composed with `v : V ⟶ T'` is the structure morphism
`Spec Γ(V) ⟶ T'`. -/
@[simp]
lemma specAlgOfHom_comp : specAlgOfHom V v ≫ v = specOverToBase T' (algOf V v) :=
  chartHom_comp V v _

/-- The canonical morphism `Spec Γ(V) ⟶ V` is an isomorphism. -/
instance isIso_specAlgOfHom : IsIso (specAlgOfHom V v) := by
  have h : IsIso (chartRingHom (P := algOf V v) V v (𝟙 _)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 Function.bijective_id
  have : IsIso ((BigFppfOver.toScheme B S hS).map (specAlgOfHom V v)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (@instIsIsoSchemeMapOfCommRingCat _ _ _ h) inferInstance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

end AffineOver

/-- **Morphisms of spectra over `T'` come from algebra maps.** -/
lemma exists_specOverMap_eq {P Q : BoundedAlg (sectionsRing T') B.cutoff}
    (z : specOver T' P ⟶ specOver T' Q) (hz : z ≫ specOverToBase T' Q = specOverToBase T' P) :
    ∃ m : Q ⟶ P, specOverMap T' m = z := by
  let zS : Spec (CommRingCat.of P.obj) ⟶ Spec (CommRingCat.of Q.obj) :=
    (BigFppfOver.toScheme B S hS).map z
  have hzS : zS ≫ specToBase T' Q = specToBase T' P :=
    ((BigFppfOver.toScheme B S hS).map_comp z _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map hz)
  let φ : CommRingCat.of Q.obj ⟶ CommRingCat.of P.obj := Spec.preimage zS
  have hφ : Spec.map φ = zS := Spec.map_preimage zS
  have hcomm : CommRingCat.ofHom (algebraMap (sectionsRing T') Q.obj) ≫ φ =
      CommRingCat.ofHom (algebraMap (sectionsRing T') P.obj) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    simpa only [specToBase, ← Category.assoc, cancel_mono] using hzS
  let m : Q.obj →ₐ[sectionsRing T'] P.obj :=
    { toRingHom := φ.hom
      commutes' := fun a => congrArg (fun k => k.hom a) hcomm }
  exact ⟨BoundedAlg.ofHom m, (BigFppfOver.toScheme B S hS).map_injective hφ⟩

/-- The cutoff of a big fppf site is uncountable. -/
instance fact_aleph0_lt_cutoff : Fact (ℵ₀ < B.cutoff) := ⟨B.aleph0_lt_cutoff⟩

variable {T'} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (i : T ⟶ T')

/-- The ideal of `Γ(T')` cutting out `T`. -/
noncomputable abbrev thickeningIdeal : Ideal (baseAlg T').obj :=
  RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom

variable [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- A closed immersion of affine objects is surjective on global sections. -/
lemma surjective_appTop_of_isClosedImmersion :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map i).appTop.hom :=
  Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)

/-- `Γ(T) ≅ Γ(T') ⧸ I` for the closed immersion `T ⟶ T'` of affines. -/
noncomputable def sectionsEquivQuot :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≃+* (quot (baseAlg T') (thickeningIdeal i)).obj :=
  (RingHom.quotientKerEquivOfSurjective (surjective_appTop_of_isClosedImmersion i)).symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The restriction `Γ(T') ⟶ Γ(T)` followed by `Γ(T) ≅ Γ(T') ⧸ I` is the quotient map
`Γ(T') ⟶ Γ(T') ⧸ I`. -/
lemma appTop_comp_sectionsEquivQuot :
    ((BigFppfOver.toScheme B S hS).map i).appTop ≫
      CommRingCat.ofHom (sectionsEquivQuot i).toRingHom =
    CommRingCat.ofHom
      (algebraMap (sectionsRing T') (quot (baseAlg T') (thickeningIdeal i)).obj) := by
  ext a
  exact (RingEquiv.symm_apply_eq _).2
    (RingHom.quotientKerEquivOfSurjective_apply_mk
      (surjective_appTop_of_isClosedImmersion i) a).symm

/-- The scheme isomorphism `Spec(Γ(T') ⧸ I) ≅ T`. -/
noncomputable def specQuotToSchemeHom :
    Spec (CommRingCat.of (quot (baseAlg T') (thickeningIdeal i)).obj) ⟶
      (BigFppfOver.toScheme B S hS).obj T :=
  Spec.map (CommRingCat.ofHom (sectionsEquivQuot i).toRingHom) ≫
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv

/-- The isomorphism `Spec(Γ(T') ⧸ I) ≅ T` followed by `T ⟶ T'` is the structure morphism
`Spec(Γ(T') ⧸ I) ⟶ T'`. -/
lemma specQuotToSchemeHom_comp :
    specQuotToSchemeHom i ≫ (BigFppfOver.toScheme B S hS).map i =
      specToBase T' (quot (baseAlg T') (thickeningIdeal i)) := by
  rw [specQuotToSchemeHom, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, appTop_comp_sectionsEquivQuot]
  rfl

/-- The isomorphism `Spec(Γ(T') ⧸ I) ≅ T` as a morphism of the site. -/
noncomputable def specQuotToObj : specOver T' (quot (baseAlg T') (thickeningIdeal i)) ⟶ T :=
  Over.homMk (ObjectProperty.homMk (specQuotToSchemeHom i)) (by
    apply ObjectProperty.hom_ext
    change specQuotToSchemeHom i ≫ B.inclusion.map T.hom =
      specToBase T' _ ≫ B.inclusion.map T'.hom
    rw [← specQuotToSchemeHom_comp i, Category.assoc]
    congr 1
    change _ = B.inclusion.map (i.left ≫ T'.hom)
    rw [Over.w])

/-- The morphism `Spec(Γ(T') ⧸ I) ⟶ T` of the site followed by `i : T ⟶ T'` is the structure
morphism `Spec(Γ(T') ⧸ I) ⟶ T'`. -/
lemma specQuotToObj_comp : specQuotToObj i ≫ i = specOverToBase T' _ :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp]
    exact specQuotToSchemeHom_comp i)

/-- The morphism `Spec(Γ(T') ⧸ I) ⟶ T` of the site is an isomorphism. -/
instance isIso_specQuotToObj : IsIso (specQuotToObj i) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map (specQuotToObj i)) := by
    change IsIso (specQuotToSchemeHom i)
    rw [specQuotToSchemeHom]
    have h : IsIso (CommRingCat.ofHom (sectionsEquivQuot i).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (sectionsEquivQuot i).bijective
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@instIsIsoSchemeMapOfCommRingCat _ _ _ h)
      inferInstance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

/-- **Section extension from the functor on algebras.** Let `p : X ⟶ h_{T'}` and `i : T ⟶ T'` a
closed immersion of affine objects of the site. If every section of the functor attached to `p`
over `Γ(T') ⧸ I` lifts to a section over `Γ(T')`, then every section `x` of `X` over `T` lying
over `i` extends to a section of `X` over `T'` lying over the identity. -/
theorem exists_extension_of_chartedFunctor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : X ⟶ yoneda.obj T')
    (H : ∀ x' : (chartedFunctor T' X p).obj (quot (baseAlg T') (thickeningIdeal i)),
      ∃ ξ : (chartedFunctor T' X p).obj (baseAlg T'),
        (chartedFunctor T' X p).map (quotMk (baseAlg T') (thickeningIdeal i)) ξ = x')
    (x : X.obj (op T)) (hx : p.app _ x = i) :
    ∃ z : X.obj (op T'), X.map i.op z = x ∧ p.app _ z = 𝟙 T' := by
  let e := specQuotToObj i
  let e' := specOverToBase T' (baseAlg T')
  have hx' : p.app _ (X.map e.op x) = specOverToBase T' _ := by
    rw [NatTrans.naturality_apply, hx]
    exact specQuotToObj_comp i
  obtain ⟨ξ, hξ⟩ := H ⟨X.map e.op x, hx'⟩
  refine ⟨X.map (inv e').op ξ.1, ?_, ?_⟩
  · have hξ' : X.map (specOverMap T' (quotMk (baseAlg T') (thickeningIdeal i))).op ξ.1 =
        X.map e.op x := congrArg Subtype.val hξ
    have hsq : i ≫ inv e' = inv e ≫ specOverMap T' (quotMk (baseAlg T') (thickeningIdeal i)) := by
      rw [IsIso.comp_inv_eq, Category.assoc, specOverMap_comp_specOverToBase, IsIso.eq_inv_comp,
        specQuotToObj_comp]
    calc X.map i.op (X.map (inv e').op ξ.1) = X.map (i ≫ inv e').op ξ.1 := by
          rw [op_comp, FunctorToTypes.map_comp_apply]
      _ = X.map (inv e).op (X.map e.op x) := by
          rw [hsq, op_comp, FunctorToTypes.map_comp_apply, hξ']
      _ = x := by
          rw [← FunctorToTypes.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
            FunctorToTypes.map_id_apply]
  · rw [NatTrans.naturality_apply, ξ.2]
    exact IsIso.inv_hom_id e'

end AlgebraicGeometry.Space.OverAffine

end
