module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.DecentSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Algebraic spaces over a field: extensions of the ground field

Let `S` be a scheme of a big fppf site with an isomorphism `e : S ≅ Spec k` to the spectrum of a
field. This file collects the facts about field-valued points and finite extensions of `k` used
in the proof that a decent group algebraic space locally of finite type over `k` is a scheme
(`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Representable`).

## Main definitions

* `AlgebraicGeometry.Space.GroupOverField.extObj`: the spectrum of an extension `K/k`, as an
  object of the big fppf site of `S`, and `AlgebraicGeometry.Space.GroupOverField.extMap` the
  morphism of such spectra attached to a `k`-algebra map.
* `AlgebraicGeometry.Space.GroupOverField.ptOf`: the field-valued point of a presheaf given by a
  morphism out of the presheaf represented by `Spec K`.
* `AlgebraicGeometry.Space.GroupOverField.pointAlgebra`: the `k`-algebra structure on the field
  of a field-valued point.

## Main results

* `AlgebraicGeometry.Space.GroupOverField.fibre_eq_ptOf`: if `M/k` is large enough to receive
  every embedding of the field `L` of a point `x` (for instance a normal extension into which `L`
  embeds), then every point of `X_M = h_M × X` over `x` is the `M`-rational point
  `(id, x ∘ τ)` for a `k`-embedding `τ : L → M`.
* `AlgebraicGeometry.Space.GroupOverField.exists_finite_point`: in an algebraic space locally of
  finite type over `k`, every nonempty locally closed set of points contains a point whose field
  is finite over `k`.
* `AlgebraicGeometry.Scheme.exists_dense_isOpen_forall_finite_isAffineOpen`: every scheme has a
  dense open subset in which every finite set of points lies in a common affine open.

## Implementation notes

Base change of a presheaf `X` on the big fppf site of `S` to an extension `K/k` is the product
`h_K × X`, `S` being terminal in its own big fppf site; so no change of site is involved, and
the projection `h_K × X ⟶ X` is a base change of the structure morphism of `Spec K`, which is
finite locally free and surjective when `K/k` is finite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space.GroupOverField

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Extensions of the ground field -/

variable {k : Type u} [Field k] (e : S ≅ Spec (.of k))

/-- The spectrum of an extension `K` of the ground field `k`, as an object of the big fppf site
of `S ≅ Spec k`. -/
noncomputable abbrev extObj (K : Type u) [Field K] [Algebra k K]
    (hK : C.Contains (Spec (.of K))) : BigFppfOver C S hS :=
  Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv⟩ : C.obj hK ⟶ C.obj hS)

/-- The morphism `Spec K' ⟶ Spec K` of the big fppf site of `S` attached to a `k`-algebra map
`K ⟶ K'`. -/
noncomputable def extMap {K K' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    {hK : C.Contains (Spec (.of K))} {hK' : C.Contains (Spec (.of K'))} (φ : K →ₐ[k] K') :
    extObj C S hS e K' hK' ⟶ extObj C S hS e K hK :=
  Over.homMk ⟨Spec.map (CommRingCat.ofHom φ.toRingHom)⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (algebraMap k K')) ≫ e.inv
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun x => φ.commutes x))

/-- `extMap` is functorial: `Spec` reverses composition. -/
theorem extMap_comp {K K' K'' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    [Field K''] [Algebra k K''] {hK : C.Contains (Spec (.of K))}
    {hK' : C.Contains (Spec (.of K'))} {hK'' : C.Contains (Spec (.of K''))}
    (φ : K →ₐ[k] K') (ψ : K' →ₐ[k] K'') :
    extMap C S hS e (hK := hK') (hK' := hK'') ψ ≫ extMap C S hS e (hK := hK) φ =
      extMap C S hS e (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- A morphism `Spec K' ⟶ Spec K` over `Spec k` is `Spec` of a `k`-algebra map. -/
private theorem exists_algHom_spec_map_eq {K K' : Type u} [Field K] [Algebra k K] [Field K']
    [Algebra k K'] (g : Spec (.of K') ⟶ Spec (.of K))
    (hw : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K'))) :
    ∃ β : K →ₐ[k] K', g = Spec.map (CommRingCat.ofHom β.toRingHom) := by
  have hc : CommRingCat.ofHom (algebraMap k K) ≫ Spec.preimage g =
      CommRingCat.ofHom (algebraMap k K') := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hw]
  exact ⟨⟨(Spec.preimage g).hom, fun x => congrArg (fun g => g.hom x) hc⟩,
    (Spec.map_preimage g).symm⟩

/-- Every morphism `Spec K' ⟶ Spec K` of the big fppf site of `S` is `Spec` of a `k`-algebra
map. -/
theorem exists_extMap_eq {K K' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    {hK : C.Contains (Spec (.of K))} {hK' : C.Contains (Spec (.of K'))}
    (φ : extObj C S hS e K' hK' ⟶ extObj C S hS e K hK) :
    ∃ β : K →ₐ[k] K', φ = extMap C S hS e β := by
  have hw : φ.left.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (algebraMap k K')) ≫ e.inv :=
    congrArg (fun g => g.hom) (Over.w φ)
  obtain ⟨β, hβ⟩ := exists_algHom_spec_map_eq φ.left.hom
    ((cancel_mono e.inv).mp (by simpa using hw))
  refine ⟨β, Over.OverMorphism.ext ?_⟩
  exact ObjectProperty.hom_ext _ hβ

/-- **Embeddings into a normal extension.** If `N/k` is normal and `L` embeds into `N` over `k`,
then every `k`-embedding of `L` into a field `Ω` receiving `N` factors through `N`. -/
theorem exists_comp_eq_of_normal {L N Ω : Type u} [Field L] [Field N] [Field Ω] [Algebra k L]
    [Algebra k N] [Algebra k Ω] [Algebra.IsAlgebraic k L] [Normal k N] (i : L →ₐ[k] N)
    (α : L →ₐ[k] Ω) (β : N →ₐ[k] Ω) : ∃ τ : L →ₐ[k] N, β.comp τ = α := by
  have hα : ∀ x, α x ∈ β.range := fun x => by
    have hint : _root_.IsIntegral k (α x) := (Algebra.IsIntegral.isIntegral x).map α
    refine hint.mem_range_algHom_of_minpoly_splits ?_ β
    rw [minpoly.algHom_eq α α.injective, ← minpoly.algHom_eq i i.injective]
    exact Normal.splits inferInstance (i x)
  refine ⟨(AlgEquiv.ofInjective β β.injective).symm.toAlgHom.comp (α.codRestrict β.range hα), ?_⟩
  ext x
  change β ((AlgEquiv.ofInjective β β.injective).symm ⟨α x, hα x⟩) = α x
  have := AlgEquiv.ofInjective_apply β β.injective
    ((AlgEquiv.ofInjective β β.injective).symm ⟨α x, hα x⟩)
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

/-- The field-valued point of a presheaf given by a morphism out of the presheaf represented by
`Spec K`. -/
noncomputable def ptOf (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) (K : Type u) [Field K]
    [Algebra k K] (hK : C.Contains (Spec (.of K))) (a : yoneda.obj (extObj C S hS e K hK) ⟶ F) :
    FieldValuedPoint C S hS F where
  carrier := K
  contained := hK
  toBase := Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv
  value := yonedaEquiv a

/-- Mapping `ptOf` along a morphism of presheaves composes the morphism. -/
theorem ptOf_map {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (K : Type u) [Field K]
    [Algebra k K] (hK : C.Contains (Spec (.of K))) (a : yoneda.obj (extObj C S hS e K hK) ⟶ F)
    (α : F ⟶ G) :
    (ptOf C S hS e F K hK a).map C S hS F α = ptOf C S hS e G K hK (a ≫ α) := by
  unfold ptOf FieldValuedPoint.map
  congr 1

/-- The class of `ptOf` does not change under an extension of the field. -/
theorem class_ptOf_extMap (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) {K K' : Type u} [Field K]
    [Algebra k K] [Field K'] [Algebra k K'] (hK : C.Contains (Spec (.of K)))
    (hK' : C.Contains (Spec (.of K'))) (φ : K →ₐ[k] K')
    (a : yoneda.obj (extObj C S hS e K hK) ⟶ F) :
    (ptOf C S hS e F K' hK' (yoneda.map (extMap C S hS e φ) ≫ a)).class C S hS F =
      (ptOf C S hS e F K hK a).class C S hS F := by
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS F
    ⟨_, FieldValuedPoint.dominates_refl C S hS F _, extMap C S hS e φ, ?_⟩
  change F.map (extMap C S hS e φ).op (yonedaEquiv a) = yonedaEquiv _
  rw [yonedaEquiv_naturality]

/-- The `k`-algebra structure on the field of a field-valued point, read off its structure
morphism to `S ≅ Spec k`. -/
noncomputable abbrev pointAlgebra {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint C S hS F) : Algebra k p.carrier :=
  (Spec.preimage (p.toBase ≫ e.hom)).hom.toAlgebra

/-- With the algebra structure `pointAlgebra`, the structure morphism of a field-valued point is
`Spec` of the algebra map followed by `e.inv`. -/
theorem toBase_eq_pointAlgebra {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint C S hS F) :
    letI := pointAlgebra C S hS e p
    p.toBase = Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) ≫ e.inv := by
  let := pointAlgebra C S hS e p
  change p.toBase = Spec.map (CommRingCat.ofHom (Spec.preimage (p.toBase ≫ e.hom)).hom) ≫ e.inv
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Every field-valued point has the class of a `ptOf` for the algebra structure of its
field. -/
theorem exists_ptOf {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint C S hS F) :
    letI := pointAlgebra C S hS e p
    ∃ a : yoneda.obj (extObj C S hS e p.carrier p.contained) ⟶ F,
      p.class C S hS F = (ptOf C S hS e F p.carrier p.contained a).class C S hS F := by
  let := pointAlgebra C S hS e p
  have h : extObj C S hS e p.carrier p.contained = p.siteObject C S hS F := by
    unfold extObj FieldValuedPoint.siteObject
    rw [← toBase_eq_pointAlgebra]
  refine ⟨yoneda.map (eqToHom h) ≫ yonedaEquiv.symm p.value, ?_⟩
  refine (FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS F
    ⟨_, FieldValuedPoint.dominates_refl C S hS F _,
      (eqToHom h : (ptOf C S hS e F p.carrier p.contained
        (yoneda.map (eqToHom h) ≫ yonedaEquiv.symm p.value)).siteObject C S hS F ⟶
          p.siteObject C S hS F), ?_⟩).symm
  change F.map (eqToHom h).op p.value = yonedaEquiv (yoneda.map (eqToHom h) ≫ _)
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- A morphism from the object of a field-valued point to `Spec K` is `Spec` of a `k`-algebra
map, for the algebra structure of the point. -/
theorem exists_algHom_of_hom {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (r : FieldValuedPoint C S hS F) {K : Type u} [Field K] [Algebra k K]
    {hK : C.Contains (Spec (.of K))} (φ : r.siteObject C S hS F ⟶ extObj C S hS e K hK) :
    letI := pointAlgebra C S hS e r
    ∃ β : K →ₐ[k] r.carrier, φ.left.hom = Spec.map (CommRingCat.ofHom β.toRingHom) := by
  let := pointAlgebra C S hS e r
  have hw : φ.left.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv = r.toBase :=
    congrArg (fun g => g.hom) (Over.w φ)
  exact exists_algHom_spec_map_eq φ.left.hom
    ((cancel_mono e.inv).mp (by simpa using hw.trans (toBase_eq_pointAlgebra C S hS e r)))

/-- **The fibre of a point with a finite residue field.** Let `ρ` be an `L`-valued point of a
presheaf `X` and let `M` be an extension of `k` such that every pair of `k`-embeddings of `L`
and `M` into a common field factors through an embedding of `L` into `M` (this holds when `M`
contains a normal extension of `k` into which `L` embeds). Then every point of
`X_M = Spec M × X` lying over the point of `ρ` is the `M`-rational point `(id, ρ ∘ τ)` for some
`k`-embedding `τ : L → M`. -/
theorem fibre_eq_ptOf (X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) (L : Type u) [Field L]
    [Algebra k L] (hL : C.Contains (Spec (.of L))) (ρ : yoneda.obj (extObj C S hS e L hL) ⟶ X)
    (M : Type u) [Field M] [Algebra k M] (hM : C.Contains (Spec (.of M)))
    (hfac : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] (α : L →ₐ[k] Ω) (β : M →ₐ[k] Ω),
      ∃ τ : L →ₐ[k] M, β.comp τ = α)
    (y : points C S hS (yoneda.obj (extObj C S hS e M hM) ⨯ X))
    (hy : pointsMap C S hS _ prod.snd y = (ptOf C S hS e X L hL ρ).class C S hS X) :
    ∃ τ : L →ₐ[k] M, y = (ptOf C S hS e _ M hM
      (prod.lift (𝟙 _) (yoneda.map (extMap C S hS e τ) ≫ ρ))).class C S hS _ := by
  obtain ⟨w, rfl⟩ := Quot.exists_rep y
  change (w.map C S hS _ prod.snd).class C S hS X = _ at hy
  obtain ⟨r, ⟨f₀, hf⟩, ⟨g₀, hg⟩⟩ := (FieldValuedPoint.class_eq_class_iff C S hS X _ _).mp hy
  let f : r.siteObject C S hS X ⟶ w.siteObject C S hS _ := f₀
  let g : r.siteObject C S hS X ⟶ extObj C S hS e L hL := g₀
  let := pointAlgebra C S hS e r
  let t := yonedaEquiv.symm w.value
  let t₁ : w.siteObject C S hS _ ⟶ extObj C S hS e M hM := yoneda.preimage (t ≫ prod.fst)
  obtain ⟨β, hβ⟩ := exists_algHom_of_hom C S hS e r (f ≫ t₁)
  obtain ⟨α, hα⟩ := exists_algHom_of_hom C S hS e r g
  obtain ⟨τ, hτ⟩ := hfac r.carrier α β
  have hg' : g = (f ≫ t₁) ≫ extMap C S hS e τ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change g.left.hom = (f ≫ t₁).left.hom ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
    rw [hα, hβ, ← Spec.map_comp, ← hτ]
    rfl
  refine ⟨τ, ?_⟩
  -- the restriction of `w` along `f`
  let r' : FieldValuedPoint C S hS (yoneda.obj (extObj C S hS e M hM) ⨯ X) :=
    { carrier := r.carrier, contained := r.contained, toBase := r.toBase
      value := (yoneda.obj (extObj C S hS e M hM) ⨯ X).map f.op w.value }
  have h1 : r'.class C S hS _ = w.class C S hS _ :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS _
      ⟨r', FieldValuedPoint.dominates_refl C S hS _ _, f, rfl⟩
  change w.class C S hS _ = _
  rw [← h1]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS _
    ⟨r', FieldValuedPoint.dominates_refl C S hS _ _, f ≫ t₁, ?_⟩
  change _ = (yoneda.obj (extObj C S hS e M hM) ⨯ X).map f.op w.value
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_symm_map, yonedaEquiv_symm_map]
  have hv : yonedaEquiv.symm (ptOf C S hS e _ M hM
      (prod.lift (𝟙 _) (yoneda.map (extMap C S hS e τ) ≫ ρ))).value =
        prod.lift (𝟙 _) (yoneda.map (extMap C S hS e τ) ≫ ρ) := Equiv.symm_apply_apply _ _
  change yoneda.map (f ≫ t₁) ≫ _ = yoneda.map f ≫ t
  rw [hv]
  apply prod.hom_ext
  · simp [t₁]
  · have hsnd : yoneda.map f ≫ t ≫ prod.snd = yonedaEquiv.symm r.value := by
      have h := yonedaEquiv_symm_naturality_right _ (prod.snd : _ ⨯ X ⟶ X) w.value
      rw [← hf, yonedaEquiv_symm_map]
      change yoneda.map f ≫ yonedaEquiv.symm w.value ≫ prod.snd = _
      rw [h]
      rfl
    have hρ : yoneda.map g ≫ ρ = yonedaEquiv.symm r.value := by
      rw [← hg, yonedaEquiv_symm_map]
      exact congrArg (fun a => yoneda.map g ≫ a) (Equiv.symm_apply_apply yonedaEquiv ρ).symm
    simp only [Category.assoc, prod.lift_snd]
    rw [hsnd, ← hρ, hg']
    simp only [Functor.map_comp, Category.assoc]

/-! ### Base change along an object of the site -/

/-- The base change `h_E × X ⟶ X` of a morphism of the site locally of finite type is locally
of finite type. -/
theorem isLocallyOfFiniteType_prod (E : BigFppfOver C S hS)
    {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace C S hS X)
    (hE : LocallyOfFiniteType ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from E)))
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from X)) :
    IsLocallyOfFiniteType C S hS
      ((isTerminal_yoneda_obj_base C S hS).from (yoneda.obj E ⨯ X)) := by
  have hsnd : IsLocallyOfFiniteType C S hS (prod.snd : yoneda.obj E ⨯ X ⟶ X) :=
    IsLocallyOfFiniteType.of_isPullback C S hS (isPullback_prod_fst_snd_yoneda_obj E X).flip
      (isAlgebraicSpace_yoneda C S hS _) (isAlgebraicSpace_yoneda C S hS _)
      ((isLocallyOfFiniteType_yoneda_map_iff C S hS _).2 hE)
  have h := isLocallyOfFiniteType_comp C S hS (isAlgebraicSpace_prod_yoneda_obj E hX) hX
    (isAlgebraicSpace_yoneda C S hS _) _ _ hsnd hlft
  rwa [(isTerminal_yoneda_obj_base C S hS).hom_ext (prod.snd ≫ _) _] at h

/-! ### The spectrum of a finite extension -/

/-- The spectrum of a finite extension of fields is finite locally free over the spectrum of the
base field. -/
theorem isFiniteLocallyFree_specMap_algebraMap (K : Type u) [Field K] [Algebra k K]
    [Module.Finite k K] :
    Stacks.Morphisms.IsFiniteLocallyFree (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [Stacks.Morphisms.specMap_finiteLocallyFree_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.AlgebraicGeometry.IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · rw [AlgebraicGeometry.Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.FinitePresentation.of_finiteType.mp
      (RingHom.finite_algebraMap.mpr inferInstance).finiteType

/-- The underlying morphism of schemes of the structure morphism of `extObj`. -/
theorem toScheme_map_from_extObj (K : Type u) [Field K] [Algebra k K]
    (hK : C.Contains (Spec (.of K))) :
    (BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e K hK)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv := by
  have h := Over.w (Over.mkIdTerminal.from (extObj C S hS e K hK))
  replace h : (Over.mkIdTerminal.from (extObj C S hS e K hK)).left =
      (extObj C S hS e K hK).hom := by simp
  change C.inclusion.map (Over.mkIdTerminal.from (extObj C S hS e K hK)).left = _
  rw [h]
  rfl

/-- The structure morphism of the spectrum of a finite extension is finite locally free. -/
theorem isFiniteLocallyFree_extObj (K : Type u) [Field K] [Algebra k K] [Module.Finite k K]
    (hK : C.Contains (Spec (.of K))) :
    Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e K hK))) := by
  rw [toScheme_map_from_extObj]
  have := isFiniteLocallyFree_specMap_algebraMap (k := k) K
  exact (MorphismProperty.RespectsIso.postcomp (P := @Stacks.Morphisms.IsFiniteLocallyFree)
    e.inv _ this)

/-- The structure morphism of the spectrum of an extension is surjective. -/
theorem surjective_extObj (K : Type u) [Field K] [Algebra k K]
    (hK : C.Contains (Spec (.of K))) :
    Surjective
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e K hK))) := by
  rw [toScheme_map_from_extObj]
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  infer_instance

/-! ### Points with a finite residue field -/

attribute [local instance] pointTopology

/-- **Points with a finite residue field are dense in every locally closed set.** If an
algebraic space `Y` over `S ≅ Spec k` is locally of finite type, then every nonempty locally
closed subset of `|Y|` contains the class of a field-valued point whose field is a finite
extension of `k`: an étale chart of `Y` is a scheme locally of finite type over `k`, hence a
Jacobson scheme whose closed points have finite residue fields. -/
theorem exists_finite_point (Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace C S hS Y)
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from Y))
    {Z : Set (points C S hS Y)} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ p : FieldValuedPoint C S hS Y, p.class C S hS Y ∈ Z ∧
      letI := pointAlgebra C S hS e p
      Module.Finite k p.carrier := by
  obtain ⟨U, a, hsurj, het⟩ := hY.exists_atlas
  have hsurj' : Function.Surjective (pointsMap C S hS _ a) :=
    (presheafSurjective_iff_isSurjective_yoneda C S hS Y hY U a).1 hsurj
  let φ := schemePointsHomeomorph C S hS U
  let Z' : Set ((BigFppfOver.toScheme C S hS).obj U) := φ '' (pointsMap C S hS _ a ⁻¹' Z)
  have hZ' : IsLocallyClosed Z' :=
    (hZ.preimage (continuous_pointsMap C S hS a)).image φ.isInducing
      (by rw [φ.range_coe]; exact isClosed_univ.isLocallyClosed)
  have hne' : Z'.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, rfl⟩ := hsurj' z
    exact ⟨φ w, w, hz, rfl⟩
  -- the chart is locally of finite type over `k`
  let h : U ⟶ Over.mk (𝟙 (C.obj hS)) := Over.mkIdTerminal.from U
  have hU : LocallyOfFiniteType ((BigFppfOver.toScheme C S hS).map h) :=
    hlft U (Over.mk (𝟙 (C.obj hS))) a (𝟙 _) h het
      (presheaf_yoneda_map_id_etale C S hS _) ((isTerminal_yoneda_obj_base C S hS).hom_ext _ _)
  let f : (BigFppfOver.toScheme C S hS).obj U ⟶ Spec (.of k) :=
    (BigFppfOver.toScheme C S hS).map h ≫ e.hom
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace ((BigFppfOver.toScheme C S hS).obj U) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints hne' hZ'
  let p := (schemePointRepresentative C S hS U x).map C S hS _ a
  refine ⟨p, ?_, ?_⟩
  · obtain ⟨w, hw, hwx⟩ := hxZ
    change pointsMap C S hS _ a ((schemePointRepresentative C S hS U x).class C S hS _) ∈ Z
    have : (schemePointRepresentative C S hS U x).class C S hS _ = w := by
      rw [← hwx]
      exact class_schemePointRepresentative_pointsToScheme C S hS U w
    rwa [this]
  · let := pointAlgebra C S hS e p
    have hcl : _root_.AlgebraicGeometry.IsClosedImmersion
        (((BigFppfOver.toScheme C S hS).obj U).fromSpecResidueField x) :=
      isClosed_singleton_iff_isClosedImmersion.mp hx
    have hfin : _root_.AlgebraicGeometry.IsFinite
        (((BigFppfOver.toScheme C S hS).obj U).fromSpecResidueField x ≫ f) :=
      (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace).mpr inferInstance
    have hp : p.toBase = ((BigFppfOver.toScheme C S hS).obj U).fromSpecResidueField x ≫
        (BigFppfOver.toScheme C S hS).map h := by
      change C.inclusion.map (C.inclusion.preimage _ ≫ U.hom) = _
      rw [Functor.map_comp, Functor.map_preimage]
      congr 1
      have hw := Over.w h
      exact (congrArg C.inclusion.map hw).symm.trans (by simp)
    have heq : ((BigFppfOver.toScheme C S hS).obj U).fromSpecResidueField x ≫ f =
        Spec.map (Spec.preimage (p.toBase ≫ e.hom)) := by
      rw [Spec.map_preimage, hp]
      rfl
    rw [heq] at hfin
    exact (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff _).mp hfin

/-! ### A dense open in which finite sets lie in affine opens -/

/-- Every scheme has a dense open subset in which every finite set of points lies in a common
affine open: the union of a maximal family of pairwise disjoint nonempty affine opens. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_dense_isOpen_forall_finite_isAffineOpen
    (X : Scheme.{u}) :
    ∃ D : Set X, IsOpen D ∧ Dense D ∧ ∀ s : Set X, s.Finite → s ⊆ D →
      ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  classical
  let 𝔉 : Set (Set X.Opens) := {F | (∀ U ∈ F, IsAffineOpen U) ∧ F.PairwiseDisjoint id}
  obtain ⟨F, hF, hmax⟩ := zorn_subset 𝔉 (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨fun U hU => ?_, fun U hU V hV hUV => ?_⟩,
      fun F hF => Set.subset_sUnion_of_mem hF⟩
    · obtain ⟨F, hFc, hUF⟩ := hU
      exact (hc hFc).1 U hUF
    · obtain ⟨F, hFc, hUF⟩ := hU
      obtain ⟨G, hGc, hVG⟩ := hV
      rcases hchain.total hFc hGc with h | h
      · exact (hc hGc).2 (h hUF) hVG hUV
      · exact (hc hFc).2 hUF (h hVG) hUV)
  refine ⟨⋃ U ∈ F, (U : Set X), isOpen_biUnion fun U _ => U.isOpen, ?_, ?_⟩
  · rw [dense_iff_closure_eq]
    by_contra hne
    obtain ⟨x, hx⟩ : (closure (⋃ U ∈ F, (U : Set X)))ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact hne
    obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (x := x)
      (U := ⟨_, isClosed_closure.isOpen_compl⟩) hx
    have hV' : insert V F ∈ 𝔉 := by
      refine ⟨fun W hW => ?_, ?_⟩
      · rcases hW with rfl | hW
        · exact hV
        · exact hF.1 W hW
      · refine hF.2.insert fun W hW _ => ?_
        change Disjoint V W
        rw [← TopologicalSpace.Opens.coe_disjoint]
        refine Set.disjoint_left.mpr fun y hyV hyW => hVsub hyV ?_
        exact subset_closure (Set.mem_biUnion hW hyW)
    have hVF : V ∈ F := hmax hV' (Set.subset_insert V F) (Set.mem_insert V F)
    exact hVsub hxV (subset_closure (Set.mem_biUnion hVF hxV))
  · intro s hs hsD
    have hch : ∀ x ∈ s, ∃ U ∈ F, x ∈ (U : Set X) := fun x hx => by
      simpa using hsD hx
    choose g hgF hgx using hch
    let t : Set X.Opens := Set.range fun x : s => g x.1 x.2
    have : Finite s := hs.to_subtype
    have ht : t.Finite := Set.finite_range _
    refine ⟨⨆ U ∈ t, U, ?_, fun x hx => ?_⟩
    · refine IsAffineOpen.biSup_of_disjoint ht (fun U hU => ?_) (fun U hU V hV hUV => ?_)
      · obtain ⟨⟨x, hx⟩, rfl⟩ := hU
        exact hF.1 _ (hgF x hx)
      · obtain ⟨⟨x, hx⟩, rfl⟩ := hU
        obtain ⟨⟨y, hy⟩, rfl⟩ := hV
        exact hF.2 (hgF x hx) (hgF y hy) hUV
    · have : (g x hx : X.Opens) ≤ ⨆ U ∈ t, U := le_biSup id ⟨⟨x, hx⟩, rfl⟩
      exact this (hgx x hx)

end AlgebraicGeometry.Space.GroupOverField
