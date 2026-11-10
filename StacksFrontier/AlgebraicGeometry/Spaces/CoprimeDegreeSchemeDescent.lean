module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictRepresentability

/-!
# Descending schemes along finite field extensions of coprime degrees

Let `k` be a finite field and `X` an algebraic space of finite presentation over `k`. Suppose
that `X_A` is a scheme for a `k`-algebra `A` which, for every `d > 0`, maps to a finite field
extension of `k` of degree prime to `d`. Then `X` is a scheme. This is the core of the proof of
Stacks 0B85 for a finite ground field, and of the third assertion of Stacks 0BA7.

The argument follows the source. The space `X` is decent and Jacobson, so it suffices to place
every closed point `x` in the schematic locus. The residue field `κ` of `x` is finite over `k`.
Choose `L/k` finite of degree prime to `[κ : k]` receiving a map from `A`; then `X_L` is a
scheme, `X_L ⟶ X` is finite locally free and surjective, and its fibre over `x` is a single
point because `κ ⊗_k L` is a field. Any affine open of `X_L` through that point contains the
whole fibre, so `x` lies in the schematic locus by Stacks 0BA1.

## Main results

* `Algebra.TensorProduct.isField_of_coprime_finrank`: the tensor product of two field extensions
  of coprime degrees is a field.
* `AlgebraicGeometry.Space.isRepresentable_of_forall_isClosed_mem_schematicLocus`: an algebraic
  space with Jacobson point space all of whose closed points lie in the schematic locus is a
  scheme.
* `AlgebraicGeometry.Space.exists_isAffine_isOpenImmersion_mem_range_of_isRepresentable`: every
  point of a scheme lies in an affine open.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_finite_of_isClosed`: a closed point of an
  algebraic space locally of finite type over a field is represented by a finite extension.
* `AlgebraicGeometry.Space.isRepresentable_of_forall_coprime_algHom_of_isRepresentable_baseChange`:
  the descent statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

universe u

/-- **Tensor products of fields of coprime degrees.** If `A` and `B` are field extensions of `F`
whose degrees are coprime, then `A ⊗_F B` is a field: in every common extension the images of
`A` and `B` are linearly disjoint by the degree count. -/
theorem Algebra.TensorProduct.isField_of_coprime_finrank (F A B : Type*) [Field F] [Field A]
    [Field B] [Algebra F A] [Algebra F B] (h : (finrank F A).Coprime (finrank F B)) :
    IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B fun _ _ _ fa fb => ?_
  have ha : finrank F A = finrank F fa.fieldRange :=
    (AlgEquiv.ofInjectiveField fa).toLinearEquiv.finrank_eq
  have hb : finrank F B = finrank F fb.fieldRange :=
    (AlgEquiv.ofInjectiveField fb).toLinearEquiv.finrank_eq
  exact IntermediateField.LinearDisjoint.of_finrank_coprime (by rwa [← ha, ← hb])

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Closed points in the schematic locus.** An algebraic space whose space of points is
Jacobson and all of whose closed points lie in the schematic locus is a scheme: the complement
of the schematic locus is closed without closed points, hence empty. -/
theorem isRepresentable_of_forall_isClosed_mem_schematicLocus
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    [JacobsonSpace (points B S hS X)]
    (hclosed : ∀ x : points B S hS X, IsClosed ({x} : Set (points B S hS X)) →
      x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
        (schematicLocus B S hS X).ι)) :
    X.IsRepresentable := by
  obtain ⟨hU, hUrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  let U := schematicLocus B S hS X
  let V := openSubspacesOrderIso B S hS X hX ⟨U, hU⟩
  have hV : (V : Set (points B S hS X)) = Set.range (pointsMap B S hS U.toFunctor U.ι) :=
    openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩
  have hempty : (V : Set (points B S hS X))ᶜ ∩ closedPoints (points B S hS X) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hxc⟩ => hx (hV ▸ hclosed x hxc)
  have hall : ∀ x : points B S hS X, x ∈ (V : Set (points B S hS X)) := by
    intro x
    by_contra hx
    have h := JacobsonSpace.closure_inter_closedPoints V.isOpen.isClosed_compl
    rw [hempty, closure_empty] at h
    exact (h ▸ hx : x ∈ (∅ : Set (points B S hS X)))
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hX U hU (𝟙 X)).mpr
    (by rintro _ ⟨x, rfl⟩; exact hV ▸ hall _)
  have : IsSplitEpi U.ι := IsSplitEpi.mk' ⟨g, hg⟩
  have : IsIso U.ι := isIso_of_mono_of_isSplitEpi _
  exact isRepresentable_of_natIso U.toFunctor (asIso U.ι)

/-- **Affine open neighbourhoods in a scheme.** Every point of a representable presheaf lies in
the image of an open immersion from an affine object of the site: a member of the standard
affine cover of the representing object. -/
theorem exists_isAffine_isOpenImmersion_mem_range_of_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [X.IsRepresentable] (x : points B S hS X) :
    ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS α ∧
        x ∈ Set.range (pointsMap B S hS (yoneda.obj V) α) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS X.reprX X.reprW p
  refine ⟨affineChart B S hS X.reprX i, yoneda.map (affineChartι B S hS X.reprX i) ≫ X.reprW.hom,
    isAffine_affineChart B S hS X.reprX i, ?_, ⟨_, hq⟩⟩
  exact MorphismProperty.RespectsIso.postcomp _ X.reprW.hom _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
      (isOpenImmersion_toScheme_map_affineChartι B S hS X.reprX i))

end General

section OverField

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **Spaces locally of finite type over a field are Jacobson**, in the form of a surjective étale
atlas by a Jacobson scheme (Stacks 0BA3 over the Jacobson base `Spec k`). -/
theorem exists_jacobson_atlas_of_isLocallyOfFiniteType_overField
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hk f) :
    ∃ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of k)) hk))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (Spec (.of k)) hk))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U) :=
  exists_jacobson_atlas_of_isLocallyOfFiniteType B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _) hX f hf
    ⟨Over.mk (𝟙 (B.obj hk)), 𝟙 _,
      presheaf_id_of_iso B (Spec (.of k)) hk _ (fun _ _ g _ =>
        inferInstanceAs (Surjective ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g))) _,
      presheaf_id_of_iso B (Spec (.of k)) hk _ (fun _ _ g _ =>
        inferInstanceAs (Etale ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g))) _,
      inferInstanceAs (JacobsonSpace (Spec (.of k)))⟩

/-- **Closed points have finite residue fields.** A closed point of a decent algebraic space
locally of finite type over a field `k` is represented by a field-valued point `Spec κ ⟶ X`
with `κ` finite over `k`: it is a finite type point (Stacks 06EG, 0BA6), so `κ` is of finite type
over `k`, hence finite by the Nullstellensatz. -/
theorem exists_fieldValuedPoint_finite_of_isClosed
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (hdec : IsDecentSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hk f)
    (x : points B (Spec (.of k)) hk X) (hx : IsClosed ({x} : Set (points B (Spec (.of k)) hk X))) :
    ∃ p : FieldValuedPoint B (Spec (.of k)) hk X,
      p.class B (Spec (.of k)) hk X = x ∧ (Spec.preimage p.toBase).hom.Finite := by
  obtain ⟨p, hpx, hp⟩ : x ∈ finiteTypePoints B (Spec (.of k)) hk X := by
    rwa [finiteTypePoints_eq_setOf_isClosed_singleton B (Spec (.of k)) hk hX hdec
      (exists_jacobson_atlas_of_isLocallyOfFiniteType_overField k B hk hX f hf)]
  refine ⟨p, hpx, ?_⟩
  let Z : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let g : p.siteObject ⟶ Z := Over.homMk p.siteObject.hom
  have hcomp := isLocallyOfFiniteType_comp B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _) hX
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk Z) _ f hp hf
  have hg : yonedaEquiv.symm p.value ≫ f = yoneda.map g :=
    (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _
  rw [hg, isLocallyOfFiniteType_yoneda_map_iff] at hcomp
  have hlft : LocallyOfFiniteType (Spec.map (Spec.preimage p.toBase)) := by
    rwa [Spec.map_preimage]
  let : Algebra k p.carrier := (Spec.preimage p.toBase).hom.toAlgebra
  have : Algebra.FiniteType k p.carrier := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft)
  exact RingHom.finite_algebraMap.mpr (finite_of_finite_type_of_isJacobsonRing k p.carrier)

/-- **Base change to an extension receiving `A`.** If `X_A` is a scheme and `φ : A →ₐ[k] L`, then
`X_L` is a scheme. -/
private theorem isRepresentable_extensionBaseChange_of_algHom (A : Type u) [CommRing A]
    [Algebra k A] (hA : B.Contains (Spec (.of A))) (L : Type u) [Field L] [Algebra k L]
    (hL : B.Contains (Spec (.of L))) (φ : A →ₐ[k] L)
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hA ⟶ B.obj hk)).obj X).IsRepresentable) :
    (extensionBaseChange k L B hk hL X).IsRepresentable := by
  let a : B.obj hL ⟶ B.obj hA := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
  let b : B.obj hA ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  have hab : a ≫ b = specExtensionHom k L B hk hL := by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext t
    exact φ.commutes t
  have := hbase
  have h := OverShriek.isRepresentable_relocalizeRestrict_comp a b X
  rw [hab] at h
  exact (OverShriek.isRepresentable_relocalizeRestrict_iff_prod _ X).mp h

/-- **Descent along finite extensions of coprime degrees.** Let `k` be a finite field, `A` a
`k`-algebra which for every `d > 0` maps to a finite extension of `k` of degree prime to `d`, and
`X` an algebraic space of finite presentation over `k` such that `X_A` is a scheme. Then `X` is a
scheme. -/
theorem isRepresentable_of_forall_coprime_algHom_of_isRepresentable_baseChange [Finite k]
    (A : Type u) [CommRing A] [Algebra k A]
    (hpts : ∀ d : ℕ, 0 < d → ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      Nat.Coprime (finrank k L) d ∧ Nonempty (A →ₐ[k] L))
    (hA : B.Contains (Spec (.of A)))
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : IsFinitePresentation B (Spec (.of k)) hk f)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hA ⟶ B.obj hk)).obj X).IsRepresentable) :
    X.IsRepresentable := by
  -- `X` is quasi-separated, hence decent, and it is Jacobson
  have hqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of k)) hk B.contains_terminal hX
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of k)) hk _
        B.contains_terminal ⟨Over.mk (𝟙 (B.obj hk)),
          inferInstanceAs (QuasiSeparatedSpace (Spec (.of k))),
          ⟨Functor.RepresentableBy.yoneda _⟩⟩) hf.2.2
  have hdec := isDecentSpace_of_isAbsolutelyQuasiSeparated B (Spec (.of k)) hk X hX hqs
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (Spec (.of k)) hk hf.1
  have := (exists_jacobson_atlas_iff_jacobsonSpace_points B (Spec (.of k)) hk hX hdec).mp
    (exists_jacobson_atlas_of_isLocallyOfFiniteType_overField k B hk hX f hft)
  refine isRepresentable_of_forall_isClosed_mem_schematicLocus B (Spec (.of k)) hk hX
    fun x hx => ?_
  obtain ⟨p, rfl, hpfin⟩ := exists_fieldValuedPoint_finite_of_isClosed k B hk hX hdec f hft x hx
  let : Algebra k p.carrier := (Spec.preimage p.toBase).hom.toAlgebra
  have : FiniteDimensional k p.carrier := RingHom.finite_algebraMap.mp hpfin
  -- an extension `L` of degree prime to `[κ : k]` receiving `A`
  obtain ⟨L, _, _, _, hcop, ⟨φ⟩⟩ := hpts (finrank k p.carrier) finrank_pos
  have : FiniteDimensional k L := Module.Finite.of_finite
  have hL : B.Contains (Spec (.of L)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k L hk
  -- `X_L` is a scheme
  have hXL := isRepresentable_extensionBaseChange_of_algHom k B hk A hA L hL φ hbase
  -- the projection `X_L ⟶ X` and the criterion of Stacks 0BA1
  let XL : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨_, isAlgebraicSpace_extensionBaseChange k L B hk hL X hX⟩
  let π : XL ⟶ ⟨X, hX⟩ := ObjectProperty.homMk (extensionBaseChangeProj k L B hk hL X)
  refine (mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion B (Spec (.of k))
    hk π (presheaf_surjective_extensionBaseChangeProj k L B hk hL X)
    (presheaf_isFiniteLocallyFree_extensionBaseChangeProj k L B hk hL X) _).mpr ?_
  obtain ⟨y, hy⟩ := isSurjective_extensionBaseChangeProj k L B hk hL X
    (p.class B (Spec (.of k)) hk X)
  obtain ⟨V, α, hV, hα, hyV⟩ :=
    exists_isAffine_isOpenImmersion_mem_range_of_isRepresentable B (Spec (.of k)) hk y
  have hfibre := subsingleton_setFibre_extensionBaseChangeProj k L B hk hL X p
    (Spec.map_preimage p.toBase)
    (Algebra.TensorProduct.isField_of_coprime_finrank k p.carrier L hcop.symm)
  exact ⟨V, α, hV, hα, fun z hz => by rwa [hfibre hz hy]⟩

end OverField

end AlgebraicGeometry.Space

end
