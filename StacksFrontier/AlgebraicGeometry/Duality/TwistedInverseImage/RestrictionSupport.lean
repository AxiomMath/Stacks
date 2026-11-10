module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence

/-!
# The twisted inverse image and restriction to opens: a support criterion

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes, `V ⊆ Y` a quasi-compact
open with inverse image `U`, and `a`, `a'` the right adjoints of `Rf_*` and `R(f|_U)_*` on the
quasi-coherent derived categories. [Stacks, Tag 0A9N] says that the canonical map
`(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)` exactly when `a`
carries every `Q ∈ D^+_QCoh(𝒪_Y)` supported on `Y \ V` to an object supported on `X \ U`, and
likewise on all of `D_QCoh(𝒪_Y)`.

## Main results

* `Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_iff` — the map of Tag 0A9L is
  invertible at `K` exactly when `(j')^* a(K) ⟶ (j')^* a(Rj_* j^* K)` is.
* `Stacks.Duality.exists_cone_unit` — the cone `Q` of `K ⟶ Rj_* j^* K`: it restricts to zero on
  `V`, is bounded below with `K`, and `a(Q)|_U = 0` forces the map of Tag 0A9L to be invertible
  at `K`.
* `Stacks.Duality.isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap_of_isBoundedBelow`
  and `Stacks.Duality.isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap` — parts (1)
  and (2) of Tag 0A9N, for an arbitrary cartesian square along an open immersion `j`.
* `Stacks.Duality.isZero_restrict_twistedInverseImage_of_isBoundedBelow` — part (3), the support
  condition passing from `D^+_QCoh` to `D_QCoh` when `a` commutes with direct sums.
* `Stacks.Duality.twistedInverseImageRestrictionMap_isIso_iff` — **[Stacks, Tag 0A9N]**, all three
  parts, for quasi-compact quasi-separated schemes, with no further hypothesis.

"Supported on `Y \ V`" is read as "restricts to zero on `V`", which is the same condition: the
cohomology sheaves of `Q|_V` are the restrictions of those of `Q`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality

open OpenImmersion

/-- The twisted inverse image is triangulated, for some commutation with the shift. -/
private theorem exists_commShift_isTriangulated_twistedInverseImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint] :
    ∃ _ : (twistedInverseImage f hpushf).CommShift ℤ,
      (twistedInverseImage f hpushf).IsTriangulated := by
  let adj := twistedInverseImageAdjunction f hpushf
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  exact ⟨‹_›, adj.isTriangulated_rightAdjoint⟩

section Pointwise

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward j).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  (sq : IsPullback j' f' f j)

/-- The map of [Stacks, Tag 0A9L] is invertible at `K` exactly when
`(j')^* a(K) ⟶ (j')^* a(Rj_* j^* K)`, the image of the unit of `j^* ⊣ Rj_*`, is. -/
theorem isIso_twistedInverseImageRestrictionMap_app_iff (K : quasiCoherentDerivedCategory Y) :
    IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) ↔
    IsIso ((quasiCoherentDerivedRestrict j' (isQuasicoherent_homology_derivedRestrict j')).map
      ((twistedInverseImage f hpushf).map
        ((quasiCoherentDerivedRestrictAdjunction j (isQuasicoherent_homology_derivedRestrict j)
          hpushj).unit.app K))) := by
  have : IsIso (quasiCoherentDerivedRestrictAdjunction j'
      (isQuasicoherent_homology_derivedRestrict j') hpushj').counit :=
    isIso_liftDerivedRestrictPushforwardAdjunction_counit j' _ _ _ _
  simp only [twistedInverseImageRestrictionMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id]
  exact isIso_comp_right_iff _ _

/-- `j^*` of the unit `K ⟶ Rj_* j^* K` of the derived adjunction `j^* ⊣ Rj_*` is invertible: the
counit is invertible and the triangle identity holds. -/
theorem isIso_derivedRestrict_map_unit_app (K : DerivedCategory Y.Modules) :
    IsIso ((derivedRestrict j).map ((derivedRestrictPushforwardAdjunction j).unit.app K)) := by
  rw [IsIso.eq_inv_of_inv_hom_id
    ((derivedRestrictPushforwardAdjunction j).left_triangle_components K)]
  infer_instance

/-- Restriction along an open immersion preserves lower bounds of cohomology. -/
theorem isGE_derivedRestrict_obj (K : DerivedCategory Y.Modules) (n : ℤ) [K.IsGE n] :
    ((derivedRestrict j).obj K).IsGE n :=
  (DerivedCategory.isGE_iff _ _).2 fun i hi =>
    ((Scheme.Modules.restrictFunctor j).map_isZero (K.isZero_of_isGE n i hi)).of_iso
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso i).app K)

/-- Derived direct image preserves lower bounds of cohomology. -/
theorem isGE_derivedPushforward_obj' {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory X.Modules) (n : ℤ) [K.IsGE n] :
    ((derivedPushforward g).obj K).IsGE n :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (Scheme.Modules.pushforward g)
    (derivedPushforward g) (derivedPushforwardUnit g)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective g I hI) K n inferInstance

/-- **The cone of the unit.** For `K ∈ D_QCoh(𝒪_Y)` the unit `K ⟶ Rj_* j^* K` sits in a
distinguished triangle of `D_QCoh(𝒪_Y)` whose third vertex `Q` restricts to zero on `V` and is
bounded below as soon as `K` is; and if `a(Q)` restricts to zero on `U` then the map of
[Stacks, Tag 0A9L] is invertible at `K`. -/
theorem exists_cone_unit (K : quasiCoherentDerivedCategory Y) :
    ∃ Q : quasiCoherentDerivedCategory Y,
      IsZero ((derivedRestrict j).obj Q.obj) ∧
      (∀ n : ℤ, K.obj.IsGE n → Q.obj.IsGE (n - 1)) ∧
      (IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj) →
        IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
          (isQuasicoherent_homology_derivedRestrict j)
          (isQuasicoherent_homology_derivedRestrict j') sq).app K)) := by
  let adjL := quasiCoherentDerivedRestrictAdjunction j
    (isQuasicoherent_homology_derivedRestrict j) hpushj
  obtain ⟨Q, g, h, hT⟩ := distinguished_cocone_triangle (adjL.unit.app K)
  have hu : (ObjectProperty.ι _).map (adjL.unit.app K) =
      (derivedRestrictPushforwardAdjunction j).unit.app K.obj :=
    map_liftDerivedRestrictPushforwardAdjunction_unit_app j _ _ _ hpushj K
  have hT₁ := (ObjectProperty.ι _).map_distinguished _ hT
  refine ⟨Q, ?_, ?_, ?_⟩
  · have hT₂ := (derivedRestrict j).map_distinguished _ hT₁
    refine (Triangle.isZero₃_iff_isIso₁ _ hT₂).2 ?_
    change IsIso ((derivedRestrict j).map ((ObjectProperty.ι _).map (adjL.unit.app K)))
    rw [hu]
    exact isIso_derivedRestrict_map_unit_app j K.obj
  · intro n hn
    have : DerivedCategory.TStructure.t.IsGE K.obj n := hn
    have := isGE_derivedRestrict_obj j K.obj n
    have h₂ : DerivedCategory.TStructure.t.IsGE
        ((derivedPushforward j).obj ((derivedRestrict j).obj K.obj)) n :=
      isGE_derivedPushforward_obj' j _ n
    have h₂' : DerivedCategory.TStructure.t.IsGE
        ((derivedPushforward j).obj ((derivedRestrict j).obj K.obj)) (n - 1) :=
      DerivedCategory.TStructure.t.isGE_of_ge _ (n - 1) n
    have h₃ : DerivedCategory.TStructure.t.IsGE (K.obj⟦(1 : ℤ)⟧) (n - 1) :=
      DerivedCategory.TStructure.t.isGE_shift K.obj n 1 (n - 1)
    exact DerivedCategory.TStructure.t.isGE₂ _ (rot_of_distTriang _ hT₁) (n - 1) h₂' h₃
  · intro hQ
    rw [isIso_twistedInverseImageRestrictionMap_app_iff]
    obtain ⟨_, _⟩ := exists_commShift_isTriangulated_twistedInverseImage f hpushf
    have hT' := (derivedRestrict j').map_distinguished _
      ((ObjectProperty.ι _).map_distinguished _
        ((twistedInverseImage f hpushf).map_distinguished _ hT))
    have hiso := (Triangle.isZero₃_iff_isIso₁ _ hT').1 hQ
    have : IsIso ((ObjectProperty.ι _).map
        ((quasiCoherentDerivedRestrict j' (isQuasicoherent_homology_derivedRestrict j')).map
          ((twistedInverseImage f hpushf).map (adjL.unit.app K)))) := hiso
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- If the map of [Stacks, Tag 0A9L] is invertible at an object `Q` restricting to zero on `V`,
then `a(Q)` restricts to zero on `U`: it is then `(j')^* a(Rj_* j^* Q)` and `j^* Q = 0`. -/
theorem isZero_of_isIso_twistedInverseImageRestrictionMap_app (Q : quasiCoherentDerivedCategory Y)
    (hQ : IsZero ((derivedRestrict j).obj Q.obj))
    (h : IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
      (isQuasicoherent_homology_derivedRestrict j)
      (isQuasicoherent_homology_derivedRestrict j') sq).app Q)) :
    IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj) := by
  rw [isIso_twistedInverseImageRestrictionMap_app_iff] at h
  let adjL := quasiCoherentDerivedRestrictAdjunction j
    (isQuasicoherent_homology_derivedRestrict j) hpushj
  let adjL' := quasiCoherentDerivedRestrictAdjunction j'
    (isQuasicoherent_homology_derivedRestrict j') hpushj'
  have := adjL.isRightAdjoint
  have := adjL'.isLeftAdjoint
  have := (twistedInverseImageAdjunction f hpushf).isRightAdjoint
  have h₁ : IsZero ((quasiCoherentDerivedRestrict j
      (isQuasicoherent_homology_derivedRestrict j)).obj Q) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ hQ
  have h₂ := (quasiCoherentDerivedRestrict j'
    (isQuasicoherent_homology_derivedRestrict j')).map_isZero
      ((twistedInverseImage f hpushf).map_isZero
        ((quasiCoherentDerivedPushforward j hpushj).map_isZero h₁))
  exact (ObjectProperty.ι _).map_isZero (h₂.of_iso (asIso
    ((quasiCoherentDerivedRestrict j' (isQuasicoherent_homology_derivedRestrict j')).map
      ((twistedInverseImage f hpushf).map (adjL.unit.app Q)))))

/-- **[Stacks, Tag 0A9N] part (1), for an arbitrary cartesian square along an open immersion.**
`a` carries every `Q ∈ D^+_QCoh(𝒪_Y)` restricting to zero on `V` to an object restricting to zero
on `U` if and only if the map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is invertible on
every object of `D^+_QCoh(𝒪_Y)`. -/
theorem isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap_of_isBoundedBelow :
    (∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
      IsZero ((derivedRestrict j).obj Q.obj) →
        IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj)) ↔
    ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
      IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
        (isQuasicoherent_homology_derivedRestrict j)
        (isQuasicoherent_homology_derivedRestrict j') sq).app K) := by
  refine ⟨fun h K ⟨n, hn⟩ => ?_, fun h Q hQb hQ =>
    isZero_of_isIso_twistedInverseImageRestrictionMap_app j' f' f j hpushj' hpushf hpushf'
      hpushj sq Q hQ (h Q hQb)⟩
  have hGE : K.obj.IsGE n := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn i hi
  obtain ⟨Q, hQ, hQb, hiso⟩ := exists_cone_unit j' f' f j hpushj' hpushf hpushf' hpushj sq K
  have := hQb n hGE
  exact hiso (h Q ⟨n - 1, fun i hi ↦ DerivedCategory.isZero_of_isGE _ (n - 1) i hi⟩ hQ)

/-- **[Stacks, Tag 0A9N] part (2), for an arbitrary cartesian square along an open immersion.**
`a` carries every `Q ∈ D_QCoh(𝒪_Y)` restricting to zero on `V` to an object restricting to zero
on `U` if and only if the map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is invertible on
every object of `D_QCoh(𝒪_Y)`. -/
theorem isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap :
    (∀ Q : quasiCoherentDerivedCategory Y, IsZero ((derivedRestrict j).obj Q.obj) →
        IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj)) ↔
    ∀ K : quasiCoherentDerivedCategory Y,
      IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
        (isQuasicoherent_homology_derivedRestrict j)
        (isQuasicoherent_homology_derivedRestrict j') sq).app K) := by
  refine ⟨fun h K => ?_, fun h Q hQ =>
    isZero_of_isIso_twistedInverseImageRestrictionMap_app j' f' f j hpushj' hpushf hpushf'
      hpushj sq Q hQ (h Q)⟩
  obtain ⟨Q, hQ, -, hiso⟩ := exists_cone_unit j' f' f j hpushj' hpushf hpushf' hpushj sq K
  exact hiso (h Q hQ)

end Pointwise

/-! ### Part (3): direct sums -/

section Sums

/-- The objects killed by a functor preserving direct sums are closed under direct sums. -/
theorem isClosedUnderColimitsOfShape_kerProp {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (G : C ⥤ D) (J : Type*) [PreservesColimitsOfShape (Discrete J) G] :
    (CategoryTheory.Pretriangulated.kerProp G).IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    change IsZero (G.obj X)
    rw [IsZero.iff_id_eq_zero]
    refine (isColimitOfPreserves G h.isColimit).hom_ext fun k => ?_
    have hk : IsZero (G.obj (h.diag.obj k)) := h.prop_diag_obj k
    exact hk.eq_of_src _ _

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [AlgebraicGeometry.QuasiCompact j'] [AlgebraicGeometry.QuasiCompact j]
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]

/-- **Part (3) of [Stacks, Tag 0A9N], with the boundedness of compact objects as a parameter.**
If `a` commutes with direct sums and carries every `Q ∈ D^+_QCoh(𝒪_Y)` restricting to zero on `V`
to an object restricting to zero on `U`, then it does so for every `Q ∈ D_QCoh(𝒪_Y)` restricting
to zero on `V`. The objects `Q` with `a(Q)|_U = 0` form a localizing subcategory, and the kernel
of restriction to `V` is the localizing subcategory generated by compact objects
(`Stacks.Duality.SupportedGeneration.kernelDetected`), which are bounded below. -/
theorem isZero_restrict_twistedInverseImage_of_isBoundedBelow
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α) (twistedInverseImage f hpushf)]
    (hbdd : ∀ K : quasiCoherentDerivedCategory Y, IsCompactObject.{u} K →
      DerivedCategoryB.IsBoundedBelow K.obj)
    (h : ∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
      IsZero ((derivedRestrict j).obj Q.obj) →
        IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj))
    (Q : quasiCoherentDerivedCategory Y) (hQ : IsZero ((derivedRestrict j).obj Q.obj)) :
    IsZero ((derivedRestrict j').obj ((twistedInverseImage f hpushf).obj Q).obj) := by
  obtain ⟨ι, K, hKc, hK0, hKdet⟩ := SupportedGeneration.kernelDetected j
  let adjj := restrictedDerivedRestrictAdjunction j
  let adjj' := restrictedDerivedRestrictAdjunction j'
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_twistedInverseImage f hpushf
  have := adjj'.leftAdjoint_preservesColimits
  let G := twistedInverseImage f hpushf ⋙ restrictedDerivedRestrict j'
  obtain ⟨h₁, h₂, h₃⟩ := CategoryTheory.Pretriangulated.kerProp_isTriangulated (L := G)
  have := h₁
  have := h₂
  have := h₃
  have : ∀ J : Type u, (CategoryTheory.Pretriangulated.kerProp G).IsClosedUnderColimitsOfShape
      (Discrete J) := fun J => isClosedUnderColimitsOfShape_kerProp G J
  have hQ' : IsZero ((restrictedDerivedRestrict j).obj Q) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ hQ
  have hloc := CategoryTheory.Pretriangulated.localizingClosure_of_isZero adjj K hKc hK0 hKdet hQ'
  have hle : (ofObj K).localizingClosure.{u} ≤ CategoryTheory.Pretriangulated.kerProp G := by
    refine ObjectProperty.localizingClosure_le ?_
    rintro _ ⟨i⟩
    exact IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (h (K i) (hbdd _ (hKc i)) ((ObjectProperty.ι _).map_isZero (hK0 i)))
  exact (ObjectProperty.ι _).map_isZero (hle _ hloc)

end Sums

/-! ### The statement for quasi-compact quasi-separated schemes -/

section Qcqs

/-- In a cartesian square along an open immersion `j : V ⟶ Y` with `f` quasi-compact and `V`
quasi-compact, the source `U` of the base change is quasi-compact. -/
theorem compactSpace_of_isPullback {U X V Y : Scheme.{u}} {j' : U ⟶ X} {f' : U ⟶ V} {f : X ⟶ Y}
    {j : V ⟶ Y} (sq : IsPullback j' f' f j) [AlgebraicGeometry.QuasiCompact f] [CompactSpace V] :
    CompactSpace U :=
  have : AlgebraicGeometry.QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  QuasiCompact.compactSpace_of_compactSpace f'

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] [CompactSpace V]

/-- **[Stacks, Tag 0A9N].** Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes,
`a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `j : V ⟶ Y` the inclusion of a
quasi-compact open and `j' : U ⟶ X` its base change, with `f' : U ⟶ V` and `a'` the right adjoint
of `Rf'_*`. Then, writing `φ : (j')^* ∘ a ⟶ a' ∘ j^*` for the map of [Stacks, Tag 0A9L]:
1. `a` carries every `Q ∈ D^+_QCoh(𝒪_Y)` supported on `Y ∖ V` to an object supported on `X ∖ U` if
   and only if `φ` is invertible on `D^+_QCoh(𝒪_Y)`;
2. the same holds with `D_QCoh(𝒪_Y)` in place of `D^+_QCoh(𝒪_Y)`;
3. if `a` commutes with direct sums, the conditions of (1) imply those of (2).
"Supported on `Y ∖ V`" is "restricts to zero on `V`". The square is an arbitrary cartesian square
along `j`. -/
@[stacks 0A9N]
theorem twistedInverseImageRestrictionMap_isIso_iff (sq : IsPullback j' f' f j) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    let a := twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    let φ := twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j') sq
    ((∀ Q : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow Q.obj →
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ↔
      ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K)) ∧
    ((∀ Q : quasiCoherentDerivedCategory Y,
        IsZero ((derivedRestrict j).obj Q.obj) → IsZero ((derivedRestrict j').obj (a.obj Q).obj)) ↔
      ∀ K : quasiCoherentDerivedCategory Y, IsIso (φ.app K)) ∧
    ((∀ α : Type u, PreservesColimitsOfShape (Discrete α) a) →
      (∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
        IsIso (φ.app K)) → ∀ K : quasiCoherentDerivedCategory Y, IsIso (φ.app K)) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace U := compactSpace_of_isPullback sq
  refine ⟨isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap_of_isBoundedBelow
    j' f' f j _ _ _ _ sq, ?_, ?_⟩
  · exact isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap j' f' f j _ _ _ _ sq
  · intro _ h K
    refine (isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap j' f' f j _ _ _ _
      sq).1 (fun Q hQ => isZero_restrict_twistedInverseImage_of_isBoundedBelow j' f j _
      isBoundedBelow_of_isCompactObject ?_ Q hQ) K
    exact (isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap_of_isBoundedBelow
      j' f' f j _ _ _ _ sq).2 h

end Qcqs

end Stacks.Duality

end
