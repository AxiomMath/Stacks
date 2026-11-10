module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# A function with a prescribed factorization along each special-fibre component

In the vanishing situation there is a nonzero element of the maximal ideal of the base whose
pullback to the source, at a suitable closed point of each irreducible component of the special
fibre, factors with one factor in the local maximal ideal restricting to a nonzero function on
that component. The point can be taken off all the other components. Every irreducible component
of the special fibre is assumed to have dimension one, as in the discussion following
Situation 0AX8.

## Main definitions

* `AlgebraicGeometry.VanishingSituation.componentInSource` regards an irreducible component of
  the special fibre as a subset of the source of the modification.
* `AlgebraicGeometry.VanishingSituation.componentScheme` equips that subset with its reduced
  induced closed subscheme structure, so that it has local rings.

## Main results

* `AlgebraicGeometry.VanishingSituation.exists_ne_zero_mem_maximalIdeal_factorization`
  produces the element of the maximal ideal together with the points and the factorizations.

## References

* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

/-- The image in the source of an irreducible component of the special fibre. -/
abbrev componentInSource (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) : Set V.X :=
  V.f.fiberι V.closedPoint '' V.component i

/-- The closure in the source of an irreducible component of the special fibre. -/
def componentClosed (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) : Closeds V.X :=
  .closure (componentInSource V i)

/-- An irreducible component of the special fibre, with its reduced induced closed subscheme
structure inside the source of the modification. -/
def componentScheme (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)).subscheme

private theorem fiberι_isClosedImmersion (V : VanishingSituation.{u}) :
    IsClosedImmersion (V.f.fiberι V.closedPoint) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Hom.range_fiberι]
  exact (IsLocalRing.isClosed_singleton_closedPoint V.A).preimage V.f.continuous

private theorem componentInSource_isClosed (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) : IsClosed (componentInSource V i) := by
  let s := V.f.fiberι V.closedPoint
  have : IsClosedImmersion s := fiberι_isClosedImmersion V
  exact s.isClosedEmbedding.isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents i))

private theorem componentClosed_coe (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    (componentClosed V i : Set V.X) = componentInSource V i := by
  change closure (componentInSource V i) = componentInSource V i
  exact closure_eq_iff_isClosed.mpr (componentInSource_isClosed V i)

private theorem componentScheme_support (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    ((Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)).support : Set V.X) =
      componentInSource V i := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, componentClosed_coe]

private theorem fiberι_ker_le_componentIdeal (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    (V.f.fiberι V.closedPoint).ker ≤
      Scheme.IdealSheafData.vanishingIdeal (componentClosed V i) := by
  have : IsClosedImmersion (V.f.fiberι V.closedPoint) := fiberι_isClosedImmersion V
  apply (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).mp
  change (componentClosed V i : Set V.X) ⊆
    (((V.f.fiberι V.closedPoint).ker).support : Set V.X)
  rw [componentClosed_coe, Scheme.Hom.support_ker]
  exact Set.image_subset_iff.mpr fun x _ => subset_closure ⟨x, rfl⟩

private noncomputable def componentSchemeHomeo (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) : componentScheme V i ≃ₜ V.component i := by
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  let e₁ : I.subscheme ≃ₜ I.support :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso I.subschemeIso)).trans I.gluedHomeo
  let e₂ : I.support ≃ₜ componentInSource V i :=
    Homeomorph.setCongr (componentScheme_support V i)
  let s := V.f.fiberι V.closedPoint
  haveI : IsClosedImmersion s := fiberι_isClosedImmersion V
  let e₃ : V.component i ≃ₜ componentInSource V i :=
    s.isClosedEmbedding.isEmbedding.homeomorphImage (V.component i)
  change I.subscheme ≃ₜ V.component i
  exact e₁.trans (e₂.trans e₃.symm)

private theorem exists_closed_point_on_component_only (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    ∃ x : V.specialFiber, x ∈ V.component i ∧ IsClosed ({x} : Set V.specialFiber) ∧
      ∀ j : Fin V.numberOfComponents, j ≠ i → x ∉ V.component j := by
  classical
  let C := V.component i
  have hC := V.component_mem_irreducibleComponents i
  let η := hC.1.genericPoint
  have hgen : IsGenericPoint η C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hηmem : η ∈ C := hgen.mem
  have hηnot (j : Fin V.numberOfComponents) (hji : j ≠ i) : η ∉ V.component j := by
    intro hηj
    have hsub : C ⊆ V.component j :=
      hgen.mem_closed_set_iff
        (isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents j))
        |>.mp hηj
    have hrev : V.component j ⊆ C := hC.2 (V.component_mem_irreducibleComponents j).1 hsub
    have heq : C = V.component j := Set.Subset.antisymm hsub hrev
    exact hji (V.component_injective heq).symm
  let T : Set V.specialFiber := ⋃ j, if j = i then ∅ else V.component j
  have hT : IsClosed T := by
    apply isClosed_iUnion_of_finite
    intro j
    split_ifs
    · exact isClosed_empty
    · exact isClosed_of_mem_irreducibleComponents _
        (V.component_mem_irreducibleComponents j)
  have hηT : η ∉ T := by
    intro ht
    rcases Set.mem_iUnion.mp ht with ⟨j, hj⟩
    by_cases hji : j = i
    · simp [hji] at hj
    · exact hηnot j hji (by simpa [hji] using hj)
  let U : Set V.specialFiber := C ∩ Tᶜ
  have hU : IsLocallyClosed U := by
    change IsLocallyClosed (C ∩ Tᶜ)
    exact (isClosed_of_mem_irreducibleComponents C hC).isLocallyClosed.inter
      hT.isOpen_compl.isLocallyClosed
  have hUne : U.Nonempty := ⟨η, hηmem, hηT⟩
  have : LocallyOfFiniteType V.f := V.modification.isProper.toLocallyOfFiniteType
  have : JacobsonSpace V.specialFiber := inferInstance
  obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints hUne hU
  exact ⟨x, hx.1, mem_closedPoints_iff.mp hxclosed, fun j hji hxj =>
    hx.2 (Set.mem_iUnion.mpr ⟨j, by simp [hji, hxj]⟩)⟩

private theorem exists_componentScheme_point (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    ∃ y : componentScheme V i,
      IsClosed ({(Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι y} : Set V.X) ∧
      (Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι y ∈ componentInSource V i ∧
      ∀ j : Fin V.numberOfComponents, j ≠ i →
        (Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι y ∉ componentInSource V j := by
  obtain ⟨x, hx, hxclosed, hxnot⟩ := exists_closed_point_on_component_only V i
  let s := V.f.fiberι V.closedPoint
  let xX := s x
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  have hxsource : xX ∈ componentInSource V i := ⟨x, hx, rfl⟩
  have hrange : xX ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι, componentScheme_support]
    exact hxsource
  obtain ⟨y, hy⟩ := hrange
  have hclosedX : IsClosed ({xX} : Set V.X) := by
    have : IsClosedImmersion s := fiberι_isClosedImmersion V
    have h := s.isClosedEmbedding.isClosedMap ({x} : Set V.specialFiber) hxclosed
    simpa [xX] using h
  refine ⟨y, ?_, ?_, ?_⟩
  · change IsClosed ({I.subschemeι y} : Set V.X)
    rw [hy]
    exact hclosedX
  · change I.subschemeι y ∈ componentInSource V i
    rw [hy]
    exact hxsource
  · intro j hji hbad
    change I.subschemeι y ∈ componentInSource V j at hbad
    rw [hy] at hbad
    change s x ∈ s '' V.component j at hbad
    rcases hbad with ⟨z, hz, hzx⟩
    have : IsClosedImmersion s := fiberι_isClosedImmersion V
    have hzx' : z = x := s.isClosedEmbedding.injective (by simpa [xX] using hzx)
    subst z
    exact hxnot j hji hz

private noncomputable def componentSchemeToResidueField (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    componentScheme V i ⟶ Spec (.of (V.base.residueField V.closedPoint)) := by
  let s := V.f.fiberι V.closedPoint
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  let J := s.ker
  haveI : IsClosedImmersion s := fiberι_isClosedImmersion V
  have hJI : J ≤ I := fiberι_ker_le_componentIdeal V i
  let q : I.subscheme ⟶ J.subscheme := Scheme.IdealSheafData.inclusion hJI
  let e : J.subscheme ≅ V.specialFiber := (asIso s.toImage).symm
  change I.subscheme ⟶ Spec (.of (V.base.residueField V.closedPoint))
  exact q ≫ e.hom ≫ V.f.fiberToSpecResidueField V.closedPoint

private theorem componentSchemeToResidueField_locallyOfFiniteType
    (V : VanishingSituation.{u}) (i : Fin V.numberOfComponents) :
    LocallyOfFiniteType (componentSchemeToResidueField V i) := by
  let s := V.f.fiberι V.closedPoint
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  let J := s.ker
  have : IsClosedImmersion s := fiberι_isClosedImmersion V
  have hJI : J ≤ I := fiberι_ker_le_componentIdeal V i
  let q : I.subscheme ⟶ J.subscheme := Scheme.IdealSheafData.inclusion hJI
  let e : J.subscheme ≅ V.specialFiber := (asIso s.toImage).symm
  have : LocallyOfFiniteType V.f := V.modification.isProper.toLocallyOfFiniteType
  have : LocallyOfFiniteType q := inferInstance
  have : LocallyOfFiniteType e.hom := inferInstance
  have : LocallyOfFiniteType (V.f.fiberToSpecResidueField V.closedPoint) := by
    change LocallyOfFiniteType (Limits.pullback.snd V.f
      (V.base.fromSpecResidueField V.closedPoint))
    infer_instance
  change LocallyOfFiniteType (q ≫ e.hom ≫ V.f.fiberToSpecResidueField V.closedPoint)
  infer_instance

private theorem componentScheme_point_isClosed (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) (y : componentScheme V i)
    (hy : IsClosed ({(Scheme.IdealSheafData.vanishingIdeal
      (componentClosed V i)).subschemeι y} : Set V.X)) :
    IsClosed ({y} : Set (componentScheme V i)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  have hpre : I.subschemeι ⁻¹' ({I.subschemeι y} : Set V.X) = {y} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact I.subschemeι.isClosedEmbedding.injective.eq_iff
  change IsClosed ({y} : Set I.subscheme)
  rw [← hpre]
  exact (I.subschemeι).isClosedEmbedding.isClosed_preimage _ hy

private theorem maximalIdeal_ne_bot_of_ringKrullDim_ne_zero {R : Type*} [CommRing R]
    [IsLocalRing R] (h : ringKrullDim R ≠ 0) : IsLocalRing.maximalIdeal R ≠ ⊥ := fun hm =>
  h (ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm))

private theorem structureSheaf_toStalk_eqToHom {R : Type u} [CommRing R]
    {x y : PrimeSpectrum.Top R} (h : x = y) :
    StructureSheaf.toStalk R x ≫
      eqToHom (congrArg (fun z : PrimeSpectrum.Top R =>
        (structurePresheafInCommRingCat R).stalk z) h) = StructureSheaf.toStalk R y := by
  cases h
  simp

private theorem exists_nonzero_maximalIdeal_element_at_component_point
    (V : VanishingSituation.{u})
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) (y : componentScheme V i)
    (hy : IsClosed ({(Scheme.IdealSheafData.vanishingIdeal
      (componentClosed V i)).subschemeι y} : Set V.X)) :
    ∃ g : V.X.presheaf.stalk
        ((Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)).subschemeι y),
      g ∈ IsLocalRing.maximalIdeal _ ∧
      (Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)).subschemeι.stalkMap y g ≠ 0 := by
  let C := componentScheme V i
  let fC := componentSchemeToResidueField V i
  have : LocallyOfFiniteType V.f := V.modification.isProper.toLocallyOfFiniteType
  have : LocallyOfFiniteType fC := componentSchemeToResidueField_locallyOfFiniteType V i
  have : IrreducibleSpace C :=
    (componentSchemeHomeo V i).irreducibleSpace_iff.mpr
      (Subtype.irreducibleSpace (V.component_mem_irreducibleComponents i).1)
  have hdimC : topologicalKrullDim C = 1 := by
    calc
      topologicalKrullDim C = topologicalKrullDim (V.component i) :=
        IsHomeomorph.topologicalKrullDim_eq _ (componentSchemeHomeo V i).isHomeomorph
      _ = 1 := hdim i
  have hclosedC : IsClosed ({y} : Set C) := componentScheme_point_isClosed V i y hy
  have hringdim : ringKrullDim (C.presheaf.stalk y) = 1 := by
    calc
      ringKrullDim (C.presheaf.stalk y) = topologicalKrullDimAt C y :=
        (AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk
          (V.base.residueField V.closedPoint) C fC y hclosedC).symm
      _ = topologicalKrullDim C :=
        (AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
          (V.base.residueField V.closedPoint) C fC y).symm
      _ = 1 := hdimC
  let R := C.presheaf.stalk y
  have hmne : IsLocalRing.maximalIdeal R ≠ ⊥ :=
    maximalIdeal_ne_bot_of_ringKrullDim_ne_zero (by rw [hringdim]; norm_num)
  obtain ⟨t, ht, htne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmne
  let I := Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)
  have : IsClosedImmersion I.subschemeι := inferInstance
  obtain ⟨g, hg⟩ := I.subschemeι.stalkMap_surjective y t
  have hgmax : g ∈ IsLocalRing.maximalIdeal (V.X.presheaf.stalk (I.subschemeι y)) := by
    by_contra hnot
    have hunit : IsUnit g := IsLocalRing.notMem_maximalIdeal.mp hnot
    have hunit' : IsUnit ((I.subschemeι.stalkMap y).hom g) := hunit.map _
    have htunit : IsUnit t := by rw [← hg]; exact hunit'
    exact (IsLocalRing.notMem_maximalIdeal.mpr htunit) ht
  refine ⟨g, hgmax, fun hzero => htne ?_⟩
  rw [← hg]
  exact hzero

private theorem exists_fraction_for_stalk_element
    (V : VanishingSituation.{u}) (x : V.X)
    (g : V.X.presheaf.stalk x) (hg : g ≠ 0) :
    ∃ a b : V.A, a ≠ 0 ∧ b ≠ 0 ∧
      (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x) a =
        g * (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x) b := by
  let ηX := genericPoint V.X
  let ηS := genericPoint V.base
  have : IsIntegral V.X := V.modification.source_isIntegral
  have : IsIntegral V.base := by infer_instance
  have hηX : ηX ∈ genericPoints V.X := by simp [ηX, genericPoints_eq_singleton]
  have hη : V.f ηX = ηS := by
    have hmem := V.modification.isBirational.bijOn.1 hηX
    have hmem' : V.f ηX ∈ ({ηS} : Set V.base) := by
      simpa [ηS, genericPoints_eq_singleton] using hmem
    exact Set.mem_singleton_iff.mp hmem'
  have : IsIso (V.f.stalkMap ηX) :=
    V.modification.isBirational.isIso_stalkMap ηX hηX
  let q : V.base.functionField ⟶ V.X.functionField :=
    eqToHom (congrArg V.base.presheaf.stalk hη.symm) ≫ V.f.stalkMap ηX
  have : IsIso q := inferInstance
  let e : V.base.functionField ≃+* V.X.functionField :=
    RingEquiv.ofRingHom q.hom (inv q).hom
      (by ext z; simp)
      (by ext z; simp)
  let φ : V.A →+* V.X.functionField :=
    (StructureSheaf.toStalk V.A ηS ≫ q).hom
  let : Algebra V.A V.base.functionField :=
    (StructureSheaf.toStalk V.A ηS).hom.toAlgebra
  let : Algebra V.A V.X.functionField := φ.toAlgebra
  let eA : V.base.functionField ≃ₐ[V.A] V.X.functionField :=
    AlgEquiv.ofRingEquiv (f := e) (by intro a; rfl)
  have : IsFractionRing V.A V.base.functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of V.A)
  have : IsFractionRing V.A V.X.functionField := IsFractionRing.of_algEquiv eA
  let α : V.A →+* V.X.presheaf.stalk x :=
    (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom
  let τ := V.X.presheaf.stalkSpecializes (genericPoint_specializes x)
  let hfx := V.f.base.hom.map_specializes (genericPoint_specializes x)
  have hnat : V.base.presheaf.stalkSpecializes hfx ≫ V.f.stalkMap ηX =
      V.f.stalkMap x ≫ τ :=
    V.f.stalkSpecializes_stalkMap ηX x (genericPoint_specializes x)
  have hstalk : StructureSheaf.toStalk V.A (V.f x) ≫
      V.base.presheaf.stalkSpecializes hfx = StructureSheaf.toStalk V.A (V.f ηX) := by
    change StructureSheaf.toStalk V.A (V.f x) ≫
      (Spec.structureSheaf V.A).presheaf.stalkSpecializes hfx =
        StructureSheaf.toStalk V.A (V.f ηX)
    exact StructureSheaf.toStalk_stalkSpecializes hfx
  have hcast : StructureSheaf.toStalk V.A ηS ≫
      eqToHom (congrArg V.base.presheaf.stalk hη.symm) =
        StructureSheaf.toStalk V.A (V.f ηX) :=
    structureSheaf_toStalk_eqToHom hη.symm
  have hcat :
      StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x ≫ τ =
        StructureSheaf.toStalk V.A ηS ≫ q := by
    calc
      _ = StructureSheaf.toStalk V.A (V.f x) ≫
          (V.base.presheaf.stalkSpecializes hfx ≫ V.f.stalkMap ηX) :=
              congrArg (fun k => StructureSheaf.toStalk V.A (V.f x) ≫ k) hnat.symm
      _ = (StructureSheaf.toStalk V.A (V.f x) ≫
          V.base.presheaf.stalkSpecializes hfx) ≫ V.f.stalkMap ηX :=
              (Category.assoc _ _ _).symm
      _ = StructureSheaf.toStalk V.A ηS ≫
          (eqToHom (congrArg V.base.presheaf.stalk hη.symm) ≫ V.f.stalkMap ηX) := by
              rw [hstalk, ← hcast]
              exact Category.assoc _ _ _
      _ = StructureSheaf.toStalk V.A ηS ≫ q := by
              rfl
  have hmap : (algebraMap (V.X.presheaf.stalk x) V.X.functionField).comp α = φ :=
    congrArg CommRingCat.Hom.hom hcat
  let γ : V.A →+* V.X.functionField := algebraMap V.A V.X.functionField
  let z := algebraMap (V.X.presheaf.stalk x) V.X.functionField g
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective V.A z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbk : γ b ≠ 0 := by
    intro hzero
    apply hb0
    exact (IsFractionRing.injective V.A V.X.functionField) (by simpa [γ] using hzero)
  have hmul : γ a = (algebraMap (V.X.presheaf.stalk x) V.X.functionField g) * γ b := by
    calc
      γ a = (γ a / γ b) * γ b := by field_simp
      _ = (algebraMap (V.X.presheaf.stalk x) V.X.functionField g) * γ b := by rw [hdiv]
  have hmap_apply (r : V.A) :
      (algebraMap (V.X.presheaf.stalk x) V.X.functionField) (α r) = γ r := by
    change (algebraMap (V.X.presheaf.stalk x) V.X.functionField) (α r) = φ r
    simpa only [RingHom.comp_apply] using
      congrArg (fun k : V.A →+* V.X.functionField => k r) hmap
  have hlocal : α a = g * α b := by
    apply (IsFractionRing.injective (V.X.presheaf.stalk x) V.X.functionField)
    calc
      (algebraMap (V.X.presheaf.stalk x) V.X.functionField) (α a) = γ a :=
        hmap_apply a
      _ = (algebraMap (V.X.presheaf.stalk x) V.X.functionField g) * γ b := hmul
      _ = (algebraMap (V.X.presheaf.stalk x) V.X.functionField g) *
          (algebraMap (V.X.presheaf.stalk x) V.X.functionField) (α b) := by
            rw [hmap_apply b]
      _ = (algebraMap (V.X.presheaf.stalk x) V.X.functionField) (g * α b) := by simp
  have hane : a ≠ 0 := by
    intro ha
    subst a
    have hgk : algebraMap (V.X.presheaf.stalk x) V.X.functionField g ≠ 0 := by
      intro hzero
      apply hg
      exact (IsFractionRing.injective (V.X.presheaf.stalk x) V.X.functionField)
        (by simpa using hzero)
    have hbk' : algebraMap (V.X.presheaf.stalk x) V.X.functionField (α b) ≠ 0 := by
      rw [hmap_apply b]
      exact hbk
    have hprod0 : g * α b = 0 := by
      simpa using hlocal.symm
    have hprodmap :
        algebraMap (V.X.presheaf.stalk x) V.X.functionField g *
          algebraMap (V.X.presheaf.stalk x) V.X.functionField (α b) = 0 := by
      simpa [map_mul] using congrArg (algebraMap (V.X.presheaf.stalk x) V.X.functionField) hprod0
    exact mul_ne_zero hgk hbk' hprodmap
  exact ⟨a, b, hane, hb0, hlocal⟩

/-- A nonzero element of the maximal ideal which, along every irreducible component of the special
fibre, admits at some closed point of that component and of no other a factorization one factor of
which lies in the local maximal ideal and restricts to a nonzero function on the component. -/
@[stacks 0AX9 "under the standing observation following Situation 0AX8 that every irreducible
component of the special fibre has dimension one"]
theorem exists_ne_zero_mem_maximalIdeal_factorization
    (V : VanishingSituation.{u})
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1) :
    ∃ a : V.A, a ≠ 0 ∧ a ∈ V.maximalIdeal ∧
      ∀ i : Fin V.numberOfComponents,
        ∃ y : componentScheme V i,
          IsClosed
              ({(Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y} : Set V.X) ∧
          (Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι y ∈ componentInSource V i ∧
          (∀ j : Fin V.numberOfComponents, j ≠ i →
            (Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y ∉ componentInSource V j) ∧
          ∃ g h : V.X.presheaf.stalk
              ((Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y),
            g ∈ IsLocalRing.maximalIdeal _ ∧
            (Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι.stalkMap y g ≠ 0 ∧
            ((StructureSheaf.toStalk V.A (V.f _) ≫ V.f.stalkMap _) a = g * h) := by
  classical
  have hmne : V.maximalIdeal ≠ ⊥ :=
    maximalIdeal_ne_bot_of_ringKrullDim_ne_zero (by rw [V.dimension_two]; norm_num)
  obtain ⟨c, hc, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmne
  have hdata : ∀ i : Fin V.numberOfComponents,
      ∃ y : componentScheme V i,
        IsClosed ({(Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι y} : Set V.X) ∧
        (Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι y ∈ componentInSource V i ∧
        (∀ j : Fin V.numberOfComponents, j ≠ i →
          (Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι y ∉ componentInSource V j) ∧
        ∃ g : V.X.presheaf.stalk
            ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι y),
          g ∈ IsLocalRing.maximalIdeal _ ∧
          (Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι.stalkMap y g ≠ 0 := by
    intro i
    obtain ⟨y, hyclosed, hysource, hynot⟩ := exists_componentScheme_point V i
    obtain ⟨g, hgmax, hgne⟩ :=
      exists_nonzero_maximalIdeal_element_at_component_point V hdim i y hyclosed
    exact ⟨y, hyclosed, hysource, hynot, g, hgmax, hgne⟩
  choose y hyclosed hysource hynot g hgmax hgne using hdata
  have hfractions : ∀ i : Fin V.numberOfComponents,
      ∃ a b : V.A, a ≠ 0 ∧ b ≠ 0 ∧
        (StructureSheaf.toStalk V.A
          (V.f ((Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι (y i))) ≫
          V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι (y i))) a =
          g i * (StructureSheaf.toStalk V.A
            (V.f ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι (y i))) ≫
            V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι (y i))) b := by
    intro i
    have hgnz : g i ≠ 0 := by
      intro hg0
      apply hgne i
      rw [hg0]
      simp
    exact exists_fraction_for_stalk_element V
      ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i)) (g i) hgnz
  choose a₀ b₀ ha₀ hb₀ hfactor using hfractions
  let a := c * ∏ i : Fin V.numberOfComponents, a₀ i
  let ρ (i : Fin V.numberOfComponents) : V.A →+*
      V.X.presheaf.stalk
        ((Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι (y i)) :=
    (StructureSheaf.toStalk V.A
      (V.f ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i))) ≫
      V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i))).hom
  let hi (i : Fin V.numberOfComponents) :=
    ρ i c * (ρ i (b₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j))
  have hprodne : (∏ i : Fin V.numberOfComponents, a₀ i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ha₀ i)
  have hane : a ≠ 0 := mul_ne_zero hcne hprodne
  have hamem : a ∈ V.maximalIdeal := by
    dsimp [a]
    simpa [mul_comm] using
      (Ideal.mul_mem_left V.maximalIdeal (∏ i : Fin V.numberOfComponents, a₀ i) hc)
  refine ⟨a, hane, hamem, ?_⟩
  · intro i
    refine ⟨y i, hyclosed i, hysource i, hynot i, g i, hi i, hgmax i, hgne i, ?_⟩
    have hprod : ρ i (∏ j : Fin V.numberOfComponents, a₀ j) =
        ρ i (a₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j) := by
      rw [map_prod]
      exact (Finset.mul_prod_erase Finset.univ (fun j => ρ i (a₀ j))
        (Finset.mem_univ i)).symm
    change ρ i a = g i * hi i
    calc
      ρ i a = ρ i c * ρ i (∏ j : Fin V.numberOfComponents, a₀ j) := by
        simp [a]
      _ = ρ i c * (ρ i (a₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j)) := by
        rw [hprod]
      _ = g i * hi i := by
        rw [hfactor i]
        simp only [hi]
        ring

end VanishingSituation

end AlgebraicGeometry

end
