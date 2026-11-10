module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexAffineVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.AffineOfNoProperComponent
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents

/-!
# `H²_c(U, R j_* F) = 0` on a curve over an algebraically closed field

Let `Ω` be an algebraically closed field, `g : U ⟶ Spec Ω` separated of finite type with `U` of
dimension at most one, `i : Z ⟶ U` a closed immersion with `Z` finite over `Ω` meeting every
irreducible component of `U` with at least two points, and `j : U₀ ⟶ U` the open complement.
For every sheaf `F` of `ℤ/N`-modules on `U₀`,

`H²(R g_!(R j_* F)) = 0`.

The compactly supported cohomology does not depend on the compactification
([Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I),
`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`), so it is computed through the
scheme-theoretic closure `X̄` of `U` in a compactification
(`AlgebraicGeometry.CompactificationOf.schemeTheoreticClosure`), a proper curve with `U` dense.
The open `V = X̄ ∖ Z` contains the boundary `X̄ ∖ U` and meets `U` in `U₀`; it is affine by
[Tag 0A28](https://stacks.math.columbia.edu/tag/0A28): an irreducible component of `V` of
dimension one which were proper would be closed in `X̄`, hence a component of `X̄`, hence the
closure of a component of `U`, which meets `Z`
(`AlgebraicGeometry.not_isProper_componentIdealSheafData_compl`). Then
`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_derivedDirectImage_of_isAffine`
applies.

This is the vanishing on the geometric fibres behind the Gysin map of the Leray step of the
reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `AlgebraicGeometry.CompactificationOf.schemeTheoreticClosure`.

## Main results

* `AlgebraicGeometry.not_isProper_componentIdealSheafData_compl`.
* `Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed`.

## Implementation notes

`AlgebraicGeometry.CompactificationOf.closure` is the same construction for an open immersion
over a Noetherian base; here `f` is arbitrary with quasi-compact compactifying immersion. The
statements on derived categories are made in the standard model `HasDerivedCategory.standard`, in
which `Stacks.EtaleCohomology.derivedLowerShriek` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))
  [QuasiCompact j.immersion]

/-- **The scheme-theoretic closure of `X` in a compactification `j : X ⟶ X̄` of `f`**, as a
compactification of `f`: the open immersion of `X` into the scheme-theoretic image of `j`, a closed
subscheme of `X̄` and hence proper over `Y`. -/
def schemeTheoreticClosure : CompactificationOf (Over.mk f) :=
  have h : j.immersion.toImage ≫ j.immersion.imageι ≫ j.toBase = f := by
    rw [Scheme.Hom.toImage_imageι_assoc, immersion_toBase]
  ⟨StructuredArrow.mk (Y := Over.mk (j.immersion.imageι ≫ j.toBase))
      (Over.homMk (U := Over.mk f) j.immersion.toImage h),
    ⟨inferInstanceAs (IsOpenImmersion j.immersion.toImage),
      inferInstanceAs (IsProper (j.immersion.imageι ≫ j.toBase))⟩⟩

/-- The open immersion of the scheme-theoretic closure is the corestriction of `j` to its
scheme-theoretic image. -/
@[simp]
lemma schemeTheoreticClosure_immersion :
    j.schemeTheoreticClosure.immersion = j.immersion.toImage := rfl

/-- The structure morphism of the scheme-theoretic closure is the inclusion of the
scheme-theoretic image of `j` followed by the structure morphism of `j`. -/
@[simp]
lemma schemeTheoreticClosure_toBase :
    j.schemeTheoreticClosure.toBase = j.immersion.imageι ≫ j.toBase := rfl

/-- The interior of the scheme-theoretic closure is dense. -/
lemma denseRange_schemeTheoreticClosure_immersion :
    DenseRange j.schemeTheoreticClosure.immersion.base :=
  j.immersion.toImage.denseRange

end AlgebraicGeometry.CompactificationOf

namespace AlgebraicGeometry

/-- The range of `f ≫ g` is closed when `f ≫ g ≫ h` is proper and `h` is separated. -/
private theorem isClosed_range_comp_of_isProper_comp_comp {X Y Z W : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ W) [IsSeparated h] [IsProper (f ≫ g ≫ h)] :
    IsClosed (Set.range (f ≫ g).base) := by
  have : IsProper ((f ≫ g) ≫ h) := by rwa [Category.assoc]
  have : IsProper (f ≫ g) := IsProper.of_comp (f ≫ g) h
  exact (f ≫ g).isClosedMap.isClosed_range

/-- **A one-dimensional component of the complement of a closed set meeting every component is
not proper.** Let `p : X ⟶ Spec k` be proper, `e : U ⟶ X` an open immersion with dense image,
and `Zs ⊆ X` meeting (the image of) every irreducible component of `U` with at least two points.
Then no irreducible component `T` of the open `V = X ∖ Zs` with at least two points is proper
over `k`: it would be closed in `X`, hence a component of `X`
(`closure_image_mem_irreducibleComponents_of_isOpen`), whose generic point lies in the dense
`e(U)`; so `e⁻¹ T` is a component of `U`, with at least two points (a closed point of the
Jacobson scheme `X` in `T ∩ e(U)` and the generic point), meeting `Zs`, which is disjoint
from `V`. -/
theorem not_isProper_componentIdealSheafData_compl {k : Type u} [Field k] {X U : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (e : U ⟶ X) [IsOpenImmersion e]
    (he : DenseRange e.base) {Zs : Set X} (hfib : ∀ C ∈ irreducibleComponents U,
      (∃ x ∈ C, ∃ y ∈ C, x ≠ y) → (C ∩ e.base ⁻¹' Zs).Nonempty)
    (V : X.Opens) (hV : (V : Set X) = Zsᶜ) (T : irreducibleComponents V)
    (hT : ∃ a ∈ T.1, ∃ b ∈ T.1, a ≠ b) :
    ¬ IsProper ((Stacks.AffineNoProperComponent.componentIdealSheafData T).subschemeι ≫
      V.ι ≫ p) := by
  intro hP
  set ιT := (Stacks.AffineNoProperComponent.componentIdealSheafData T).subschemeι
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  set S : Set X := Subtype.val '' T.1
  have hrange : Set.range (ιT ≫ V.ι).base = S := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Stacks.AffineNoProperComponent.range_subschemeι_componentIdealSheafData]
    rfl
  have hSc : IsClosed S := hrange ▸ isClosed_range_comp_of_isProper_comp_comp ιT V.ι p
  have hScomp : S ∈ irreducibleComponents X := by
    have := closure_image_mem_irreducibleComponents_of_isOpen V.isOpen T.2
    convert this using 1
    exact hSc.closure_eq.symm
  -- the generic point of `S` lies in the dense open `e(U)`
  set η := hScomp.1.genericPoint
  have hη : IsGenericPoint η S := by
    simpa [hSc.closure_eq] using hScomp.1.isGenericPoint_genericPoint_closure
  have hηgen : η ∈ genericPoints X := by
    change closure {η} ∈ irreducibleComponents X
    rw [hη.def]
    exact hScomp
  have hηe : η ∈ Set.range e.base := by
    have := genericPoints_mem_of_dense e.opensRange
      (by rw [Scheme.Hom.coe_opensRange]; exact he) ⟨η, hηgen⟩
    rwa [← Scheme.Hom.coe_opensRange]
  have hηS : η ∈ S := hη.mem
  -- `S ∩ e(U)` contains a closed point, distinct from `η`
  obtain ⟨x, ⟨hxS, hxe⟩, hxcl⟩ := nonempty_inter_closedPoints (Z := S ∩ Set.range e.base)
    ⟨η, hηS, hηe⟩ (hSc.isLocallyClosed.inter e.isOpenEmbedding.isOpen_range.isLocallyClosed)
  have hxη : x ≠ η := by
    intro hxη
    obtain ⟨a, ha, b, hb, hab⟩ := hT
    have hcl : closure {η} = {η} := (mem_closedPoints_iff.1 (hxη ▸ hxcl)).closure_eq
    exact hab (Subtype.val_injective (by
      have h1 : Subtype.val a ∈ S := ⟨a, ha, rfl⟩
      have h2 : Subtype.val b ∈ S := ⟨b, hb, rfl⟩
      rw [← hη.def, hcl] at h1 h2
      exact h1.trans h2.symm))
  -- the component `e⁻¹ S` of `U` meets `Zs`, which `S ⊆ V` avoids
  have hC := preimage_mem_irreducibleComponents hScomp e.isOpenEmbedding ⟨η, hηS, hηe⟩
  obtain ⟨η', hη'⟩ := hηe
  obtain ⟨x', hx'⟩ := hxe
  obtain ⟨z, hzC, hzZ⟩ := hfib _ hC ⟨η', by simpa [hη'] using hηS, x', by simpa [hx'] using hxS,
    fun h => hxη (by rw [← hx', ← hη', h])⟩
  obtain ⟨t, -, ht⟩ := hzC
  have ht2 : Subtype.val t ∈ Zsᶜ := hV ▸ t.2
  exact ht2 (ht ▸ hzZ)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **`H²(R g_!(R j_* F)) = 0` on a curve over an algebraically closed field.** Let
`g : U ⟶ Spec Ω` be separated of finite type with `U` of dimension at most one, `i : Z ⟶ U` a
closed immersion with `Z` finite over `Ω` meeting every irreducible component of `U` with at
least two points, and `j : U₀ ⟶ U` an open immersion onto the complement of `Z`. For every
sheaf `F` of `ℤ/N`-modules on `U₀` and every compactification `jg` of `g`,
`H²(R g_!(R j_* F)) = 0`. -/
theorem isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] {U Z U₀ : Scheme.{u}} (g : U ⟶ Spec (.of Ω)) [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (jg : CompactificationOf (Over.mk g))
    (i : Z ⟶ U) [IsClosedImmersion i] [IsFinite (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (hdim : topologicalKrullDim U ≤ 1)
    (hfib : ∀ C ∈ irreducibleComponents U, (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
      (C ∩ Set.range i.base).Nonempty)
    (N : ℕ) [NeZero N] (F : EtaleModules.{u, 0} (ZMod N) U₀) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} g jg (ZMod N)).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  set K := (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j).obj
    ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod N) U₀) 0).obj F)
  have hK : isTorsionPlus.{u, 0} (ZMod N) U K := by
    refine isTorsionPlus_of_nsmul_id_eq_zero K N (NeZero.pos N) ?_
    have hF : N • 𝟙 F = 0 := by
      rw [nsmul_id_sheaf_zmod_eq F (a := N) (b := 0) (by simp), zero_smul]
    rw [← CategoryTheory.Functor.map_id (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j),
      ← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, ← Functor.map_nsmul, hF, Functor.map_zero, Functor.map_zero]
  -- compute through the scheme-theoretic closure (Tag 0F7I)
  let jc := jg.schemeTheoreticClosure
  have e0 := (derivedLowerShriekCompactificationIso g jc jg (ZMod N)).app ⟨K, hK⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso e0.symm)
  set e := jc.immersion
  have he : DenseRange e.base := jg.denseRange_schemeTheoreticClosure_immersion
  have : IsProper (i ≫ e ≫ jc.toBase) := by
    rw [CompactificationOf.immersion_toBase]; infer_instance
  set Zs := Set.range (i ≫ e).base
  have hZs : IsClosed Zs := isClosed_range_comp_of_isProper_comp_comp i e jc.toBase
  let V : jc.space.Opens := ⟨Zsᶜ, hZs.isOpen_compl⟩
  have hD : IsClosed (Set.range e.base)ᶜ := e.isOpenEmbedding.isOpen_range.isClosed_compl
  let ID := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range e.base)ᶜ, hD⟩ : TopologicalSpace.Closeds jc.space)
  let iD := ID.subschemeι
  have hiD : Set.range iD.base = (Set.range e.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hei : Set.range e.base = (Set.range iD.base)ᶜ := by rw [hiD, compl_compl]
  have hie : ∀ z, (i ≫ e).base z = e.base (i.base z) := fun z => Scheme.Hom.comp_apply _ _ _
  have hcv : Set.range iD.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι, hiD]
    rintro x hx ⟨z, rfl⟩
    exact hx ⟨i.base z, (hie z).symm⟩
  let c := IsOpenImmersion.lift V.ι iD hcv
  have hc : c ≫ V.ι = iD := IsOpenImmersion.lift_fac _ _ _
  have hφ : Set.range j.base = Set.range (e ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι, hj]
    ext x
    change x ∉ Set.range i.base ↔ e.base x ∉ Zs
    constructor
    · rintro hx ⟨z, hz⟩
      exact hx ⟨z, e.isOpenEmbedding.injective (by rw [← hie z, hz])⟩
    · rintro hx ⟨z, rfl⟩
      exact hx ⟨z, hie z⟩
  let φ := IsOpenImmersion.isoOfRangeEq j (e ⁻¹ᵁ V).ι hφ
  let e' := φ.hom ≫ (e ∣_ V)
  have sq : IsPullback e' j V.ι e := by
    have s : IsPullback φ.hom j (e ⁻¹ᵁ V).ι (𝟙 U) :=
      IsPullback.of_horiz_isIso ⟨by simp [φ]⟩
    have := s.paste_horiz (isPullback_morphismRestrict e V)
    simpa using this
  have hw : ∀ x, V.ι.base (e'.base x) = e.base (j.base x) := fun x => by
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
  have hcw : ∀ d, V.ι.base (c.base d) = iD.base d := fun d => by
    rw [← Scheme.Hom.comp_apply, hc]
  have hce : Set.range e'.base = (Set.range c.base)ᶜ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩ ⟨d, hd⟩
      have h1 : iD.base d ∈ (Set.range e.base)ᶜ := hiD ▸ ⟨d, rfl⟩
      exact h1 ⟨j.base x, by rw [← hw, ← hd, hcw]⟩
    · intro hy
      have hye : V.ι.base y ∈ Set.range e.base := by
        by_contra h
        have h' : V.ι.base y ∈ (Set.range e.base)ᶜ := h
        rw [← hiD] at h'
        obtain ⟨d, hd⟩ := h'
        exact hy ⟨d, V.ι.isOpenEmbedding.injective (by rw [hcw, hd])⟩
      obtain ⟨x', hx'⟩ := hye
      have hx'j : x' ∈ Set.range j.base := by
        rw [hj]
        rintro ⟨z, rfl⟩
        have hyV : V.ι.base y ∈ (V : Set jc.space) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩
        exact hyV ⟨z, by rw [hie z, hx']⟩
      obtain ⟨x, rfl⟩ := hx'j
      exact ⟨x, V.ι.isOpenEmbedding.injective (by rw [hw, hx'])⟩
  -- `V` is an affine curve (Tag 0A28)
  have : CompactSpace jc.space := QuasiCompact.compactSpace_of_compactSpace jc.toBase
  have hdimX : topologicalKrullDim jc.space ≤ 1 :=
    topologicalKrullDim_le_one_of_isOpenImmersion_of_denseRange jc.toBase e he hdim
  have hdimV : topologicalKrullDim V ≤ 1 :=
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdimX
  have : QuasiCompact (V.ι ≫ jc.toBase) := by
    have : IsLocallyNoetherian jc.space := LocallyOfFiniteType.isLocallyNoetherian jc.toBase
    have : IsNoetherian jc.space := ⟨⟩
    infer_instance
  have hfib' : ∀ C ∈ irreducibleComponents U, (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
      (C ∩ e.base ⁻¹' Zs).Nonempty := by
    intro C hC h2
    obtain ⟨x, hxC, z, rfl⟩ := hfib C hC h2
    exact ⟨i.base z, hxC, z, hie z⟩
  have : IsAffine V := by
    refine
      Stacks.AffineNoProperComponent.isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper
        Ω (V.ι ≫ jc.toBase) hdimV fun T hT => ?_
    refine not_isProper_componentIdealSheafData_compl jc.toBase e he hfib' V rfl T ?_
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    let ιT := (Stacks.AffineNoProperComponent.componentIdealSheafData T).subschemeι
    have : Subsingleton (Stacks.AffineNoProperComponent.componentIdealSheafData T).subscheme := by
      refine ⟨fun a b => ιT.isClosedEmbedding.injective ?_⟩
      have hr := Stacks.AffineNoProperComponent.range_subschemeι_componentIdealSheafData T
      exact h _ (hr ▸ ⟨a, rfl⟩) _ (hr ▸ ⟨b, rfl⟩)
    have : DiscreteTopology (Stacks.AffineNoProperComponent.componentIdealSheafData T).subscheme :=
      Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology
      (Stacks.AffineNoProperComponent.componentIdealSheafData T).subscheme
    rw [hT] at h0
    exact absurd h0 (by decide)
  exact isZero_homology_two_derivedLowerShriek_derivedDirectImage_of_isAffine Ω g jc j iD hei V.ι
    c hc e' sq hce hdimV N F

end Stacks.EtaleCohomology
