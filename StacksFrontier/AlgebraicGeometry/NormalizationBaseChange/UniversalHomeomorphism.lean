module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksFrontier.AlgebraicGeometry.AffineUniversalHomeo.Basic
public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Comparison
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.UniversalHomeomorphismLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.FieldTheory.Separable.Basic
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The normalization base-change comparison is a universal homeomorphism

Let `X` be a scheme locally of finite type over a field `k` and let `K/k` be an extension of
fields.  The comparison morphism `AlgebraicGeometry.normalizationBaseChangeComparison` of
Tag 0C3N, from the normalization of `X_K` to the base change of the normalization of `X`, is a
universal homeomorphism, and it is an isomorphism when `K/k` is separable.

## Main results

* `AlgebraicGeometry.normalizationBaseChangeComparison_isUniversalHomeomorphism`
* `AlgebraicGeometry.normalizationBaseChangeComparison_isIso_of_isSeparableExtension`

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points along open immersions -/

/-- An open immersion carries generic points of irreducible components to generic points of
irreducible components. -/
theorem mem_genericPoints_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] {x : A} (hx : x ∈ genericPoints A) : f x ∈ genericPoints B :=
  mem_genericPoints_of_generalizingMap f.isOpenEmbedding.generalizingMap hx

/-- A morphism carries generic points of irreducible components to generic points of irreducible
components as soon as its precomposition with a surjective morphism does. -/
private theorem mapsTo_genericPoints_of_surjective_comp {A B C : Scheme.{u}} (f : A ⟶ B)
    (g : B ⟶ C) [Surjective f]
    (h : Set.MapsTo (f ≫ g) (genericPoints A) (genericPoints C)) :
    Set.MapsTo g (genericPoints B) (genericPoints C) := by
  intro b hb
  obtain ⟨a, ha⟩ := f.surjective b
  let Z : irreducibleComponents A :=
    ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
  have hηa : (genericPoints.ofComponent Z : A) ⤳ a :=
    (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent
  have heq : f (genericPoints.ofComponent Z : A) = b :=
    (mem_genericPoints_iff_forall_specializes_eq b).1 hb _
      (by simpa only [ha] using hηa.map f.continuous)
  simpa only [Scheme.Hom.comp_apply, heq] using h (genericPoints.ofComponent Z).2

/-- An isomorphism of schemes restricts to a bijection on generic points of irreducible
components. -/
private theorem bijOn_genericPoints_of_iso {A B : Scheme.{u}} (e : A ≅ B) :
    Set.BijOn e.hom (genericPoints A) (genericPoints B) :=
  ⟨fun _ hx ↦ mem_genericPoints_of_isOpenImmersion e.hom hx,
    fun _ _ _ _ hxy ↦ e.hom.homeomorph.injective hxy,
    fun y hy ↦ ⟨e.inv y, mem_genericPoints_of_isOpenImmersion e.inv hy, by simp⟩⟩

/-- An isomorphism of schemes reflects generic points of irreducible components. -/
private theorem preimage_genericPoints_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] :
    f ⁻¹' genericPoints B = genericPoints A :=
  Set.ext fun x ↦ ⟨fun hx ↦ by
    have := mem_genericPoints_of_isOpenImmersion (inv f) hx
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at this
    exact this,
    fun hx ↦ mem_genericPoints_of_isOpenImmersion f hx⟩

/-! ### Elementary stability properties of birationality -/

/-- Birationality is stable under composition. -/
private theorem isBirational_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsBirational f) (hg : IsBirational g) : IsBirational (f ≫ g) := by
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨fun x hx ↦ hg.bijOn.mapsTo (hf.bijOn.mapsTo hx),
    fun x hx y hy h ↦ hf.bijOn.injOn hx hy
      (hg.bijOn.injOn (hf.bijOn.mapsTo hx) (hf.bijOn.mapsTo hy) h), fun z hz ↦ ?_⟩ fun x hx ↦ ?_
  · obtain ⟨y, hy, hyz⟩ := hg.bijOn.surjOn hz
    obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn hy
    exact ⟨x, hx, (congrArg g hxy).trans hyz⟩
  · have := hf.isIso_stalkMap x hx
    have := hg.isIso_stalkMap (f x) (hf.bijOn.mapsTo hx)
    rw [Scheme.Hom.stalkMap_comp]
    exact (asIso (g.stalkMap (f x)) ≪≫ asIso (f.stalkMap x)).isIso_hom

/-- An isomorphism of schemes is birational. -/
private theorem isBirational_of_iso {A B : Scheme.{u}} (e : A ≅ B) : IsBirational e.hom :=
  isBirational_of_bijOn_of_isIso_stalkMap _ (bijOn_genericPoints_of_iso e)
    fun x _ ↦ ((isIso_iff_isIso_stalkMap e.hom).mp inferInstance).2 x

/-- The first factor of a birational composite is birational, provided the second factor is
birational and reflects generic points. -/
private theorem isBirational_of_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsBirational (f ≫ g)) (hg : IsBirational g)
    (hpre : g ⁻¹' genericPoints C = genericPoints B) : IsBirational f := by
  have hmap : Set.MapsTo f (genericPoints A) (genericPoints B) := fun x hx ↦
    (Set.ext_iff.mp hpre (f x)).mp (hfg.bijOn.mapsTo hx)
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨hmap, fun x hx y hy hxy ↦
    hfg.bijOn.injOn hx hy (by simpa only [Scheme.Hom.comp_apply] using congrArg g hxy),
    fun y hy ↦ ?_⟩ fun x hx ↦ ?_
  · obtain ⟨x, hx, hxy⟩ := hfg.bijOn.surjOn (hg.bijOn.mapsTo hy)
    exact ⟨x, hx, hg.bijOn.injOn (hmap hx) hy (by simpa only [Scheme.Hom.comp_apply] using hxy)⟩
  · have : IsIso (g.stalkMap (f x)) := hg.isIso_stalkMap (f x) (hmap hx)
    have : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      exact hfg.isIso_stalkMap x hx
    exact IsIso.of_isIso_comp_left (g.stalkMap (f x)) (f.stalkMap x)

/-- The restriction `f ∣_ U` of a morphism agrees with `f` on points, via the open immersions. -/
private theorem morphismRestrict_apply_ι {A B : Scheme.{u}} (f : A ⟶ B) (U : B.Opens)
    (z : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) z) = f ((f ⁻¹ᵁ U).ι z) :=
  congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ B ↦ g z) (morphismRestrict_ι f U)

/-- Birationality is inherited by the restriction over an open of the target. -/
theorem isBirational_morphismRestrict {A B : Scheme.{u}} (f : A ⟶ B)
    (hf : IsBirational f) (U : B.Opens) : IsBirational (f ∣_ U) := by
  have hmap := morphismRestrict_apply_ι f U
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨fun z hz ↦ ?_, fun z hz z' hz' h ↦ ?_,
    fun y hy ↦ ?_⟩ fun z hz ↦ ?_
  · refine mem_genericPoints_of_isOpenImmersion_apply U.ι ?_
    rw [hmap z]
    exact hf.bijOn.mapsTo (mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz)
  · refine (f ⁻¹ᵁ U).ι.isOpenEmbedding.injective (hf.bijOn.injOn
      (mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz)
      (mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz') ?_)
    simpa only [← hmap z, ← hmap z'] using congrArg U.ι h
  · obtain ⟨z, hz, hzy⟩ := hf.bijOn.surjOn (mem_genericPoints_of_isOpenImmersion U.ι hy)
    have hzU : z ∈ f ⁻¹ᵁ U := by
      change f z ∈ U
      rw [show f z = U.ι y from hzy]
      exact y.2
    refine ⟨⟨z, hzU⟩, mem_genericPoints_of_isOpenImmersion_apply (f ⁻¹ᵁ U).ι hz,
      U.ι.isOpenEmbedding.injective ?_⟩
    rw [hmap ⟨z, hzU⟩]
    exact hzy
  · exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictStalkMap f U z)).mpr
      (hf.isIso_stalkMap _ (mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz))

/-- The preimage of a dense open under a birational morphism is dense. -/
private theorem dense_preimage_of_isBirational {A B : Scheme.{u}} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : IsBirational f) (U : B.Opens) (hU : Dense (U : Set B)) :
    Dense (f ⁻¹' (U : Set B)) := by
  refine (dense_iff_closure_eq.mpr (genericPoints.closure (α := A))).mono fun a ha ↦ ?_
  exact scheme_genericPoints_mem_dense_open B U.isOpen hU (hf.bijOn.mapsTo ha)

/-- A morphism that is an isomorphism over a dense open whose preimage is dense is birational. -/
private theorem isBirational_of_dense_open_isIso {A B : Scheme.{u}}
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] (f : A ⟶ B)
    (U : B.Opens) (hU : Dense (U : Set B)) (hpre : Dense (f ⁻¹' (U : Set B)))
    [IsIso (f ∣_ U)] : IsBirational f := by
  have hval (z : A) (hz : z ∈ f ⁻¹ᵁ U) : ((f ∣_ U) ⟨z, hz⟩).1 = f z :=
    morphismRestrict_apply_ι f U ⟨z, hz⟩
  have hV {x : A} (hx : x ∈ genericPoints A) : x ∈ f ⁻¹ᵁ U :=
    scheme_genericPoints_mem_dense_open A (f ⁻¹ᵁ U).isOpen hpre hx
  have hgen {x : A} (hx : x ∈ genericPoints A) : f x ∈ genericPoints B := by
    have hxV := hV hx
    have H := mem_genericPoints_of_isOpenImmersion U.ι
      ((bijOn_genericPoints_of_iso (asIso (f ∣_ U))).mapsTo
        (mem_genericPoints_of_isOpenImmersion_apply (f ⁻¹ᵁ U).ι (x := ⟨x, hxV⟩) hx))
    change ((f ∣_ U) ⟨x, hxV⟩).1 ∈ genericPoints B at H
    rw [← hval x hxV]
    exact H
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨fun _ hx ↦ hgen hx, fun x hx y hy hxy ↦ ?_,
    fun y hy ↦ ?_⟩ fun x hx ↦ ?_
  · have he : (f ∣_ U) ⟨x, hV hx⟩ = (f ∣_ U) ⟨y, hV hy⟩ :=
      Subtype.ext ((hval x _).trans (hxy.trans (hval y _).symm))
    exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective he)
  · have hyU := scheme_genericPoints_mem_dense_open B U.isOpen hU hy
    obtain ⟨x, hx, he⟩ := (bijOn_genericPoints_of_iso (asIso (f ∣_ U))).surjOn
      (mem_genericPoints_of_isOpenImmersion_apply U.ι (x := (⟨y, hyU⟩ : U.toScheme)) hy)
    exact ⟨x.1, mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι hx,
      (hval x.1 x.2).symm.trans (congrArg Subtype.val he)⟩
  · exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictStalkMap f U ⟨x, hV hx⟩)).mp
        (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp inferInstance).2 _)

/-- A morphism that is an isomorphism over a dense open whose preimage is dense reflects generic
points. -/
private theorem preimage_genericPoints_eq_of_dense_open_isIso {A B : Scheme.{u}}
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] (f : A ⟶ B)
    (U : B.Opens) (hU : Dense (U : Set B)) (hpre : Dense (f ⁻¹' (U : Set B)))
    [IsIso (f ∣_ U)] : f ⁻¹' genericPoints B = genericPoints A := by
  refine Set.ext fun x ↦ ⟨fun hx ↦ ?_,
    fun hx ↦ (isBirational_of_dense_open_isIso f U hU hpre).bijOn.mapsTo hx⟩
  have hxU : f x ∈ U := scheme_genericPoints_mem_dense_open B U.isOpen hU hx
  have hval := morphismRestrict_apply_ι f U ⟨x, hxU⟩
  have hyU : (f ∣_ U) ⟨x, hxU⟩ ∈ genericPoints U.toScheme :=
    mem_genericPoints_of_isOpenImmersion_apply U.ι (hval ▸ hx)
  exact mem_genericPoints_of_isOpenImmersion (f ⁻¹ᵁ U).ι
    ((preimage_genericPoints_of_isIso (f ∣_ U)).subset hyU)

/-! ### The maximal open over which a morphism is an isomorphism -/

/-- The largest open of the target over which a morphism restricts to an isomorphism. -/
private noncomputable def maximalIsomorphismOpen {A B : Scheme.{u}} (f : A ⟶ B) : B.Opens :=
  ⨆ W : {W : B.Opens // IsIso (f ∣_ W)}, W.1

private theorem le_maximalIsomorphismOpen {A B : Scheme.{u}} (f : A ⟶ B)
    (W : B.Opens) (hW : IsIso (f ∣_ W)) : W ≤ maximalIsomorphismOpen f :=
  le_iSup_of_le ⟨W, hW⟩ le_rfl

private theorem isIso_morphismRestrict_maximalIsomorphismOpen {A B : Scheme.{u}} (f : A ⟶ B) :
    IsIso (f ∣_ maximalIsomorphismOpen f) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) fun x ↦ ?_
  have hmem : x.1 ∈ (⨆ W : {W : B.Opens // IsIso (f ∣_ W)}, W.1) := x.2
  rw [Opens.mem_iSup] at hmem
  obtain ⟨i, hxi⟩ := hmem
  have hiU : i.1 ≤ maximalIsomorphismOpen f := le_iSup_of_le i le_rfl
  refine ⟨(opensRestrict (maximalIsomorphismOpen f)).symm ⟨i.1, hiU⟩, hxi, ?_⟩
  have himage : (maximalIsomorphismOpen f).ι ''ᵁ
      ((opensRestrict (maximalIsomorphismOpen f)).symm ⟨i.1, hiU⟩) = i.1 := by
    refine Opens.ext (Set.ext fun y ↦ ⟨?_, fun hy ↦ ⟨⟨y, hiU hy⟩, hy, rfl⟩⟩)
    rintro ⟨z, hz, rfl⟩
    exact hz
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f (maximalIsomorphismOpen f) _), himage]
  exact i.2

/-- A finite birational morphism onto a reduced locally Noetherian scheme is an isomorphism over
a dense open.  This is the global form of Tag 0BAJ, obtained from
`AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isIntegralHom` on affine charts. -/
private theorem dense_maximalIsomorphismOpen_of_isFinite {A B : Scheme.{u}}
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsReduced B] (f : A ⟶ B) [IsFinite f]
    (hf : IsBirational f) : Dense (maximalIsomorphismOpen f : Set B) := by
  refine (dense_iff_closure_eq.mpr (genericPoints.closure (α := B))).mono fun b hb ↦ ?_
  obtain ⟨_, ⟨U : B.Opens, hU, rfl⟩, hbU, -⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ b) isOpen_univ
  have hfin {S : Scheme.{u}} [IsLocallyNoetherian S] {V : S.Opens} (hV : IsCompact (V : Set S)) :
      IsNoetherian V.toScheme ∧ Finite (irreducibleComponents V.toScheme) := by
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V := { toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion V.ι }
    exact ⟨inferInstance, finite_irreducibleComponents_of_isNoetherian⟩
  obtain ⟨_, _⟩ := hfin hU.isCompact
  obtain ⟨_, _⟩ := hfin (f.isCompact_preimage hU.isCompact)
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  obtain ⟨V, hV, hIso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isIntegralHom (f ∣_ U)
      (isBirational_morphismRestrict f hf U) (Or.inl ⟨inferInstance, inferInstance⟩)
  refine le_maximalIsomorphismOpen f (U.ι ''ᵁ V)
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U V)).mp hIso) ⟨⟨b, hbU⟩, ?_, rfl⟩
  exact genericPoints_mem_dense_open V.isOpen hV
    (mem_genericPoints_of_isOpenImmersion_apply U.ι (x := (⟨b, hbU⟩ : U.toScheme)) hb)

/-! ### Functoriality of the reduction -/

/-- The closed immersion of the reduction is a homeomorphism. -/
private theorem isHomeomorph_subschemeι_nilradical (A : Scheme.{u}) :
    IsHomeomorph A.nilradical.subschemeι := by
  have hsurj : Function.Surjective A.nilradical.subschemeι := fun x ↦
    Set.mem_range.mp (by rw [A.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  exact (A.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    hsurj).isHomeomorph

/-- The morphism of reductions induced by a morphism of schemes. -/
private noncomputable def reductionMap {A B : Scheme.{u}} (f : A ⟶ B) :
    A.nilradical.subscheme ⟶ B.nilradical.subscheme :=
  let := isReduced_nilradical_subscheme A
  Classical.choose
    (Scheme.existsUnique_lift_nilradical_subschemeι (A.nilradical.subschemeι ≫ f))

private theorem reductionMap_subschemeι {A B : Scheme.{u}} (f : A ⟶ B) :
    reductionMap f ≫ B.nilradical.subschemeι = A.nilradical.subschemeι ≫ f :=
  let := isReduced_nilradical_subscheme A
  (Classical.choose_spec
    (Scheme.existsUnique_lift_nilradical_subschemeι (A.nilradical.subschemeι ≫ f))).1

private theorem reductionMap_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    reductionMap (f ≫ g) = reductionMap f ≫ reductionMap g := by
  apply (cancel_mono C.nilradical.subschemeι).mp
  simp only [Category.assoc, reductionMap_subschemeι]
  exact congrArg (fun h : A.nilradical.subscheme ⟶ B ↦ h ≫ g)
    (reductionMap_subschemeι f).symm

private theorem isIso_reductionMap {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] :
    IsIso (reductionMap f) := by
  refine ⟨⟨reductionMap (inv f), ?_, ?_⟩⟩
  · apply (cancel_mono A.nilradical.subschemeι).mp
    rw [Category.assoc, reductionMap_subschemeι, ← Category.assoc, reductionMap_subschemeι,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono B.nilradical.subschemeι).mp
    rw [Category.assoc, reductionMap_subschemeι, ← Category.assoc, reductionMap_subschemeι,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The reduction of a surjective closed immersion is an isomorphism. -/
private theorem isIso_reductionMap_of_surjective_isClosedImmersion {A B : Scheme.{u}}
    (f : A ⟶ B) [IsClosedImmersion f] [Surjective f] : IsIso (reductionMap f) := by
  have hsup : f.ker.support = ⊤ := by
    apply Closeds.ext
    rw [Scheme.Hom.support_ker]
    simp [Set.range_eq_univ.mpr f.surjective]
  have hker : f.ker ≤ B.nilradical := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
        (I := f.ker) (Z := ⊤)).mp (by simp [hsup])
  let s : B.nilradical.subscheme ⟶ A :=
    IsClosedImmersion.lift f B.nilradical.subschemeι (by
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using hker)
  have hs : s ≫ f = B.nilradical.subschemeι :=
    IsClosedImmersion.lift_fac f B.nilradical.subschemeι _
  let := isReduced_nilradical_subscheme B
  obtain ⟨t, ht, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι s
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply (cancel_mono A.nilradical.subschemeι).mp
    apply (cancel_mono f).mp
    calc
      ((reductionMap f ≫ t) ≫ A.nilradical.subschemeι) ≫ f = reductionMap f ≫ s ≫ f := by
        simp only [Category.assoc, ht]
      _ = reductionMap f ≫ B.nilradical.subschemeι := by rw [hs]
      _ = A.nilradical.subschemeι ≫ f := reductionMap_subschemeι f
      _ = ((𝟙 _) ≫ A.nilradical.subschemeι) ≫ f := by simp
  · apply (cancel_mono B.nilradical.subschemeι).mp
    calc
      (t ≫ reductionMap f) ≫ B.nilradical.subschemeι = (t ≫ A.nilradical.subschemeι) ≫ f := by
        rw [Category.assoc, reductionMap_subschemeι, ← Category.assoc]
      _ = s ≫ f := by rw [ht]
      _ = B.nilradical.subschemeι := hs
      _ = (𝟙 _) ≫ B.nilradical.subschemeι := by simp

private theorem subschemeι_eqToHom {A : Scheme.{u}} {I J : A.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The reduction of an open immersion is an open immersion, with the expected range. -/
private theorem exists_reductionMap_isOpenImmersion {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] :
    ∃ jr : U.nilradical.subscheme ⟶ A.nilradical.subscheme,
      IsOpenImmersion jr ∧
        jr ≫ A.nilradical.subschemeι = U.nilradical.subschemeι ≫ j := by
  let I := A.nilradical.comap j
  let q := (A.nilradical.comapIso j).hom ≫ pullback.snd j A.nilradical.subschemeι
  have : IsOpenImmersion q := inferInstance
  have : IsReduced A.nilradical.subscheme := isReduced_nilradical_subscheme A
  have : IsReduced I.subscheme := isReduced_of_isOpenImmersion q
  have heq : I = U.nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top]
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I ⊤ ?_
    simp only [I, Scheme.IdealSheafData.support_comap, Scheme.support_nilradical]
    ext x
    rfl
  refine ⟨(eqToIso (congrArg Scheme.IdealSheafData.subscheme heq.symm)).hom ≫ q,
    inferInstance, ?_⟩
  have hq : q ≫ A.nilradical.subschemeι = I.subschemeι ≫ j := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  rw [Category.assoc, hq, ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ j) (subschemeι_eqToHom heq.symm)

private theorem isOpenImmersion_reductionMap {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] : IsOpenImmersion (reductionMap j) := by
  obtain ⟨jr, hjr, heq⟩ := exists_reductionMap_isOpenImmersion j
  have h : jr = reductionMap j := by
    apply (cancel_mono A.nilradical.subschemeι).mp
    rw [heq, reductionMap_subschemeι]
  exact h ▸ hjr

private theorem range_reductionMap_of_isOpenImmersion {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] :
    Set.range (reductionMap j) = A.nilradical.subschemeι ⁻¹' Set.range j := by
  have hrU : IsHomeomorph U.nilradical.subschemeι := isHomeomorph_subschemeι_nilradical U
  have hrA : IsHomeomorph A.nilradical.subschemeι := isHomeomorph_subschemeι_nilradical A
  refine Set.ext fun a ↦ ⟨?_, ?_⟩
  · rintro ⟨v, rfl⟩
    exact ⟨U.nilradical.subschemeι v, by
      simp only [← Scheme.Hom.comp_apply, reductionMap_subschemeι]⟩
  · rintro ⟨v, hv⟩
    obtain ⟨v', rfl⟩ := hrU.surjective v
    refine ⟨v', hrA.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, reductionMap_subschemeι] using hv

/-- A morphism that is an isomorphism over a dense open whose preimage is dense has the same
property after passing to the reductions. -/
private theorem exists_dense_open_isIso_reductionMap {A B : Scheme.{u}}
    (f : A ⟶ B) (U : B.Opens) (hU : Dense (U : Set B))
    (hpre : Dense (f ⁻¹' (U : Set B))) [IsIso (f ∣_ U)] :
    ∃ W : B.nilradical.subscheme.Opens,
      Dense (W : Set B.nilradical.subscheme) ∧
      Dense ((reductionMap f) ⁻¹' (W : Set B.nilradical.subscheme)) ∧
      IsIso (reductionMap f ∣_ W) := by
  have hiU : IsOpenImmersion (reductionMap U.ι) := isOpenImmersion_reductionMap U.ι
  have hiV : IsOpenImmersion (reductionMap (f ⁻¹ᵁ U).ι) :=
    isOpenImmersion_reductionMap (f ⁻¹ᵁ U).ι
  set W := (reductionMap U.ι).opensRange with hWdef
  set W' := (reductionMap (f ⁻¹ᵁ U).ι).opensRange with hW'def
  have hW : (W : Set B.nilradical.subscheme) = B.nilradical.subschemeι ⁻¹' (U : Set B) := by
    simpa only [hWdef, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
      using range_reductionMap_of_isOpenImmersion U.ι
  have hW' : (W' : Set A.nilradical.subscheme) =
      A.nilradical.subschemeι ⁻¹' ((f ⁻¹ᵁ U : A.Opens) : Set A) := by
    simpa only [hW'def, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
      using range_reductionMap_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have hpreW : (reductionMap f) ⁻¹ᵁ W = W' := by
    refine Opens.ext (Set.ext fun a ↦ ?_)
    change reductionMap f a ∈ W ↔ a ∈ W'
    rw [show (reductionMap f a ∈ W) ↔ B.nilradical.subschemeι (reductionMap f a) ∈ U from
        Set.ext_iff.mp hW _,
      show (a ∈ W') ↔ A.nilradical.subschemeι a ∈ (f ⁻¹ᵁ U : A.Opens) from Set.ext_iff.mp hW' _,
      ← Scheme.Hom.comp_apply, reductionMap_subschemeι]
    rfl
  have hsq : IsPullback (reductionMap (f ∣_ U)) (reductionMap (f ⁻¹ᵁ U).ι)
      (reductionMap U.ι) (reductionMap f) := by
    refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · rw [← reductionMap_comp, ← reductionMap_comp, morphismRestrict_ι]
    · simpa only [hWdef, hW'def] using hpreW
  have : IsIso (reductionMap (f ∣_ U)) := isIso_reductionMap _
  have hPb : IsIso (pullback.snd (reductionMap f) (reductionMap U.ι)) := by
    rw [← hsq.flip.isoPullback_inv_snd]
    infer_instance
  have hRes : IsIso (reductionMap f ∣_ W) := by
    simpa only [hWdef] using (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictOpensRange (reductionMap f) (reductionMap U.ι))).mpr hPb
  have hrA : IsHomeomorph A.nilradical.subschemeι := isHomeomorph_subschemeι_nilradical A
  have hrB : IsHomeomorph B.nilradical.subschemeι := isHomeomorph_subschemeι_nilradical B
  refine ⟨W, by rw [hW]; exact hU.preimage hrB.isOpenMap, ?_, hRes⟩
  have hW'dense : Dense (W' : Set A.nilradical.subscheme) := by
    rw [hW']
    exact hpre.preimage hrA.isOpenMap
  simpa only [← Scheme.Hom.coe_preimage, hpreW] using hW'dense

/-- Being an isomorphism over a dense open with dense preimage is inherited by a base change
along open maps. -/
private theorem exists_dense_open_isIso_of_isPullback {A B A' B' : Scheme.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') (p : B' ⟶ B) (q : A' ⟶ A)
    (H : IsPullback f' q p f) (hp : IsOpenMap p) (hq : IsOpenMap q)
    (U : B.Opens) (hU : Dense (U : Set B)) (hpre : Dense (f ⁻¹' (U : Set B)))
    [IsIso (f ∣_ U)] :
    ∃ W : B'.Opens, Dense (W : Set B') ∧ Dense (f' ⁻¹' (W : Set B')) ∧ IsIso (f' ∣_ W) := by
  have he : f' ⁻¹ᵁ (p ⁻¹ᵁ U) = q ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  have HR := Scheme.Hom.isPullback_resLE H (US := U) (UT := f ⁻¹ᵁ U) (UX := p ⁻¹ᵁ U)
    le_rfl le_rfl (UY := f' ⁻¹ᵁ (p ⁻¹ᵁ U)) (by rw [he, inf_idem])
  have hi : IsIso (f' ∣_ (p ⁻¹ᵁ U)) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (MorphismProperty.of_isPullback (P := .isomorphisms Scheme) HR.flip
        (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
          (inferInstance : IsIso (f ∣_ U))))
  refine ⟨p ⁻¹ᵁ U, hU.preimage hp, ?_, hi⟩
  change Dense ((f' ⁻¹ᵁ (p ⁻¹ᵁ U) : A'.Opens) : Set A')
  rw [he]
  exact hpre.preimage hq

/-! ### The normalization over an affine chart of the reduction -/

/-- The normalization of `X` is the normalization of the reduction of `X`, compatibly with the
canonical factor of the normalization morphism through the reduction. -/
private theorem exists_iso_normalizationScheme_normalizationToReduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ e : X.normalizationScheme hX ≅
        X.nilradical.subscheme.normalizationScheme (X.finite_irreducibleComponents_reduction hX),
      e.hom ≫ X.nilradical.subscheme.normalization
          (X.finite_irreducibleComponents_reduction hX) =
        X.normalizationToReduction hX := by
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  refine ⟨e, (cancel_mono X.nilradical.subschemeι).mp ?_⟩
  rw [Category.assoc, he, X.normalizationToReduction_subschemeι hX]

/-- The canonical morphism from the normalization of `X` to the reduction of `X` is birational. -/
private theorem isBirational_normalizationToReduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsBirational (X.normalizationToReduction hX) := by
  obtain ⟨e, he⟩ := exists_iso_normalizationScheme_normalizationToReduction X hX
  have : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  rw [← he]
  exact isBirational_comp e.hom _ (isBirational_of_iso e)
    (X.nilradical.subscheme.isBirational_normalization
      (X.finite_irreducibleComponents_reduction hX))

/-- Over an affine open, the closed immersion of a closed subscheme is the spectrum map of the
quotient by its ideal. -/
private theorem subschemeAffineIso_comp {X : Scheme.{u}} (idealData : X.IdealSheafData)
    (affineOpen : X.affineOpens)
    (affinePreimage : IsAffineOpen (idealData.subschemeι ⁻¹ᵁ affineOpen.1)) :
    (Scheme.Spec.mapIso (idealData.subschemeObjIso affineOpen).op ≪≫
      (affinePreimage.isoSpec).symm).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (idealData.ideal affineOpen))) =
      (idealData.subschemeι ∣_ affineOpen.1) ≫ affineOpen.2.isoSpec.hom := by
  change affinePreimage.isoSpec.hom ≫ Spec.map (idealData.subschemeObjIso affineOpen).inv ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (idealData.ideal affineOpen))) = _
  rw [← Spec.map_comp, ← idealData.subschemeι_app affineOpen, IsAffineOpen.isoSpec_hom]
  exact Scheme.Opens.toSpecΓ_naturality idealData.subschemeι affineOpen.1

/-- Over an affine chart `Spec A ≅ U` of `X`, the normalization of `X` is the spectrum of the
integral closure of `A ⧸ nilradical A` in its total ring of fractions, compatibly with the
normalization morphism. -/
private theorem exists_affine_normalization_chart_reduction {X : Scheme.{u}} {A : Type u}
    [CommRing A] (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) :
    let Q := A ⧸ nilradical A
    let C := integralClosure Q (FractionRing Q)
    ∃ E : (X.normalization hX ⁻¹ᵁ U).toScheme ≅ Spec (.of C),
      E.hom ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap Q C).comp (Ideal.Quotient.mk (nilradical A)))) =
        (X.normalization hX ∣_ U) ≫ e.inv := by
  classical
  let I := X.nilradical
  let Xr := I.subscheme
  let hred := X.finite_irreducibleComponents_reduction hX
  let Uaff : X.affineOpens := ⟨U, .of_isIso e.inv⟩
  let V : Xr.Opens := I.subschemeι ⁻¹ᵁ U
  let Vaff : Xr.affineOpens := ⟨V, Uaff.2.preimage I.subschemeι⟩
  let B := Γ(X, U)
  let Q := A ⧸ nilradical A
  let C := integralClosure Q (FractionRing Q)
  let eA : A ≃+* B := affineOpenCoordinateRingEquiv U e
  have hrad : Ideal.map (eA : A →+* B) (nilradical A) = nilradical B := by
    change Ideal.map (eA : A →+* B) (Ideal.radical ⊥) = Ideal.radical ⊥
    rw [Ideal.map_radical_of_surjective (f := (eA : A →+* B)) (I := ⊥) eA.surjective (by simp),
      Ideal.map_bot]
  have hideal : I.ideal Uaff = nilradical B := rfl
  let eQ : Q ≃+* (B ⧸ I.ideal Uaff) :=
    Ideal.quotientEquiv (nilradical A) (I.ideal Uaff) eA (by simpa [hideal] using hrad.symm)
  let eSub := I.subschemeObjIso Uaff
  let eV : Spec (.of Q) ≅ V.toScheme :=
    Scheme.Spec.mapIso (eQ.toCommRingCatIso.symm.op) ≪≫
      Scheme.Spec.mapIso eSub.op ≪≫ Vaff.2.isoSpec.symm
  have heV : eV.inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical A))) =
      (I.subschemeι ∣_ U) ≫ e.inv := by
    have hQmap : CommRingCat.ofHom (Ideal.Quotient.mk (nilradical A)) ≫ eQ.toCommRingCatIso.hom =
        CommRingCat.ofHom eA.toRingHom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal Uaff)) := by
      ext a
      change eQ (Ideal.Quotient.mk (nilradical A) a) = Ideal.Quotient.mk (I.ideal Uaff) (eA a)
      exact Ideal.quotientEquiv_mk (nilradical A) (I.ideal Uaff) eA _ a
    change Vaff.2.isoSpec.hom ≫ Spec.map eSub.inv ≫ Spec.map eQ.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical A))) = _
    rw [← Spec.map_comp, hQmap, Spec.map_comp]
    have hSub := subschemeAffineIso_comp I Uaff Vaff.2
    change Vaff.2.isoSpec.hom ≫ Spec.map eSub.inv ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal Uaff))) = _ at hSub
    have hAmap := affineOpenCoordinateRingEquiv_specMap U Uaff.2 e
    change Spec.map (CommRingCat.ofHom eA.toRingHom) = _ at hAmap
    calc
      _ = ((I.subschemeι ∣_ U) ≫ Uaff.2.isoSpec.hom) ≫
          Spec.map (CommRingCat.ofHom eA.toRingHom) := by
            simpa only [Category.assoc] using
              congrArg (fun m ↦ m ≫ Spec.map (CommRingCat.ofHom eA.toRingHom)) hSub
      _ = _ := by
        rw [Category.assoc, hAmap]
        simp
  have : IsReduced Xr := isReduced_nilradical_subscheme X
  let eRed := preimageNormalizationIsoSpecIntegralClosure hred V eV
  obtain ⟨eNorm, heNorm⟩ := exists_iso_normalizationScheme_normalizationToReduction X hX
  let W := Xr.normalization hred ⁻¹ᵁ V
  have hpre : eNorm.hom ⁻¹ᵁ W = X.normalization hX ⁻¹ᵁ U := by
    change eNorm.hom ⁻¹ᵁ (Xr.normalization hred ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U)) = _
    rw [← Scheme.Hom.comp_preimage, heNorm, ← Scheme.Hom.comp_preimage,
      X.normalizationToReduction_subschemeι hX]
  let eSource : (X.normalization hX ⁻¹ᵁ U).toScheme ≅ W.toScheme :=
    Scheme.isoOfEq _ hpre.symm ≪≫ eNorm.hom.preimageIso W
  have heSourceι : eSource.hom ≫ W.ι = (X.normalization hX ⁻¹ᵁ U).ι ≫ eNorm.hom := by
    simp only [eSource, Iso.trans_hom, Category.assoc, Scheme.Hom.preimageIso_hom_ι]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  have heSource : eSource.hom ≫ (Xr.normalization hred ∣_ V) ≫ (I.subschemeι ∣_ U) =
      (X.normalization hX ∣_ U) := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, morphismRestrict_ι]
    change eSource.hom ≫ (Xr.normalization hred ∣_ V) ≫ V.ι ≫ I.subschemeι = _
    rw [morphismRestrict_ι_assoc]
    change eSource.hom ≫ W.ι ≫ Xr.normalization hred ≫ I.subschemeι = _
    rw [← Category.assoc eSource.hom, heSourceι]
    simp only [Category.assoc]
    rw [← Category.assoc eNorm.hom, heNorm]
    exact congrArg (fun m ↦ (X.normalization hX ⁻¹ᵁ U).ι ≫ m)
      (X.normalizationToReduction_subschemeι hX)
  refine ⟨eSource ≪≫ eRed, ?_⟩
  change eSource.hom ≫ eRed.hom ≫
      Spec.map (CommRingCat.ofHom ((algebraMap Q C).comp (Ideal.Quotient.mk (nilradical A)))) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc eRed.hom,
    preimageNormalizationIsoSpecIntegralClosure_hom_comp, Category.assoc, heV, ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ e.inv) heSource

/-! ### The normalization of a base change of a normal scheme -/

/-- Being a universal homeomorphism transports along an isomorphism of arrows. -/
private theorem universalHomeomorphism_of_arrowIso {V W V' W' : Scheme.{u}} (f : V ⟶ W)
    (g : V' ⟶ W') (e : Arrow.mk f ≅ Arrow.mk g) (hg : UniversalHomeomorphism g) :
    UniversalHomeomorphism f :=
  (MorphismProperty.arrow_mk_iso_iff (P := @UniversalHomeomorphism) e).mpr hg

/-- Over an affine chart of the form `Spec (R ⊗[k] K)` with `R` normal, the normalization
morphism restricts to a universal homeomorphism. -/
private theorem universalHomeomorphism_morphismRestrict_normalization_of_tensor_chart
    {Z : Scheme.{u}} (hZ : ∀ V : Z.Opens, IsCompact (V : Set Z) → (irreducibleComponents V).Finite)
    {k K R : Type u} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    (hR : IsNormalRing R) (U : Z.Opens)
    (e : Spec (.of (TensorProduct k R K)) ≅ U.toScheme) :
    UniversalHomeomorphism (Z.normalization hZ ∣_ U) := by
  obtain ⟨E, hE⟩ := exists_affine_normalization_chart_reduction hZ U e
  refine universalHomeomorphism_of_arrowIso _ _ (Arrow.isoMk E e.symm ?_)
    (universalHomeomorphism_normalization_tensorProduct_of_normal (K := K) hR)
  change E.hom ≫ Spec.map (CommRingCat.ofHom _) = (Z.normalization hZ ∣_ U) ≫ e.inv
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using hE

/-- If `Z` is covered by affine opens of the form `Spec (R ⊗[k] K)` with each `R` normal, then
the normalization morphism of `Z` is a universal homeomorphism. -/
private theorem universalHomeomorphism_normalization_of_tensor_cover {Z : Scheme.{u}}
    (hZ : ∀ V : Z.Opens, IsCompact (V : Set Z) → (irreducibleComponents V).Finite)
    {k K : Type u} [Field k] [Field K] [Algebra k K] {ι : Type*} (U : ι → Z.Opens)
    (hcover : (⨆ i, U i) = ⊤) (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (hR : ∀ i, IsNormalRing (R i))
    (e : ∀ i, Spec (.of (TensorProduct k (R i) K)) ≅ (U i).toScheme) :
    UniversalHomeomorphism (Z.normalization hZ) := by
  refine universalHomeomorphism_of_openCover _ (Z.openCoverOfIsOpenCover U hcover) fun i ↦ ?_
  let : CommRing (R i) := (inferInstance : ∀ j, CommRing (R j)) i
  let : Algebra k (R i) := (inferInstance : ∀ j, Algebra k (R j)) i
  refine universalHomeomorphism_of_arrowIso _ _
    (morphismRestrictEq (Z.normalization hZ) (Scheme.Opens.opensRange_ι (U i)).symm ≪≫
      morphismRestrictOpensRange (Z.normalization hZ)
        ((Z.openCoverOfIsOpenCover U hcover).f i)).symm
    (universalHomeomorphism_morphismRestrict_normalization_of_tensor_chart hZ (hR i) (U i) (e i))

/-- The ring of sections of an affine open of a normal scheme is a normal ring. -/
private theorem isNormalRing_of_isNormal_affineOpen {Z : Scheme.{u}} [IsNormal Z] (U : Z.Opens)
    (hU : IsAffineOpen U) : IsNormalRing Γ(Z, U) := by
  have h : IsNormal Z ↔ ∀ J : Z.affineOpens, IsNormalRing Γ(Z, J) := (isNormal_tfae Z).out 1 2
  exact h.mp inferInstance ⟨U, hU⟩

/-- **The geometric core of Tag 0C3N.** For a normal scheme `N` locally of finite type over `k`,
the normalization morphism of the base change `N_K` is a universal homeomorphism: affine-locally
`N_K` is `Spec (Γ(N, U) ⊗[k] K)` with `Γ(N, U)` normal. -/
private theorem universalHomeomorphism_normalization_baseChange_of_isNormal
    {k K : Type u} [Field k] [Field K] [Algebra k K] {N : Scheme.{u}} (p : N ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [IsNormal N] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj (Over.mk p)
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    UniversalHomeomorphism
      (Y.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom)) := by
  classical
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (Over.pullback σ).obj (Over.mk p)
  have : LocallyOfFiniteType Y.hom := by
    dsimp [Y, σ]
    infer_instance
  let π : Y.left ⟶ N := pullback.fst p σ
  have hAff (y : Y.left) : ∃ U : N.Opens, IsAffineOpen U ∧ π y ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
    exact ⟨U, hU, hxU⟩
  let U (y : Y.left) : N.Opens := (hAff y).choose
  have hU (y : Y.left) : IsAffineOpen (U y) := (hAff y).choose_spec.1
  have hy (y : Y.left) : π y ∈ U y := (hAff y).choose_spec.2
  let V (y : Y.left) : Y.left.Opens := π ⁻¹ᵁ U y
  have hcover : (⨆ y : Y.left, V y) = ⊤ :=
    top_unique fun y _ ↦ Opens.mem_iSup.2 ⟨y, hy y⟩
  let R (y : Y.left) : Type u := Γ(N, U y)
  let : ∀ y : Y.left, CommRing (R y) := fun _ ↦ inferInstance
  let : ∀ y : Y.left, Algebra k (R y) := fun y ↦
    (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫
      p.appLE ⊤ (U y) (by simp)).hom.toAlgebra
  have hR (y : Y.left) : IsNormalRing (R y) :=
    isNormalRing_of_isNormal_affineOpen (U y) (hU y)
  refine universalHomeomorphism_normalization_of_tensor_cover (k := k) (K := K) _ V hcover R hR
    fun y ↦ ?_
  exact (Classical.choose (Classical.choose_spec
    (affineBaseChangeLocalModel k K N p y (U y) (hU y) (hy y)))).symm

/-! ### Descending from the normalization to the comparison morphism -/

/-- The closed immersion of the reduction is a universal homeomorphism. -/
private theorem universalHomeomorphism_subschemeι_nilradical (Z : Scheme.{u}) :
    UniversalHomeomorphism Z.nilradical.subschemeι := by
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  exact ⟨inferInstance, inferInstance, ⟨(isHomeomorph_subschemeι_nilradical Z).surjective⟩⟩

/-- An integral morphism from a normal scheme which is birational over every quasi-compact open
of the target is a universal homeomorphism as soon as the normalization morphism of the target
is one: the morphism *is* the normalization morphism, up to an isomorphism of arrows. -/
private theorem universalHomeomorphism_of_isIntegralHom_of_locally_isBirational
    {V W : Scheme.{u}} (f : V ⟶ W) [IsIntegralHom f] [IsNormal V]
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (hcomponents : ∀ U : W.Opens, IsCompact (U : Set W) →
      (irreducibleComponents (f ⁻¹ᵁ U)).Finite)
    (hbirational : ∀ U : W.Opens, IsCompact (U : Set W) → IsBirational (f ∣_ U))
    (hν : UniversalHomeomorphism (W.normalization hW)) : UniversalHomeomorphism f := by
  obtain ⟨hV, g, e, hg, he⟩ :=
    exists_normalizationFactorization_of_integral_of_birational hW f hcomponents hbirational
  have : IsIso (V.normalization hV) := V.isIso_normalization_of_isNormal hV
  have : IsIso g := by
    rw [← he]
    infer_instance
  refine universalHomeomorphism_of_arrowIso f _ (Arrow.isoMk (asIso g).symm (Iso.refl W) ?_) hν
  change inv g ≫ W.normalization hW = f ≫ 𝟙 W
  rw [← hg]
  simp only [Category.comp_id, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- If the normalization morphism of `Z` is a universal homeomorphism, so is the normalization
morphism of the reduction of `Z`. -/
private theorem universalHomeomorphism_normalization_nilradical_subscheme (Z : Scheme.{u})
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (hν : UniversalHomeomorphism (Z.normalization hZ)) :
    UniversalHomeomorphism
      (Z.nilradical.subscheme.normalization (Z.finite_irreducibleComponents_reduction hZ)) := by
  have hnr : UniversalHomeomorphism (Z.normalizationToReduction hZ) := by
    refine universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty.of_postcomp
      (Z.normalizationToReduction hZ) Z.nilradical.subschemeι
      (universalHomeomorphism_subschemeι_nilradical Z) ?_
    rw [Z.normalizationToReduction_subschemeι hZ]
    exact hν
  obtain ⟨e, he⟩ := exists_iso_normalizationScheme_normalizationToReduction Z hZ
  refine universalHomeomorphism_of_arrowIso _ _ (Arrow.isoMk e.symm (Iso.refl _) ?_) hnr
  change e.inv ≫ Z.normalizationToReduction hZ =
    Z.nilradical.subscheme.normalization (Z.finite_irreducibleComponents_reduction hZ) ≫ 𝟙 _
  rw [← he]
  simp only [Category.comp_id, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

section OverField

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The normalization of a scheme locally of finite type over a field is again locally of finite
type over that field, because the normalization morphism is finite. -/
private theorem locallyOfFiniteType_normalization_over_field (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType
      (X.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType k X.hom) ≫
        X.hom) := by
  have : IsFinite
      (X.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType k X.hom)) :=
    isFinite_normalizationOverField k X.hom
  infer_instance

/-- The normalization morphism of the base change of the normalization of `X` is a universal
homeomorphism: that base change is a base change of the *normal* scheme
`X.normalizationScheme`. -/
private theorem universalHomeomorphism_normalization_baseChangeOfNormalization
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    letI : LocallyOfFiniteType (X.left.normalization hX ≫ X.hom) :=
      locallyOfFiniteType_normalization_over_field X
    let Z := (Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))
    letI : LocallyOfFiniteType Z.hom := by
      dsimp [Z, σ]
      infer_instance
    UniversalHomeomorphism
      (Z.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType K Z.hom)) := by
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  have : IsNormal (X.left.normalizationScheme hX) := X.left.isNormal_normalizationScheme hX
  have : LocallyOfFiniteType (X.left.normalization hX ≫ X.hom) :=
    locallyOfFiniteType_normalization_over_field X
  exact universalHomeomorphism_normalization_baseChange_of_isNormal (K := K)
    (X.left.normalization hX ≫ X.hom)

/-- The comparison morphism factors, integrally, through the reduction of its target: its source,
the normalization of `X_K`, is reduced. -/
private theorem exists_isIntegralHom_comparison_to_reduction (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj X
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
    let Z := ((Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))).left
    ∃ d : Y.left.normalizationScheme hY ⟶ Z.nilradical.subscheme,
      d ≫ Z.nilradical.subschemeι = normalizationBaseChangeComparison X ∧ IsIntegralHom d := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (Over.pullback σ).obj X
  have : LocallyOfFiniteType Y.hom := by
    dsimp [Y, σ]
    infer_instance
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
  let Z := ((Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))).left
  have : IsReduced (Y.left.normalizationScheme hY) :=
    Scheme.isReduced_normalizationScheme Y.left hY
  have : IsIntegralHom (normalizationBaseChangeComparison (k := k) (K := K) X) :=
    isIntegralHom_normalizationBaseChangeComparison X
  obtain ⟨d, hd, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι
    (X := Z) (normalizationBaseChangeComparison (k := k) (K := K) X)
  refine ⟨d, hd, ?_⟩
  have : IsIntegralHom (d ≫ Z.nilradical.subschemeι) := hd ▸ inferInstance
  exact IsIntegralHom.of_comp d Z.nilradical.subschemeι

/-- The base change of the closed immersion of the reduction becomes an isomorphism after
reducing: it is a surjective closed immersion. -/
private theorem isIso_reductionMap_baseChange_subschemeι (X : Over (Spec (.of k))) :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let r := X.left.nilradical.subschemeι
    let f : Over.mk (r ≫ X.hom) ⟶ X := Over.homMk r
    IsIso (reductionMap ((Over.pullback σ).map f).left) := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let r := X.left.nilradical.subschemeι
  let f : Over.mk (r ≫ X.hom) ⟶ X := Over.homMk r
  have : Surjective r := ⟨(isHomeomorph_subschemeι_nilradical X.left).surjective⟩
  have : IsClosedImmersion f.left := by
    change IsClosedImmersion r
    infer_instance
  have : Surjective f.left := by
    change Surjective r
    infer_instance
  have : IsClosedImmersion ((Over.pullback σ).map f).left :=
    MorphismProperty.of_isPullback (overPullback_isPullback σ _ _ f) inferInstance
  have : Surjective ((Over.pullback σ).map f).left :=
    MorphismProperty.of_isPullback (overPullback_isPullback σ _ _ f) inferInstance
  exact isIso_reductionMap_of_surjective_isClosedImmersion _

/-- The reduction of the base change of the normalization morphism is birational and reflects
generic points.

This is where Tag 0BAJ enters: the normalization morphism of `X` is finite and birational over
the reduction of `X`, hence an isomorphism over a dense open, and that property survives the base
change to `K` and the passage to the reductions. -/
private theorem isBirational_reductionMap_baseChangeNormalization (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] :
    let q := baseChangeNormalization (k := k) (K := K) X
    IsBirational (reductionMap q) ∧
      (reductionMap q) ⁻¹' genericPoints _ = genericPoints _ := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  let r := X.left.nilradical.subschemeι
  let nr := X.left.normalizationToReduction hX
  let ν := X.left.normalization hX
  let XR : Over (Spec (.of k)) := Over.mk (r ≫ X.hom)
  let N : Over (Spec (.of k)) := Over.mk (ν ≫ X.hom)
  let f : N ⟶ XR := Over.homMk nr (by
    change nr ≫ (r ≫ X.hom) = ν ≫ X.hom
    rw [← Category.assoc, X.left.normalizationToReduction_subschemeι hX])
  let g : XR ⟶ X := Over.homMk r
  let qf := ((Over.pullback σ).map f).left
  let qg := ((Over.pullback σ).map g).left
  have hν : f ≫ g = Over.homMk ν :=
    Over.OverMorphism.ext (X.left.normalizationToReduction_subschemeι hX)
  have hq : baseChangeNormalization (K := K) X = qf ≫ qg := by
    change ((Over.pullback σ).map (Over.homMk ν)).left = qf ≫ qg
    rw [← hν]
    exact congrArg Over.Hom.left ((Over.pullback σ).map_comp f g)
  have : IsReduced X.left.nilradical.subscheme := isReduced_nilradical_subscheme X.left
  have : LocallyOfFiniteType XR.hom := by
    change LocallyOfFiniteType (r ≫ X.hom)
    infer_instance
  have : LocallyOfFiniteType N.hom := locallyOfFiniteType_normalization_over_field X
  have : IsLocallyNoetherian X.left.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian XR.hom
  have : IsLocallyNoetherian (X.left.normalizationScheme hX) :=
    LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : IsFinite nr := by
    have : IsFinite ν := isFinite_normalizationOverField k X.hom
    have : IsFinite (nr ≫ r) := by
      rw [X.left.normalizationToReduction_subschemeι hX]
      infer_instance
    exact IsFinite.of_comp nr r
  have hnr : IsBirational nr := isBirational_normalizationToReduction X.left hX
  let W : XR.left.Opens := maximalIsomorphismOpen nr
  have hW : Dense (W : Set XR.left) := dense_maximalIsomorphismOpen_of_isFinite nr hnr
  have : IsIso (nr ∣_ W) := isIso_morphismRestrict_maximalIsomorphismOpen nr
  have hpreW : Dense (nr ⁻¹' (W : Set XR.left)) := dense_preimage_of_isBirational nr hnr W hW
  obtain ⟨W', hW', hpreW', hIsoqf⟩ :=
    exists_dense_open_isIso_of_isPullback nr qf (pullback.fst XR.hom σ) (pullback.fst N.hom σ)
      (overPullback_isPullback σ _ _ f).flip (pullback.fst XR.hom σ).isOpenMap
      (pullback.fst N.hom σ).isOpenMap W hW hpreW
  have : IsIso (qf ∣_ W') := hIsoqf
  obtain ⟨W'', hW'', hpreW'', hIsoredqf⟩ :=
    exists_dense_open_isIso_reductionMap qf W' hW' hpreW'
  have : LocallyOfFiniteType ((Over.pullback σ).obj XR).hom := by
    change LocallyOfFiniteType (pullback.snd XR.hom σ)
    infer_instance
  have : LocallyOfFiniteType ((Over.pullback σ).obj N).hom := by
    change LocallyOfFiniteType (pullback.snd N.hom σ)
    infer_instance
  have : IsLocallyNoetherian ((Over.pullback σ).obj XR).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback σ).obj XR).hom
  have : IsLocallyNoetherian ((Over.pullback σ).obj N).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback σ).obj N).hom
  have : IsLocallyNoetherian ((Over.pullback σ).obj XR).left.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((Over.pullback σ).obj XR).left.nilradical.subschemeι
  have : IsLocallyNoetherian ((Over.pullback σ).obj N).left.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((Over.pullback σ).obj N).left.nilradical.subschemeι
  have : IsIso (reductionMap qf ∣_ W'') := hIsoredqf
  have hqfr : IsBirational (reductionMap qf) :=
    isBirational_of_dense_open_isIso (reductionMap qf) W'' hW'' hpreW''
  have hpreqf : (reductionMap qf) ⁻¹' genericPoints _ = genericPoints _ :=
    preimage_genericPoints_eq_of_dense_open_isIso (reductionMap qf) W'' hW'' hpreW''
  have : IsIso (reductionMap qg) := isIso_reductionMap_baseChange_subschemeι (K := K) X
  have hqgr : IsBirational (reductionMap qg) := isBirational_of_iso (asIso (reductionMap qg))
  have hpreqg : (reductionMap qg) ⁻¹' genericPoints _ = genericPoints _ :=
    preimage_genericPoints_of_isIso (reductionMap qg)
  change IsBirational (reductionMap (baseChangeNormalization (K := K) X)) ∧
    (reductionMap (baseChangeNormalization (K := K) X)) ⁻¹' genericPoints _ = genericPoints _
  rw [hq, reductionMap_comp]
  refine ⟨isBirational_comp _ _ hqfr hqgr, Set.ext fun x ↦ ?_⟩
  exact (Set.ext_iff.mp hpreqg (reductionMap qf x)).trans (Set.ext_iff.mp hpreqf x)

/-! ### The two remaining assertions of Tag 0C3N -/

/-- **Stacks Project, Tag 0C3N.** The normalization comparison for an arbitrary extension of
fields is a universal homeomorphism.

The comparison lands in the reduction of its target (its source is reduced), and the resulting
morphism `d` is integral and birational onto a scheme whose normalization morphism is a universal
homeomorphism — because that scheme is the reduction of a base change of the *normal* scheme
`X.normalizationScheme`. -/
@[stacks 0C3N "universal homeomorphism"]
theorem normalizationBaseChangeComparison_isUniversalHomeomorphism
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    UniversalHomeomorphism (normalizationBaseChangeComparison (k := k) (K := K) X) := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (Over.pullback σ).obj X
  have : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (pullback.snd X.hom σ)
    infer_instance
  let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  have : LocallyOfFiniteType (X.left.normalization hX ≫ X.hom) :=
    locallyOfFiniteType_normalization_over_field X
  let Z := (Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))
  have : LocallyOfFiniteType Z.hom := by
    dsimp [Z, σ]
    infer_instance
  let hZ := finite_irreducibleComponents_of_locallyOfFiniteType K Z.hom
  let hZr := Z.left.finite_irreducibleComponents_reduction hZ
  have : LocallyOfFiniteType (Y.left.normalization hY ≫ Y.hom) :=
    locallyOfFiniteType_normalization_over_field Y
  let hN := finite_irreducibleComponents_of_locallyOfFiniteType K
    (Y.left.normalization hY ≫ Y.hom)
  obtain ⟨d, hd, hint⟩ := exists_isIntegralHom_comparison_to_reduction (k := k) (K := K) X
  obtain ⟨hq, hpreq⟩ := isBirational_reductionMap_baseChangeNormalization (k := k) (K := K) X
  have : IsIntegralHom d := hint
  have hcomp : d ≫ reductionMap (baseChangeNormalization (K := K) X) =
      Y.left.normalizationToReduction hY := by
    apply (cancel_mono Y.left.nilradical.subschemeι).mp
    calc
      (d ≫ reductionMap (baseChangeNormalization (K := K) X)) ≫ Y.left.nilradical.subschemeι =
          d ≫ (Z.left.nilradical.subschemeι ≫ baseChangeNormalization (K := K) X) := by
            rw [Category.assoc, reductionMap_subschemeι]
      _ = normalizationBaseChangeComparison X ≫ baseChangeNormalization (K := K) X := by
            rw [← Category.assoc, hd]
      _ = Y.left.normalization hY :=
            normalizationBaseChangeComparison_comp_baseChangeNormalization X
      _ = Y.left.normalizationToReduction hY ≫ Y.left.nilradical.subschemeι :=
            (Y.left.normalizationToReduction_subschemeι hY).symm
  have hbir : IsBirational d := by
    refine isBirational_of_comp d (reductionMap (baseChangeNormalization (K := K) X)) ?_ hq hpreq
    rw [hcomp]
    exact isBirational_normalizationToReduction Y.left hY
  have hνZ : UniversalHomeomorphism (Z.left.normalization hZ) :=
    universalHomeomorphism_normalization_baseChangeOfNormalization (K := K) X
  have hνZr : UniversalHomeomorphism (Z.left.nilradical.subscheme.normalization hZr) :=
    universalHomeomorphism_normalization_nilradical_subscheme Z.left hZ hνZ
  have : IsNormal (Y.left.normalizationScheme hY) := Y.left.isNormal_normalizationScheme hY
  have hdUH : UniversalHomeomorphism d :=
    universalHomeomorphism_of_isIntegralHom_of_locally_isBirational d hZr
      (fun U hU ↦ hN (d ⁻¹ᵁ U) (d.isCompact_preimage hU))
      (fun U _ ↦ isBirational_morphismRestrict d hbir U) hνZr
  have hcUH : UniversalHomeomorphism (d ≫ Z.left.nilradical.subschemeι) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition.comp_mem
      d Z.left.nilradical.subschemeι hdUH (universalHomeomorphism_subschemeι_nilradical Z.left)
  exact hd ▸ hcUH

/-- **Stacks Project, Tag 0C3N.** For a separable extension of fields, the normalization
comparison is an isomorphism.

The target of the comparison is normal, by Tag 0C3M, so the universal property of the
normalization of `X_K` produces a two-sided inverse. -/
@[stacks 0C3N "separable extension"]
theorem normalizationBaseChangeComparison_isIso_of_isSeparableExtension
    [Algebra.IsSeparableExtension k K] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    IsIso (normalizationBaseChangeComparison (k := k) (K := K) X) := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (Over.pullback σ).obj X
  have : LocallyOfFiniteType Y.hom := by
    dsimp [Y, σ]
    infer_instance
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
  let Z := ((Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))).left
  let c : Y.left.normalizationScheme hY ⟶ Z := normalizationBaseChangeComparison X
  let q : Z ⟶ Y.left := baseChangeNormalization X
  have hcq : c ≫ q = Y.left.normalization hY :=
    normalizationBaseChangeComparison_comp_baseChangeNormalization X
  have hc : UniversalHomeomorphism c :=
    normalizationBaseChangeComparison_isUniversalHomeomorphism X
  have : Surjective c :=
    ⟨(hc.universally_isHomeomorph _ _ _ IsPullback.of_id_snd).surjective⟩
  have hq : Set.MapsTo q (genericPoints Z) (genericPoints Y.left) :=
    mapsTo_genericPoints_of_surjective_comp c q (by
      rw [hcq]
      exact fun _ hz ↦ Y.left.normalization_mem_genericPoints hY hz)
  have : IsNormal Z := by
    have : IsNormal (X.left.normalizationScheme hX) := X.left.isNormal_normalizationScheme hX
    exact isNormal_pullback_of_isSeparableExtension k K (X.left.normalization hX ≫ X.hom)
  have : IsNormal (Y.left.normalizationScheme hY) := Y.left.isNormal_normalizationScheme hY
  obtain ⟨s, hs, -⟩ := Scheme.existsUnique_lift_normalization hY q fun η ↦ hq η.2
  have hcs : c ≫ s = 𝟙 _ := by
    obtain ⟨t, ht, hu⟩ := Scheme.existsUnique_lift_normalization hY
      (Y.left.normalization hY) fun η ↦ Y.left.normalization_mem_genericPoints hY η.2
    exact (hu _ (by
      dsimp only
      rw [Category.assoc, hs, hcq])).trans
      (hu _ (Category.id_comp _)).symm
  have hsc : s ≫ c = 𝟙 Z := by
    refine pullback.hom_ext ?_ ?_
    · let p : Z ⟶ X.left.normalizationScheme hX :=
        pullback.fst (X.left.normalization hX ≫ X.hom) σ
      let π : Y.left ⟶ X.left := pullback.fst X.hom σ
      have := flat_pullback_fst_specMap_algebraMap (K := K) X
      have hqp : q ≫ π = p ≫ X.left.normalization hX := by
        dsimp [q, baseChangeNormalization, Over.pullback, π, p, σ, hX]
        simp only [Over.homMk_left, pullback.lift_fst]
      obtain ⟨t, ht, hu⟩ := Scheme.existsUnique_lift_normalization hX (q ≫ π)
        fun η ↦ (pullback.fst X.hom σ).mem_genericPoints_of_flat (hq η.2)
      change (s ≫ c) ≫ p = (𝟙 Z) ≫ p
      rw [Category.id_comp]
      refine (hu _ ?_).trans (hu _ hqp.symm).symm
      calc
        ((s ≫ c) ≫ p) ≫ X.left.normalization hX = s ≫ ((c ≫ q) ≫ π) := by
          simp only [Category.assoc, hqp]
        _ = q ≫ π := by rw [hcq, ← Category.assoc, hs]
    · rw [Category.id_comp, Category.assoc]
      change s ≫ (normalizationBaseChangeComparison X ≫
        pullback.snd (X.left.normalization hX ≫ X.hom) σ) = _
      rw [normalizationBaseChangeComparison_comp_snd, ← Category.assoc, hs]
      dsimp [q, baseChangeNormalization, Over.pullback, σ, hX]
      simp only [Over.homMk_left, pullback.lift_snd]
  exact ⟨⟨s, hcs, hsc⟩⟩

end OverField

end AlgebraicGeometry

end
