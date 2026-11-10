module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineSectionsSurjectiveLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeOfCartesianLargeSections
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.IsoLocusOfLeftExactNatTrans
public import StacksFrontier.Homology.PseudoCoherent.Local

/-!
# Cartesian locally quasi-coherent modules form a weak Serre class at module universe `u + 1`

Let `𝒵` be a category fibred in groupoids over `(Sch/S)_{fppf}` whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` (the underlying category of an algebraic
stack). This file proves that the étale sheaves of `𝒪_𝒵`-modules at module universe `u + 1` which
are locally quasi-coherent (Stacks 06WJ) and cartesian on flat arrows between objects over affine
schemes (`AlgebraicGeometry.Stack.IsCartesianOnFlatAffineArrows`) form a weak Serre subcategory.

The argument works with sections over objects lying over affine schemes. For such an object `x`
the functor `F ↦ F(x)` is left exact, and it carries a short exact sequence whose first term is
locally quasi-coherent to a sequence whose last map is surjective: restricted to the small étale
site of the scheme below `x` the first term is quasi-coherent, and the first étale cohomology of
a quasi-coherent module vanishes on affine schemes
(`AlgebraicGeometry.SmallEtale.surjective_val_app_of_shortExact_freeModuleUniverse`). For an
arrow `φ : x ⟶ y` over a flat morphism of affine schemes, `F ↦ 𝒪(x) ⊗_{𝒪(y)} F(y)` is then left
exact with the same property, the ring map `𝒪(y) ⟶ 𝒪(x)` being flat; the base change maps form a
natural transformation between these functors, and the locus where they are all invertible is a
weak Serre class by `CategoryTheory.ObjectProperty.isWeakSerreClass_isoLocus_of_epi`.

## Main results

* `Stack.surjective_val_app_of_shortExact_succ`: sections over an object over an affine scheme
  of a short exact sequence with locally quasi-coherent kernel.
* `Stack.isWeakSerreClass_isLocallyQuasicoherent_isCartesianOnFlatAffineArrows_succ`: the weak
  Serre property.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The arrows of `𝒳` lying over flat morphisms between affine schemes. -/
abbrev FlatAffineArrowIndex {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) :=
  {a : Σ (x y : 𝒳), x ⟶ y // Flat (B.inclusion.map (p.map a.2.2).left) ∧
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj a.1)) ∧
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj a.2.1))}

/-- The ring map `𝒪(y) ⟶ 𝒪(x)` of the structure sheaf along an arrow `φ : x ⟶ y` lying over a
flat morphism of affine schemes is flat. -/
theorem flat_structureSheaf_map_of_flat {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : Flat (B.inclusion.map (p.map φ).left))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y))) :
    ((structureSheaf B S hS p hp τ hτ).obj.map φ.op).hom.Flat := by
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (p.map φ)).op).hom.Flat
  rw [Scheme.Γ_map_op]
  have : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) := hφ
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)
    (f := (BigFppfOver.toScheme B S hS).map (p.map φ))).1 inferInstance

section Succ

variable {𝒵 : Type (u + 1)} [Category.{u} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS)
  (hr : r.IsFiberedInGroupoids)

/-- **Sections over an object over an affine scheme of a short exact sequence with locally
quasi-coherent kernel**, at module universe `u + 1`: for a short exact sequence
`0 ⟶ 𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃ ⟶ 0` of étale sheaves of modules on `𝒵` with `𝓕₁` locally quasi-coherent and
an object `x` lying over an affine scheme, `𝓕₂(x) ⟶ 𝓕₃(x)` is surjective. -/
theorem surjective_val_app_of_shortExact_succ
    (Tc : ShortComplex (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS r hr
      (etaleTopology B) (etaleTopology_le_topology B))))
    (hTc : letI := abelian_etaleModuleSheavesSucc B S hS r hr; Tc.ShortExact)
    (h₁ : IsLocallyQuasicoherent B E h S hS r hr Tc.X₁.val) (x : 𝒵)
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (r.obj x))) :
    Function.Surjective (Tc.g.val.app (op x)) := by
  let := abelian_etaleModuleSheavesSucc B S hS r hr
  let : HasSheafify (SmallEtale.topology E (r.obj x).left.1 (contains_base B E h S hS r x))
      AddCommGrpCat.{u + 1} :=
    hasSheafify_smallEtale_freeModuleUniverse.{u, u} E _ _
  let : Abelian (SheafOfModules.{u + 1} (SmallEtale.structureSheaf E (r.obj x).left.1
      (contains_base B E h S hS r x))) :=
    SheafOfModules.instAbelian.{u + 1, u, u, u + 1} _
  let := hasSheafify_associatedTopology_of_category_succ B S hS r
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS r
  let rx := restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS r hr x
  have := preservesZeroMorphisms_restrictSheafToSmallEtale.{u, u + 1, u, u + 1}
    B E h S hS r hr x
  have := preservesFiniteLimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr x
  have := preservesFiniteColimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr x
  have hW : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleTop B E h S hS r x)) := hx
  have hs := SmallEtale.surjective_val_app_of_shortExact_freeModuleUniverse.{u, u} B E h
    (r.obj x).left.1 (contains_base B E h S hS r x) (Tc.map rx) (hTc.map_of_exact rx)
    ((isLocallyQuasicoherent_iff B E h S hS r hr Tc.X₁).1 h₁ x) (etaleTop B E h S hS r x) hW
  have hf : Etale (B.inclusion.map (r.map (𝟙 x)).left) := by
    rw [r.map_id, Over.id_left, CategoryTheory.Functor.map_id]
    infer_instance
  obtain ⟨-, e₂, -⟩ := exists_arrowIso_etaleIndex B E h S hS r hr (𝟙 x) hf
  exact SmallEtale.surjective_app_of_iso Tc.g.val e₂.symm hs

/-- **Cartesian locally quasi-coherent modules form a weak Serre class at module universe
`u + 1`.** The étale sheaves of modules on `𝒵` which are locally quasi-coherent (Stacks 06WJ) and
cartesian on flat arrows between objects over affine schemes form a weak Serre subcategory of the
étale sheaves of modules at module universe `u + 1`. -/
theorem isWeakSerreClass_isLocallyQuasicoherent_isCartesianOnFlatAffineArrows_succ :
    letI := abelian_etaleModuleSheavesSucc B S hS r hr
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS r hr (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => IsLocallyQuasicoherent B E h S hS r hr F.val ∧
        IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS r hr (etaleTopology B)
          (etaleTopology_le_topology B) F.val) := by
  let := abelian_etaleModuleSheavesSucc B S hS r hr
  let Q := isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS r hr
  have : Q.IsWeakSerreClass := isWeakSerreClass_isLocallyQuasicoherent_succ B E h S hS r hr
  let O := (structureSheaf B S hS r hr (etaleTopology B) (etaleTopology_le_topology B)).obj
  let 𝒪 := ringStructureSheafCore B S hS r hr (etaleTopology B) (etaleTopology_le_topology B)
  let fo : SheafOfModules.{u + 1} 𝒪 ⥤ PresheafOfModules.{u + 1} (O ⋙ forget₂ CommRingCat RingCat) :=
    SheafOfModules.forget 𝒪
  let ev : ∀ X : 𝒵ᵒᵖ, PresheafOfModules.{u + 1} (O ⋙ forget₂ CommRingCat RingCat) ⥤
      ModuleCat.{u + 1} ((O ⋙ forget₂ CommRingCat RingCat).obj X) := fun X =>
    PresheafOfModules.evaluation _ X
  let ex : ∀ i : FlatAffineArrowIndex B S hS r,
      ModuleCat.{u + 1} ((O ⋙ forget₂ CommRingCat RingCat).obj (op i.1.2.1)) ⥤
        ModuleCat.{u + 1} ((O ⋙ forget₂ CommRingCat RingCat).obj (op i.1.1)) := fun i =>
    ModuleCat.extendScalars.{u, u, u + 1} (O.map i.1.2.2.op).hom
  let T : ∀ i : FlatAffineArrowIndex B S hS r, SheafOfModules.{u + 1} 𝒪 ⥤
      ModuleCat.{u + 1} ((O ⋙ forget₂ CommRingCat RingCat).obj (op i.1.1)) := fun i =>
    fo ⋙ ev (op i.1.2.1) ⋙ ex i
  let R : ∀ i : FlatAffineArrowIndex B S hS r, SheafOfModules.{u + 1} 𝒪 ⥤
      ModuleCat.{u + 1} ((O ⋙ forget₂ CommRingCat RingCat).obj (op i.1.1)) := fun i =>
    fo ⋙ ev (op i.1.1)
  let c : ∀ i, T i ⟶ R i := fun i =>
    Functor.whiskerLeft fo (restrictionBaseChangeNatTrans.{u + 1, u, u, u + 1} O i.1.2.2.op)
  have hfo : PreservesFiniteLimits fo :=
    PreservesLimitsOfSize.preservesFiniteLimits.{u + 1, u + 1} (SheafOfModules.forget 𝒪)
  have hev : ∀ X, PreservesFiniteLimits (ev X) := fun X =>
    PresheafOfModules.evaluation_preservesFiniteLimits _ X
  have hex : ∀ i, PreservesFiniteLimits (ex i) := fun i =>
    StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat _
      (flat_structureSheaf_map_of_flat B S hS r hr (etaleTopology B)
        (etaleTopology_le_topology B) i.1.2.2 i.2.1 i.2.2.1 i.2.2.2)
  have : fo.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : ∀ X, (ev X).PreservesZeroMorphisms := fun X => ⟨fun _ _ => rfl⟩
  have : ∀ i, (ex i).IsLeftAdjoint := fun i =>
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (O.map i.1.2.2.op).hom).isLeftAdjoint
  have : ∀ i, (ex i).PreservesZeroMorphisms := fun i =>
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : ∀ i, PreservesFiniteLimits (T i) := fun i =>
    comp_preservesFiniteLimits fo (ev (op i.1.2.1) ⋙ ex i)
  have : ∀ i, (T i).PreservesZeroMorphisms := fun i => by dsimp only [T]; infer_instance
  have : ∀ i, PreservesFiniteLimits (R i) := fun i => comp_preservesFiniteLimits fo _
  have : ∀ i, (R i).PreservesZeroMorphisms := fun i => by dsimp only [R]; infer_instance
  have hR : ∀ i (Sc : ShortComplex _), Sc.ShortExact → Q Sc.X₁ → Epi ((R i).map Sc.g) :=
    fun i Sc hSc h₁ => (ModuleCat.epi_iff_surjective _).2
      (surjective_val_app_of_shortExact_succ B E h S hS r hr Sc hSc h₁ i.1.1 i.2.2.1)
  have hT : ∀ i (Sc : ShortComplex _), Sc.ShortExact → Q Sc.X₁ → Epi ((T i).map Sc.g) := by
    intro i Sc hSc h₁
    have : Epi ((fo ⋙ ev (op i.1.2.1)).map Sc.g) := (ModuleCat.epi_iff_surjective _).2
      (surjective_val_app_of_shortExact_succ B E h S hS r hr Sc hSc h₁ i.1.2.1 i.2.2.2)
    exact Functor.map_epi (ex i) ((fo ⋙ ev (op i.1.2.1)).map Sc.g)
  have hmain := ObjectProperty.isWeakSerreClass_isoLocus_of_epi Q T R c hT hR
  convert hmain using 1
  funext F
  apply propext
  refine and_congr Iff.rfl ⟨fun hF i => ?_, fun hF x y φ hφ hx hy => ?_⟩
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hF i.1.2.2 i.2.1 i.2.2.1 i.2.2.2)
  · exact (ConcreteCategory.isIso_iff_bijective _).1 (hF ⟨⟨x, y, φ⟩, hφ, hx, hy⟩)

end Succ

end AlgebraicGeometry.Stack

end
