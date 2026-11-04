module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.NoetherianInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.NormalApproximation
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.NotEquidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SectionCycle

/-!
# Noetherian induction through normalizations

Let `S` be a Noetherian Nagata scheme and `G` a sheaf of `Λ`-modules on `S_étale`. To show that
`G` is constructible it suffices to show, for every integral normal scheme `T` of finite type
over `S`, that the inverse image of `G` to `T` is constructible on a nonempty open of `T`.

This is the device by which the proofs of Stacks 0GKY and 0GKZ pass to a normal base over a
Nagata scheme: by Noetherian induction
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isClosedImmersion`) one needs, for
every nonempty reduced closed `Z ⊆ S`, a nonempty open of `Z` on which `G` is constructible. Take
an irreducible open `V ⊆ Z`, so `V` is integral, and its normalization `ν : V' ⟶ V`, which is
finite (Stacks 035S, `V` being Nagata) and surjective. If `G|_{V'}` is constructible on a nonempty
open `W ⊆ V'`, then `ν(V' \ W)` is a closed subset of `V` missing the generic point of `V` (the
fibres of `ν` are discrete and `W` contains the generic point of `V'`), and over its complement
`O` the morphism `ν⁻¹(O) ⟶ O` is surjective with `ν⁻¹(O) ⊆ W`, so `G|_O` is constructible by
Stacks 095Q.

## Main results

* `exists_isOpen_isIrreducible_of_mem_genericPoints`: a generic point of a Noetherian space has
  an irreducible open neighbourhood.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isIntegral_isNormal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

universe u

/-- **A generic point of a Noetherian space has an irreducible open neighbourhood**: the
complement of the union of the other irreducible components, of which there are finitely many. -/
theorem exists_isOpen_isIrreducible_of_mem_genericPoints {Z : Type*} [TopologicalSpace Z]
    [NoetherianSpace Z] {η : Z} (hη : η ∈ genericPoints Z) :
    ∃ V : Set Z, IsOpen V ∧ η ∈ V ∧ IsIrreducible V := by
  set C := closure ({η} : Set Z)
  have hC : C ∈ irreducibleComponents Z := hη
  let O := (⋃₀ (irreducibleComponents Z \ {C}))ᶜ
  have hO : IsOpen O := (Set.Finite.isClosed_sUnion
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).diff
    fun t ht => isClosed_of_mem_irreducibleComponents t ht.1).isOpen_compl
  have hηO : η ∈ O := by
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hle : C ⊆ C' := closure_minimal (Set.singleton_subset_iff.2 hηC')
      (isClosed_of_mem_irreducibleComponents C' hC')
    exact hne (hC.eq_of_le hC'.1 hle).symm
  have hOC : O ⊆ C := by
    intro x hx
    by_contra hxC
    refine hx ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
      fun h => hxC ?_⟩, mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.mp h]
    exact mem_irreducibleComponent
  exact ⟨O, hO, hηO, ⟨η, hηO⟩, hC.1.isPreirreducible.open_subset hO hOC⟩

namespace AlgebraicGeometry

/-- A nonempty reduced Noetherian scheme has an integral open subscheme. -/
theorem exists_isIntegral_opens_of_isReduced {X : Scheme.{u}} [IsReduced X] [NoetherianSpace X]
    [Nonempty X] : ∃ V : X.Opens, IsIntegral V.toScheme := by
  obtain ⟨z⟩ := ‹Nonempty X›
  obtain ⟨V₀, hV₀, -, hirr⟩ := exists_isOpen_isIrreducible_of_mem_genericPoints
    (genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩ :
      genericPoints X).2
  let V : X.Opens := ⟨V₀, hV₀⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  exact ⟨V, isIntegral_of_irreducibleSpace_of_isReduced _⟩

/-- If `ν : V' ⟶ V` is a finite surjective morphism of integral schemes and `o : W ⟶ V'` is an
open immersion from a nonempty scheme, then the generic point of `V` is not the image of a point
outside the range of `o`. -/
theorem genericPoint_notMem_image_compl_range {V' V W : Scheme.{u}} [IsIntegral V'] [IsIntegral V]
    (ν : V' ⟶ V) [IsFinite ν] [Surjective ν] (o : W ⟶ V') [IsOpenImmersion o] [Nonempty W] :
    genericPoint V ∉ ν.base '' (Set.range o.base)ᶜ := by
  rintro ⟨x, hx, hνx⟩
  have : LocallyOfFiniteType ν := IsProper.toLocallyOfFiniteType
  have : IsIntegralHom ν := inferInstance
  have hξ : ν (genericPoint V') = genericPoint V := by
    have := NormalApproximation.mapsTo_genericPoints_of_isDominant ν
      (by rw [genericPoints_eq_singleton]; rfl : genericPoint V' ∈ genericPoints V')
    rwa [genericPoints_eq_singleton] at this
  obtain rfl : genericPoint V' = x :=
    Stacks.Chow.NotEquidimensional.eq_of_specializes_of_relativeDimensionLE_zero ν
      (Stacks.Chow.relativeDimensionLE_zero_of_locallyQuasiFinite ν) _ x
      (genericPoint_specializes x) (hξ.trans hνx.symm)
  obtain ⟨w₀⟩ := ‹Nonempty W›
  exact hx (((genericPoint_spec V').mem_open_set_iff o.isOpenEmbedding.isOpen_range).2
    ⟨_, Set.mem_univ _, ⟨w₀, rfl⟩⟩)

/-- The restriction of a surjective morphism to the preimage of an open is surjective. -/
theorem surjective_morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (U : Y.Opens) : Function.Surjective (f ∣_ U).base := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := f.surjective y
  exact ⟨⟨x, hy⟩, Subtype.ext (morphismRestrict_base_coe f U ⟨x, hy⟩)⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Descent of generic constructibility along a finite surjective morphism.** Let
`ν : T ⟶ V` be a finite surjective morphism of integral Noetherian schemes of `B` and `f : V ⟶ S`.
If the inverse image of `G` along `ν ≫ f` is constructible on a nonempty open of `T`, then the
inverse image of `G` along `f` is constructible on a nonempty open of `V`. -/
theorem exists_isConstructibleEtaleModule_of_isFinite_of_surjective {S V T W : B.Scheme}
    (G : EtaleModules.{u, 0} Λ S.obj) (f : V ⟶ S) (ν : T ⟶ V) (o : W ⟶ T)
    [IsIntegral V.obj] [IsIntegral T.obj] [IsNoetherian V.obj] [IsNoetherian T.obj]
    [IsFinite (B.inclusion.map ν)] [Surjective (B.inclusion.map ν)]
    [IsOpenImmersion (B.inclusion.map o)] [Nonempty W.obj]
    (hW : IsBigSiteConstructibleEtaleModule B W Λ
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (o ≫ ν ≫ f))).obj G)) :
    ∃ (O : B.Scheme) (j : O ⟶ V), IsOpenImmersion (B.inclusion.map j) ∧ Nonempty O.obj ∧
      IsBigSiteConstructibleEtaleModule B O Λ
        ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (j ≫ f))).obj G) := by
  let ν' : T.obj ⟶ V.obj := B.inclusion.map ν
  let o' : W.obj ⟶ T.obj := B.inclusion.map o
  let f' : V.obj ⟶ S.obj := B.inclusion.map f
  have : IsFinite ν' := ‹IsFinite (B.inclusion.map ν)›
  have : Surjective ν' := ‹Surjective (B.inclusion.map ν)›
  have : IsOpenImmersion o' := ‹IsOpenImmersion (B.inclusion.map o)›
  let O : V.obj.Opens := ⟨(ν'.base '' (Set.range o'.base)ᶜ)ᶜ,
    (ν'.isClosedMap _ o'.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  have hgen : genericPoint V.obj ∈ O := genericPoint_notMem_image_compl_range ν' o'
  have : QuasiCompact O.ι := inferInstance
  let OB : B.Scheme := B.obj O.toScheme
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact O.ι V.property)
  let P : T.obj.Opens := ν' ⁻¹ᵁ O
  let p : P.toScheme ⟶ O.toScheme := ν' ∣_ O
  have hPW : Set.range P.ι.base ⊆ Set.range o'.base := by
    rintro _ ⟨x, rfl⟩
    by_contra hxW
    exact x.2 ⟨_, hxW, rfl⟩
  let k : P.toScheme ⟶ W.obj := IsOpenImmersion.lift o' P.ι hPW
  have : QuasiCompact P.ι := inferInstance
  let PB : B.Scheme := B.obj P.toScheme
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact P.ι T.property)
  let pB : PB ⟶ OB := ObjectProperty.homMk p
  have : CompactSpace OB.obj := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : QuasiSeparatedSpace OB.obj := inferInstanceAs (QuasiSeparatedSpace O.toScheme)
  have : CompactSpace PB.obj := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : QuasiSeparatedSpace PB.obj := inferInstanceAs (QuasiSeparatedSpace P.toScheme)
  refine ⟨OB, ObjectProperty.homMk O.ι, inferInstanceAs (IsOpenImmersion O.ι), ⟨⟨_, hgen⟩⟩,
    isConstructibleEtaleModule_of_inverseImage B Λ pB (surjective_morphismRestrict_base ν' O) ?_⟩
  have heq : k ≫ o' ≫ ν' ≫ f' = p ≫ O.ι ≫ f' := by
    rw [← Category.assoc k, IsOpenImmersion.lift_fac, ← Category.assoc p, morphismRestrict_ι,
      Category.assoc]
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((etaleModuleInverseImageCompIso.{u, 0} Λ k (o' ≫ ν' ≫ f')).symm.app G ≪≫
      eqToIso (by rw [heq]) ≪≫ (etaleModuleInverseImageCompIso.{u, 0} Λ p (O.ι ≫ f')).app G)
    (isConstructibleEtaleModule_inverseImage B Λ (ObjectProperty.homMk k : PB ⟶ W) hW)

/-- **Noetherian induction through normalizations.** Let `S` be a Noetherian Nagata scheme of `B`
and `G` a sheaf of `Λ`-modules on `S_étale`. If for every integral normal scheme `T` of `B` of
finite type over `S` the inverse image of `G` to some nonempty open of `T` is constructible, then
`G` is constructible. -/
theorem isConstructibleEtaleModule_of_forall_isIntegral_isNormal (S : B.Scheme)
    [IsNoetherian S.obj] (hS : IsNagataScheme S.obj) (G : EtaleModules.{u, 0} Λ S.obj)
    (h : ∀ (T : B.Scheme) (w : T ⟶ S), LocallyOfFiniteType (B.inclusion.map w) →
      QuasiCompact (B.inclusion.map w) → IsIntegral T.obj → IsNormal T.obj →
      ∃ (W : B.Scheme) (o : W ⟶ T), IsOpenImmersion (B.inclusion.map o) ∧ Nonempty W.obj ∧
        IsBigSiteConstructibleEtaleModule B W Λ
          ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (o ≫ w))).obj G)) :
    IsBigSiteConstructibleEtaleModule B S Λ G := by
  refine isConstructibleEtaleModule_of_forall_isClosedImmersion B Λ S G
    (fun Z i hi _ hne => ?_)
  let i' : Z.obj ⟶ S.obj := B.inclusion.map i
  have : IsClosedImmersion i' := hi
  have : IsNoetherian Z.obj := isNoetherian_of_isClosedImmersion i'
  obtain ⟨V, _⟩ := exists_isIntegral_opens_of_isReduced (X := Z.obj)
  have : IsNoetherian V.toScheme := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType V.ι
  let VB : B.Scheme := B.obj V.toScheme
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact V.ι Z.property)
  let vB : VB ⟶ Z := ObjectProperty.homMk V.ι
  have hVN : IsNagataScheme V.toScheme := isNagataScheme_of_locallyOfFiniteType (V.ι ≫ i') hS
  let V' := NormalApproximation.integralNormalization V.toScheme
  let ν : V' ⟶ V.toScheme := NormalApproximation.integralNormalizationMap V.toScheme
  have : IsFinite ν := NormalApproximation.isFinite_integralNormalizationMap _ hVN
  have : Surjective ν :=
    Scheme.surjective_normalization _ (finite_irreducibleComponents_of_isIntegral _)
  have : LocallyOfFiniteType ν := IsProper.toLocallyOfFiniteType
  let TB : B.Scheme := B.obj V' (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ν VB.2)
  let νB : TB ⟶ VB := ObjectProperty.homMk ν
  have : IsIntegral V' := inferInstanceAs (IsIntegral (NormalApproximation.integralNormalization _))
  obtain ⟨W, o, ho, hW₀, hW⟩ := h TB (νB ≫ vB ≫ i)
    (inferInstanceAs (LocallyOfFiniteType (ν ≫ V.ι ≫ i')))
    (inferInstanceAs (QuasiCompact (ν ≫ V.ι ≫ i'))) ‹IsIntegral V'›
    (inferInstanceAs (IsNormal (NormalApproximation.integralNormalization _)))
  have : IsNoetherian V' := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType ν
  have : IsIntegral VB.obj := inferInstanceAs (IsIntegral V.toScheme)
  have : IsNoetherian VB.obj := inferInstanceAs (IsNoetherian V.toScheme)
  have : IsIntegral TB.obj := inferInstanceAs (IsIntegral V')
  have : IsNoetherian TB.obj := inferInstanceAs (IsNoetherian V')
  have : IsFinite (B.inclusion.map νB) := inferInstanceAs (IsFinite ν)
  have : Surjective (B.inclusion.map νB) := inferInstanceAs (Surjective ν)
  obtain ⟨O, j, hj, hO, hc⟩ :=
    exists_isConstructibleEtaleModule_of_isFinite_of_surjective B Λ G (vB ≫ i) νB o hW
  have : IsOpenImmersion (B.inclusion.map vB) := inferInstanceAs (IsOpenImmersion V.ι)
  exact ⟨O, j ≫ vB, by rw [Functor.map_comp]; infer_instance, hO, by rwa [Category.assoc]⟩

end Stacks.EtaleCohomology

end
