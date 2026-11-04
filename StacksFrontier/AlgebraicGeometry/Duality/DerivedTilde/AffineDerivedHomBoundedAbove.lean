module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedAboveLocal
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.PullbackIsoInvertible
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSurjective
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# The derived internal Hom into a complex of finite injective dimension on `Spec R`

Let `R` be a Noetherian ring, `E` an object of `D(R)` in `D^{≥ k}` and `ω` an object of `D(R)` of
injective amplitude in `[a, b]`. On `X = Spec R`,

`R𝓗om(Ẽ, ω̃) ∈ D^{≤ b - k}(𝒪_X)`.

Over a standard open `D(g) = Spec R_g` the restrictions of `Ẽ` and `ω̃` are the complexes
associated to `E ⊗_R R_g` and `ω ⊗_R R_g`, the second of injective amplitude in `[a, b]` because
localization preserves injectivity of modules over a Noetherian ring ([Stacks, Tag 0A6I]). As
`~` is fully faithful on derived categories ([Stacks, Tag 06Z0]) there is no degree-`n` morphism
between the restrictions for `n > b - k`, and this local vanishing bounds `R𝓗om(Ẽ, ω̃)` by
[Stacks, Tag 08DK].

## Main results

* `Stacks.Duality.subsingleton_shiftedHom_Q_of_isStrictlyGE_of_isStrictlyLE`: no degree-`n`
  morphism from a complex in degrees `≥ k` to a K-injective complex in degrees `≤ b`, `n > b - k`.
* `Stacks.Duality.isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude`: the bound above.

## References

* [Stacks Project, Tag 0A6I](https://stacks.math.columbia.edu/tag/0A6I)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
  Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor

namespace Stacks.Duality

/-- There is no degree-`n` morphism in the derived category from a complex vanishing below `k`
to a K-injective complex vanishing above `b`, for `n > b - k`. -/
theorem subsingleton_shiftedHom_Q_of_isStrictlyGE_of_isStrictlyLE {C : Type (u + 1)}
    [Category.{u} C] [Abelian C] (F I : CochainComplex C ℤ) [I.IsKInjective] (k b n : ℤ)
    (hF : F.IsStrictlyGE k) (hI : I.IsStrictlyLE b) (hn : b - k < n) :
    Subsingleton (ShiftedHom (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj I) n) := by
  have hX : IsZero ((F.HomComplex I).X n) := by
    refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    by_cases hp : p < k
    · exact (F.isZero_of_isStrictlyGE k p hp).eq_of_src _ _
    · exact (I.isZero_of_isStrictlyLE b q (by omega)).eq_of_tgt _ _
  exact (Equiv.subsingleton_congr
    (Stacks.SheafOfModules.homComplexHomologyEquivDerivedExt F I n)).mp
    (AddCommGrpCat.isZero_iff_subsingleton.mp (ShortComplex.isZero_homology_of_isZero_X₂ _ hX))

/-- Vanishing of a group of degree-`n` morphisms is invariant under isomorphisms of source and
target. -/
theorem subsingleton_shiftedHom_of_iso {D : Type*} [Category D] [HasShift D ℤ] {A A' B B' : D}
    (eA : A ≅ A') (eB : B ≅ B') (n : ℤ) (h : Subsingleton (ShiftedHom A' B' n)) :
    Subsingleton (ShiftedHom A B n) :=
  (Equiv.subsingleton_congr (Iso.homCongr eA ((shiftFunctor D n).mapIso eB))).mpr h

/-- A fully faithful functor commuting with the shift carries vanishing groups of degree-`n`
morphisms to vanishing ones. -/
theorem subsingleton_shiftedHom_map_of_fullyFaithful {D D' : Type*} [Category D] [Category D']
    [HasShift D ℤ] [HasShift D' ℤ] {G : D ⥤ D'} [G.CommShift ℤ] (hG : G.FullyFaithful)
    (A B : D) (n : ℤ) (h : Subsingleton (ShiftedHom A B n)) :
    Subsingleton (ShiftedHom (G.obj A) (G.obj B) n) :=
  (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _) ((G.commShiftIso n).app B))).mp
    ((Equiv.subsingleton_congr hG.homEquiv).mp h)

/-- **Local vanishing over an open immersion `Spec S ⟶ Spec R`.** Let `φ : R ⟶ S` be a ring map
whose spectrum is an open immersion with image `U`, and along which extension of scalars keeps
modules injective. For a complex `F` of `R`-modules vanishing below `k` and a bounded complex `I`
of injective `R`-modules vanishing above `b`, there is no degree-`n` morphism `F̃|_U ⟶ Ĩ|_U` in
the derived category of the slice site over `U`, for `n > b - k`. -/
theorem subsingleton_shiftedHom_overFunctor_tilde {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsOpenImmersion (Spec.map φ)]
    (hinj : ∀ M : ModuleCat.{u} R, Injective M → Injective ((ModuleCat.extendScalars φ.hom).obj M))
    (F I : CochainComplex (ModuleCat.{u} R) ℤ) (k a b n : ℤ) (hF : F.IsStrictlyGE k)
    (hIa : I.IsStrictlyGE a) (hIb : I.IsStrictlyLE b) (hI : ∀ i, Injective (I.X i))
    (hn : b - k < n) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (Spec R).ringCatSheaf
          (Spec.map φ).opensRange).mapDerivedCategory.obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj F)))
      ((SheafOfModules.overFunctor.{u} (Spec R).ringCatSheaf
          (Spec.map φ).opensRange).mapDerivedCategory.obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj I))) n) := by
  let f := Spec.map φ
  let U := f.opensRange
  let h := f.isoOpensRange
  refine Stacks.SheafOfModules.subsingleton_shiftedHom_of_equivalence (Scheme.Modules.overEquiv U)
    _ _ n ?_
  refine subsingleton_shiftedHom_of_iso
    ((Stacks.SheafOfModules.derivedOverFunctorEquiv U).app _)
    ((Stacks.SheafOfModules.derivedOverFunctorEquiv U).app _) n ?_
  let e := Stacks.AlgebraicGeometry.CoherentOfFiniteType.restrictEquivOfIso h.symm
  have : e.functor.Additive := inferInstanceAs (Scheme.Modules.restrictFunctor h.hom).Additive
  have : e.inverse.Additive := inferInstanceAs (Scheme.Modules.restrictFunctor h.inv).Additive
  refine Stacks.SheafOfModules.subsingleton_shiftedHom_of_equivalence e _ _ n ?_
  let c : ∀ W, e.functor.mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj W) ≅
        (Scheme.Modules.restrictFunctor f).mapDerivedCategory.obj W := fun W =>
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.restrictFunctor h.hom)).app W ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr
      ((Scheme.Modules.restrictFunctorComp h.hom U.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι f))).app W
  let t : ∀ G : CochainComplex (ModuleCat.{u} R) ℤ,
      (Scheme.Modules.restrictFunctor f).mapDerivedCategory.obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj G)) ≅
      (tilde.functor S).mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)) :=
    fun G =>
      (Scheme.Modules.restrictFunctor f).mapDerivedCategory.mapIso
          ((tilde.functor R).mapDerivedCategoryFactors.app G) ≪≫
        (Scheme.Modules.restrictFunctor f).mapDerivedCategoryFactors.app _ ≪≫
        DerivedCategory.Q.mapIso (Stacks.AffineTilde.restrictTildeComplexIso φ G) ≪≫
        ((tilde.functor S).mapDerivedCategoryFactors.app _).symm
  refine subsingleton_shiftedHom_of_iso (c _ ≪≫ t F) (c _ ≪≫ t I) n ?_
  refine subsingleton_shiftedHom_map_of_fullyFaithful
    (StandardModel.mapDerivedCategoryFullyFaithful S) _ _ n ?_
  let IS : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hISa : IS.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    (ModuleCat.extendScalars φ.hom).map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp hIa i hi)
  have hISb : IS.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi =>
    (ModuleCat.extendScalars φ.hom).map_isZero ((CochainComplex.isStrictlyLE_iff I b).mp hIb i hi)
  have hFS : CochainComplex.IsStrictlyGE (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F) k := (CochainComplex.isStrictlyGE_iff _ k).mpr fun i hi =>
    (ModuleCat.extendScalars φ.hom).map_isZero ((CochainComplex.isStrictlyGE_iff F k).mp hF i hi)
  have : ∀ i, Injective (IS.X i) := fun i => hinj _ (hI i)
  have : IS.IsKInjective := CochainComplex.isKInjective_of_injective IS a
  exact subsingleton_shiftedHom_Q_of_isStrictlyGE_of_isStrictlyLE _ IS k b n hFS hISb hn

/-- **The derived internal Hom into a complex of finite injective dimension on `Spec R`.** For
`R` Noetherian, `E` in `D^{≥ k}(R)` and `ω` of injective amplitude in `[a, b]`, the derived
internal Hom `R𝓗om(Ẽ, ω̃)` on `Spec R` lies in `D^{≤ b - k}`. -/
theorem isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude (R : CommRingCat.{u})
    [IsNoetherianRing R]
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
    [∀ M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]
    (E ω : DerivedCategory (ModuleCat.{u} R)) (k a b : ℤ) (hE : E.IsGE k)
    (hω : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b) :
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
      (op ((tilde.functor R).mapDerivedCategory.obj E))).obj
        ((tilde.functor R).mapDerivedCategory.obj ω)).IsLE (b - k) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := E.exists_iso_Q_obj_of_isGE k
  obtain ⟨I, hIa, hIb, hIinj, ⟨eI⟩⟩ := hω
  let tl := (tilde.functor R).mapDerivedCategory
  let e : ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op (tl.obj E))).obj
        (tl.obj ω) ≅
      ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op (tl.obj (DerivedCategory.Q.obj F)))).obj (tl.obj (DerivedCategory.Q.obj I)) :=
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso (tl.mapIso eF.symm).op).app _ ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj _).mapIso (tl.mapIso eI)
  suffices hX : (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op (tl.obj (DerivedCategory.Q.obj F)))).obj (tl.obj (DerivedCategory.Q.obj I))).IsLE
          (b - k) by
    exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (b - k)
  refine Stacks.SheafOfModules.isLE_derivedSheafHom_of_locally_subsingleton (Spec R).sheaf _ _
    (b - k) (fun U => ∃ g : R,
      U = (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).opensRange)
    (fun x U hxU => ?_) ?_
  · obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU U.2
    exact ⟨PrimeSpectrum.basicOpen g, hxg, hgU, g,
      (Scheme.Hom.opensRange_localizationAway g).symm⟩
  · rintro U ⟨g, rfl⟩ n hn
    exact subsingleton_shiftedHom_overFunctor_tilde
      (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
      (fun M _ => Dualizing.injective_extendScalars.{u, u} (Submonoid.powers g) M)
      F I k a b n hF hIa hIb hIinj (by omega)

end Stacks.Duality

end
