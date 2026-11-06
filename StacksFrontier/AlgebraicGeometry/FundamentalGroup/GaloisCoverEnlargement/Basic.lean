module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenFinitelyManyComponents
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.NormalStrictHenselization
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Enlarging the open over which a generic Galois cover extends: restriction and Galois structure

Let `f : X ⟶ S` be a flat morphism from a normal locally Noetherian scheme to an integral scheme,
and let `U ⊆ U'` be opens of `S` with `U` containing the generic point. Every point of `f⁻¹(U')`
generizes into `f⁻¹(U)`, so restriction of finite étale covers from `f⁻¹(U')` to `f⁻¹(U)` is
fully faithful, by [Stacks, Tag 0BQG] at the normal local rings. Consequently a finite étale
cover of `f⁻¹(U')` extending a Galois cover of `f⁻¹(U)` is connected and carries a unique
compatible Galois structure, which is the last step of the enlargement in the proof of
[Stacks, Tag 0EYJ].

## Main results

* `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_of_isNormal`: restriction of
  finite étale covers of a normal locally Noetherian scheme to a dense open is fully faithful.
* `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_of_isOpenImmersion`: the same
  for an open immersion with dense image.
* `AlgebraicGeometry.Abhyankar.galoisExtendsOver_of_extension`: if `Z` extends over `U` by `Y`,
  and `Y` extends to a finite étale cover of `f⁻¹(U')`, then `Z` extends over `U'`.

## References

* [Stacks Project, Tag 0BQG](https://stacks.math.columbia.edu/tag/0BQG)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **Restriction to a dense open of a normal locally Noetherian scheme is fully faithful** on
finite étale covers: [Stacks, Tag 0BQG], the punctured spectra of the strict henselizations of
the normal local rings outside the open being connected. -/
@[sga "7 II 2.3.1" "partial"]
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_of_isNormal {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens) (hdense : Dense (U : Set X)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite := by
    intro V hV
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V.toScheme := ⟨⟩
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := V.toScheme)
  refine fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents _ _ hfinite hdense ?_
  intro p hp
  have : IsIntegrallyClosed (X.presheaf.stalk p) := IsNormal.stalk_normal p
  refine isConnectedPuncturedStrictHenselization_of_isIntegrallyClosed _ fun hfield ↦ hp ?_
  exact scheme_genericPoints_mem_dense_open X U.2 hdense
    ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X p).mp
      (ringKrullDim_eq_zero_of_isField hfield))

/-- **Restriction along an open immersion with dense image into a normal locally Noetherian
scheme is fully faithful** on finite étale covers. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_of_isOpenImmersion {X V : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (j : V ⟶ X) [IsOpenImmersion j]
    (hdense : Dense (Set.range j)) :
    Nonempty (finiteEtaleBaseChange j).FullyFaithful := by
  obtain ⟨h⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_of_isNormal j.opensRange
    (by simpa using hdense)
  let e := j.isoOpensRange
  have : (finiteEtaleBaseChange e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange e.hom) (finiteEtaleBaseChange e.inv)
      (finiteEtaleBaseChangeId.symm ≪≫
        finiteEtaleBaseChangeComp e.inv e.hom (𝟙 _) e.inv_hom_id.symm)
      ((finiteEtaleBaseChangeComp e.hom e.inv (𝟙 _) e.hom_inv_id.symm).symm ≪≫
        finiteEtaleBaseChangeId)).isEquivalence_functor
  exact ⟨(h.comp (Functor.FullyFaithful.ofFullyFaithful (finiteEtaleBaseChange e.hom))).ofIso
    (finiteEtaleBaseChangeComp e.hom j.opensRange.ι j (Scheme.Hom.isoOpensRange_hom_ι j).symm).symm⟩

namespace Abhyankar

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]

/-- For opens `U ≤ U'` of `S` containing the generic point, the map from the generic fibre into
`f⁻¹(U)` followed by the inclusion `f⁻¹(U) ⟶ f⁻¹(U')` is the map from the generic fibre into
`f⁻¹(U')`. -/
@[reassoc]
lemma genericFiberToPreimage_homOfLE {U U' : S.Opens} (hUU' : U ≤ U') (hη : genericPoint S ∈ U) :
    genericFiberToPreimage f U hη ≫ X.homOfLE (f.preimage_mono hUU') =
      genericFiberToPreimage f U' (hUU' hη) := by
  rw [← cancel_mono (f ⁻¹ᵁ U').ι, Category.assoc, Scheme.homOfLE_ι, genericFiberToPreimage_ι,
    genericFiberToPreimage_ι]

/-- For `f` flat onto an integral scheme and `U ∋ η`, every point of `f⁻¹(U')` generizes into
`f⁻¹(U)`. -/
lemma exists_specializes_mem_preimage [Flat f] {U U' : S.Opens} (hUU' : U ≤ U')
    (hη : genericPoint S ∈ U) (x : (f ⁻¹ᵁ U').toScheme) :
    ∃ y ∈ Set.range (X.homOfLE (f.preimage_mono hUU')), y ⤳ x := by
  obtain ⟨x', hx'x, hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f x.1))
  have hx'U' : x' ∈ f ⁻¹ᵁ U' := hx'x.mem_open (f ⁻¹ᵁ U').isOpen x.2
  have hx'U : x' ∈ f ⁻¹ᵁ U := by
    show f x' ∈ U
    rwa [hfx']
  exact ⟨⟨x', hx'U'⟩, ⟨⟨x', hx'U⟩, Scheme.homOfLE_apply' _ _ _⟩,
    Topology.IsInducing.subtypeVal.specializes_iff.mp hx'x⟩

/-- The part of a flat scheme over `f⁻¹(U')` lying over `f⁻¹(U)` is dense. -/
lemma dense_range_fst_homOfLE [Flat f] {U U' : S.Opens} (hUU' : U ≤ U')
    (hη : genericPoint S ∈ U) {Y : Scheme.{u}} (p : Y ⟶ (f ⁻¹ᵁ U').toScheme) [Flat p] :
    Dense (Set.range (pullback.fst p (X.homOfLE (f.preimage_mono hUU')))) := by
  intro y
  obtain ⟨x', ⟨x'', rfl⟩, hx'⟩ := exists_specializes_mem_preimage f hUU' hη (p y)
  obtain ⟨y', hy'y, hpy'⟩ := Flat.generalizingMap p hx'
  refine hy'y.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨x'', hpy'.symm⟩

variable {G : Type v} [Group G] [Finite G] (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)

/-- **Enlarging the open over which `Z` extends.** Let `f` be flat with normal locally Noetherian
source. If `Z` extends over `U` by the Galois cover `Y` of `f⁻¹(U)`, and `Y` is the restriction of
a finite étale cover `F` of `f⁻¹(U')` for some `U' ⊇ U`, then `Z` extends over `U'`: `F` is
connected and carries a compatible Galois structure, because restriction from `f⁻¹(U')` to the
dense open `f⁻¹(U)` is fully faithful. -/
theorem galoisExtendsOver_of_extension [Flat f] [IsLocallyNoetherian X] [IsNormal X]
    {U U' : S.Opens} (hUU' : U ≤ U') (hη : genericPoint S ∈ U)
    (Y : FiniteEtaleGaloisCover (f ⁻¹ᵁ U).toScheme G)
    (e : (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).obj Y.obj ≅ Z.obj)
    (he : ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).map
      (Y.action g).asIso.hom ≫ e.hom = e.hom ≫ (Z.action g).asIso.hom)
    (F : FiniteEtaleOver (f ⁻¹ᵁ U').toScheme)
    (eF : (finiteEtaleBaseChange (X.homOfLE (f.preimage_mono hUU'))).obj F ≅ Y.obj) :
    GaloisExtendsOver f Z U' := by
  let j := X.homOfLE (f.preimage_mono hUU')
  have hj : Dense (Set.range j) := by
    simpa [Scheme.Pullback.range_fst] using dense_range_fst_homOfLE f hUU' hη (𝟙 _)
  obtain ⟨hff⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_of_isOpenImmersion j hj
  have : Etale F.hom := F.prop.2
  have hconn : ConnectedSpace F.left := by
    have : ConnectedSpace Y.obj.left := Y.connected
    let eL : ((finiteEtaleBaseChange j).obj F).left ≅ Y.obj.left :=
      (MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).mapIso eF
    have hs : Function.Surjective eL.inv := fun y ↦
      ⟨eL.hom y, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
    have : ConnectedSpace ((finiteEtaleBaseChange j).obj F).left :=
      hs.connectedSpace eL.inv.continuous
    have hd : DenseRange (finiteEtaleBaseChangeProj j F) :=
      dense_range_fst_homOfLE f hUU' hη F.hom
    have : PreconnectedSpace F.left :=
      hd.preconnectedSpace (finiteEtaleBaseChangeProj j F).continuous
    obtain ⟨y⟩ := (inferInstance : Nonempty ((finiteEtaleBaseChange j).obj F).left)
    exact { toNonempty := ⟨finiteEtaleBaseChangeProj j F y⟩ }
  obtain ⟨Y', e₁, he₁⟩ := exists_finiteEtaleGaloisCover_of_fullyFaithful j hff G F hconn Y eF
  let c := finiteEtaleBaseChangeComp (genericFiberToPreimage f U hη) j
    (genericFiberToPreimage f U' (hUU' hη)) (genericFiberToPreimage_homOfLE f hUU' hη).symm
  refine ⟨hUU' hη, Y', c.app Y'.obj ≪≫
    (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).mapIso e₁ ≪≫ e, fun g ↦ ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, c.hom.naturality, Category.assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, he₁, Functor.map_comp_assoc, he, Category.assoc, Category.assoc]

end Abhyankar

end AlgebraicGeometry
