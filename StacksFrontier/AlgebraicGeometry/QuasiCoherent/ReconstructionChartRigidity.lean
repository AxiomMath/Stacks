module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineCatCenter
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalIso
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionPairInverse

/-!
# Rigidity of a reconstruction chart at the level of natural transformations

`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` is the rigidity of the
reconstruction pair for *morphisms*: two morphisms with isomorphic inverse-image-and-tensor
functors are equal.  The gluing step of [Stacks, Tag 0GPJ] needs the companion statement one
level up, for *natural transformations*: an endomorphism of one such functor which is the
identity at the structure sheaf is the identity.  This file proves it.

That is the statement the comparison of functors in [Stacks, Tag 0GPJ] is missing.  The
per-chart comparisons `e(F)|_{V i} ≅ (g^*F ⊗ M)|_{V i}` are each obtained from an existential
choice, so two of them over an open contained in two charts differ by an automorphism of the
chart functor; normalising the family at `𝒪_X` makes that automorphism the identity there, and
the theorem below then makes it the identity.  The difference cannot be dismissed without such
an argument: automorphisms of the identity functor of `QCoh(𝒪_W)` form the units of
`Γ(W, 𝒪_W)`, and it is exactly their failure to be globally trivial that makes the invertible
module `L` of the tag necessary in the first place.

## The reduction

Let `U ⊆ X` be an affine open of a quasi-compact quasi-separated scheme, let `β : W ≅ U` be an
isomorphism of schemes and let `N` be an invertible sheaf of `𝒪_W`-modules.  The functor in
question is `F ↦ (β ≫ U.ι)^*F ⊗ N` on `QCoh(𝒪_X)`.  Three cancellations reduce an endomorphism
of it to a central element of `QCoh(𝒪_U)`:

1. *the target is localised to `U`.*  The functor is restriction to `U` followed by
   `F ↦ β^*F ⊗ N` (`AlgebraicGeometry.pullbackTensorFunctorQuasicoherentRestrictIso`), and
   restriction `QCoh(𝒪_X) ⥤ QCoh(𝒪_U)` is a localization by [Stacks, Tag 0GPH]
   (`AlgebraicGeometry.quasicoherentRestriction_isLocalization`), so whiskering with it is
   fully faithful on functors out of `QCoh(𝒪_U)`
   (`CategoryTheory.Localization.fullyFaithfulWhiskeringLeft`) and the endomorphism descends.
2. *the chart functor is cancelled.*  `F ↦ β^*F ⊗ N` is the inclusion of the quasi-coherent
   modules followed by `AlgebraicGeometry.twistedPullback`, which is an equivalence because `β`
   is an isomorphism and `N` is invertible
   (`AlgebraicGeometry.twistedPullback_isEquivalence`); the composite is fully faithful, so the
   descended endomorphism is the image of an endomorphism of the identity functor of
   `QCoh(𝒪_U)`.
3. *the centre of `QCoh(𝒪_U)` is `Γ(U, 𝒪_U)`.*  `U` is affine, so
   `AlgebraicGeometry.catCenter_eq_one_of_app_unit_eq_id` applies: the endomorphism is the
   identity at `𝒪_U`, which is the restriction of `𝒪_X`, hence is the identity.

## The normalisation at `𝒪_X` costs nothing

One might expect the per-chart comparisons to have to be *corrected* by a unit of
`Γ(V i, 𝒪)` before they agree at `𝒪_X`.  They do not, provided the single invertible module is
the one `AlgebraicGeometry.exists_isOpenCover_invertibleModule_restrictIso_of_isAffineOpenCover`
produces: its restriction to `V i` is identified with `L i` by
`AlgebraicGeometry.restrictMapUnitIsoOfChartIso`, which is built from the very isomorphisms
`α i` and `β i` read at the structure sheaf.  A comparison assembled from `α i`, `β i` and that
identification therefore has, at `𝒪_X`, a composite of an isomorphism with its own inverse.  The
normalisation is automatic, and no action of the units of `Γ(V i, 𝒪)` on natural transformations
has to be constructed.

## Main results

* `AlgebraicGeometry.catCenterOfFullyFaithful` — an endomorphism of a fully faithful functor is
  the image of an endomorphism of the identity functor of its source.
* `AlgebraicGeometry.fullyFaithfulPullbackTensorFunctor` — the chart functor `F ↦ β^*F ⊗ N` is
  fully faithful when `β` is an isomorphism and `N` is invertible.
* `AlgebraicGeometry.natTrans_eq_id_of_app_restrictUnit` — the rigidity over the affine chart,
  before the target is localised.
* `AlgebraicGeometry.natTrans_eq_id_of_app_unit_eq_id` — **the rigidity**: an endomorphism of
  `F ↦ (β ≫ U.ι)^*F ⊗ N` which is the identity at the structure sheaf is the identity.
* `AlgebraicGeometry.natIso_eq_of_app_unit_eq` and
  `AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` — the form the gluing consumes: two
  natural isomorphisms into that functor, or into any functor isomorphic to it, which agree at
  the structure sheaf are equal.

## Implementation notes

The proof is cut into separate top-level declarations rather than written as one tactic block.
The heartbeat budget is per declaration, and the whole argument as a single theorem exceeds it:
the localization instance of [Stacks, Tag 0GPH], the full faithfulness of the chart functor and
the transport of the centre each cost a substantial fraction of it on their own.  The two purely
categorical steps — cancelling a fully faithful functor out of an endomorphism, and recognising
an endomorphism conjugate to the identity — are stated for abstract categories, where they are
cheap, and the descended transformation is introduced by `obtain` so that its type is fixed once
rather than re-inferred through
`CategoryTheory.Localization.fullyFaithfulWhiskeringLeft` at every use.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list
is declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### Cancelling a fully faithful functor out of an endomorphism -/

/-- **An endomorphism of a fully faithful functor comes from an endomorphism of the identity
functor.**  For `Φ : C ⥤ D` fully faithful and `σ : Φ ⟶ Φ`, taking the preimage of each
component gives an endomorphism of `𝟭 C`; its naturality is the naturality of `σ`, read through
the faithfulness of `Φ`. -/
def catCenterOfFullyFaithful {C : Type*} [Category* C] {D : Type*} [Category* D] {Φ : C ⥤ D}
    (hΦ : Φ.FullyFaithful) (σ : Φ ⟶ Φ) : CatCenter C :=
  End.of
    { app A := hΦ.preimage (σ.app A)
      naturality A B φ := hΦ.map_injective (by simp) }

/-- The image under `Φ` of the component at `A` of `catCenterOfFullyFaithful hΦ σ` is the
component `σ.app A`. -/
@[simp]
theorem map_catCenterOfFullyFaithful_app {C : Type*} [Category* C] {D : Type*} [Category* D]
    {Φ : C ⥤ D} (hΦ : Φ.FullyFaithful) (σ : Φ ⟶ Φ) (A : C) :
    Φ.map ((catCenterOfFullyFaithful hΦ σ).app A) = σ.app A :=
  hΦ.map_preimage _

/-- **An endomorphism of a fully faithful functor whose attached central element is trivial is
the identity.**  The component at `B` is the image of the component of the central element,
which is the identity. -/
theorem eq_id_of_catCenterOfFullyFaithful_eq_one {C : Type*} [Category* C] {D : Type*}
    [Category* D] {Φ : C ⥤ D} (hΦ : Φ.FullyFaithful) (σ : Φ ⟶ Φ)
    (h : catCenterOfFullyFaithful hΦ σ = 1) : σ = 𝟙 Φ := by
  ext B
  rw [← map_catCenterOfFullyFaithful_app hΦ σ B, h]
  simp [CatCenter.app_one]

/-- **An endomorphism conjugate to the identity is the identity.** -/
theorem eq_id_of_conj_eq_id {C : Type*} [Category* C] {G H : C} (κ : G ≅ H) (τ : H ⟶ H)
    (h : κ.hom ≫ τ ≫ κ.inv = 𝟙 G) : τ = 𝟙 H := by
  have h1 : τ ≫ κ.inv = κ.inv := by
    rw [← Iso.cancel_iso_hom_left κ (τ ≫ κ.inv) κ.inv, h, Iso.hom_inv_id]
  have h2 : τ ≫ κ.inv ≫ κ.hom = κ.inv ≫ κ.hom := by rw [← Category.assoc, h1]
  rwa [Iso.inv_hom_id, Category.comp_id] at h2

/-! ### The chart functor is fully faithful -/

/-- **A reconstruction chart functor is fully faithful.**  For `β : W ≅ U` an isomorphism of
schemes and `N` an invertible sheaf of `𝒪_W`-modules, `F ↦ β^*F ⊗ N` on `QCoh(𝒪_U)` is the
inclusion of the quasi-coherent modules (fully faithful) followed by
`AlgebraicGeometry.twistedPullback`, which is an equivalence
(`AlgebraicGeometry.twistedPullback_isEquivalence`). -/
def fullyFaithfulPullbackTensorFunctor {U W : Scheme.{u}} (β : W ≅ U)
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N) :
    (pullbackTensorFunctor β.hom N).FullyFaithful :=
  haveI : (twistedPullback β.hom N).IsEquivalence := twistedPullback_isEquivalence β N hN
  (ObjectProperty.fullyFaithfulι (SheafOfModules.isQuasicoherent U.ringCatSheaf)).comp
    (Functor.FullyFaithful.ofFullyFaithful (twistedPullback β.hom N))

/-- **The restriction to an open of a quasi-coherent module isomorphic to the structure sheaf is
the structure sheaf.**  Restriction along an open immersion is a functor, and it takes `𝒪_X` to
`𝒪_U` (`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`). -/
def restrictUnitIsoQuasicoherentRestriction {X : Scheme.{u}} (U : X.Opens)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : A.obj ≅ SheafOfModules.unit X.ringCatSheaf) :
    ((quasicoherentRestriction U.ι).obj A).obj ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso hA ≪≫ Scheme.Modules.restrictUnitIso U.ι

/-! ### The rigidity over the affine chart -/

/-- **An endomorphism of `F ↦ β^*F ⊗ N` on `QCoh(𝒪_U)`, `U` affine, which is the identity at the
structure sheaf is the identity.**  The chart functor is fully faithful
(`AlgebraicGeometry.fullyFaithfulPullbackTensorFunctor`), so the endomorphism is the image of an
endomorphism of the identity functor of `QCoh(𝒪_U)`, and that is the identity by
`AlgebraicGeometry.catCenter_eq_one_of_app_unit_eq_id`.

The object at which the endomorphism is prescribed is the restriction to `U` of a quasi-coherent
`𝒪_X`-module isomorphic to `𝒪_X`, which is how the global statement below hands it over. -/
theorem natTrans_eq_id_of_app_restrictUnit {X W : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (β : W ≅ U.toScheme) (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : Nonempty (A.obj ≅ SheafOfModules.unit X.ringCatSheaf))
    (σ : pullbackTensorFunctor β.hom N ⟶ pullbackTensorFunctor β.hom N)
    (hσ : σ.app ((quasicoherentRestriction U.ι).obj A) = 𝟙 _) :
    σ = 𝟙 (pullbackTensorFunctor β.hom N) := by
  have hUaff : IsAffine U.toScheme := hU
  have hPff := fullyFaithfulPullbackTensorFunctor β N hN
  refine eq_id_of_catCenterOfFullyFaithful_eq_one hPff σ ?_
  refine catCenter_eq_one_of_app_unit_eq_id U.toScheme _
    ((quasicoherentRestriction U.ι).obj A)
    ⟨restrictUnitIsoQuasicoherentRestriction U A hA.some⟩ ?_
  refine hPff.map_injective ?_
  rw [map_catCenterOfFullyFaithful_app, CategoryTheory.Functor.map_id, hσ]

/-! ### The rigidity -/

/-- **An endomorphism of a reconstruction chart functor which is the identity at the structure
sheaf is the identity.**  Let `X` be a quasi-compact quasi-separated scheme, let `U ⊆ X` be an
affine open, let `β : W ≅ U` be an isomorphism of schemes and let `N` be an invertible sheaf of
`𝒪_W`-modules.  If `τ` is an endomorphism of the functor `F ↦ (β ≫ U.ι)^*F ⊗ N` on `QCoh(𝒪_X)`
whose component at a quasi-coherent module `A` with `A ≅ 𝒪_X` is the identity, then `τ` is the
identity.

The three cancellations are described in the module documentation: the localization of
[Stacks, Tag 0GPH], the chart equivalence, and the centre of the quasi-coherent modules on the
affine `U`. -/
theorem natTrans_eq_id_of_app_unit_eq_id {X W : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U) (β : W ≅ U.toScheme)
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : Nonempty (A.obj ≅ SheafOfModules.unit X.ringCatSheaf))
    (τ : pullbackTensorFunctor (β.hom ≫ U.ι) N ⟶ pullbackTensorFunctor (β.hom ≫ U.ι) N)
    (hτ : τ.app A = 𝟙 _) :
    τ = 𝟙 (pullbackTensorFunctor (β.hom ≫ U.ι) N) := by
  have : (quasicoherentRestriction U.ι).IsLocalization
      (quasicoherentSupportedOn X ((U : Set X)ᶜ)).isoModSerre :=
    quasicoherentRestriction_isLocalization X ((U : Set X)ᶜ) U (compl_compl _).symm hU.isCompact
  have κ : quasicoherentRestriction U.ι ⋙ pullbackTensorFunctor β.hom N ≅
      pullbackTensorFunctor (β.hom ≫ U.ι) N :=
    pullbackTensorFunctorQuasicoherentRestrictIso U β.hom N
  have hFF := Localization.fullyFaithfulWhiskeringLeft (quasicoherentRestriction U.ι)
    (quasicoherentSupportedOn X ((U : Set X)ᶜ)).isoModSerre
    (SheafOfModules.{u} W.ringCatSheaf)
  obtain ⟨σ, hσmap⟩ : ∃ σ : pullbackTensorFunctor β.hom N ⟶ pullbackTensorFunctor β.hom N,
      Functor.whiskerLeft (quasicoherentRestriction U.ι) σ = κ.hom ≫ τ ≫ κ.inv :=
    ⟨hFF.preimage (κ.hom ≫ τ ≫ κ.inv), hFF.map_preimage _⟩
  have hσapp : σ.app ((quasicoherentRestriction U.ι).obj A) = 𝟙 _ := by
    have happ := congrArg (fun ν => NatTrans.app ν A) hσmap
    simp only [Functor.whiskerLeft_app] at happ
    rw [happ, NatTrans.comp_app, NatTrans.comp_app, hτ, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  refine eq_id_of_conj_eq_id κ τ ?_
  rw [← hσmap, natTrans_eq_id_of_app_restrictUnit U hU β N hN A hA σ hσapp]
  exact Functor.whiskerLeft_id' _

/-- **Two natural transformations out of a reconstruction chart functor which agree at the
structure sheaf are equal.**  This is
`AlgebraicGeometry.natTrans_eq_id_of_app_unit_eq_id` in the form the gluing of the per-chart
comparisons consumes: the difference of two such transformations, conjugated back to an
endomorphism of the source, is the identity. -/
theorem natIso_eq_of_app_unit_eq {X W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsAffineOpen U) (β : W ≅ U.toScheme)
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : Nonempty (A.obj ≅ SheafOfModules.unit X.ringCatSheaf))
    {G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} W.ringCatSheaf}
    (θ θ' : G ≅ pullbackTensorFunctor (β.hom ≫ U.ι) N)
    (h : θ.hom.app A = θ'.hom.app A) : θ = θ' := by
  have hid : θ.inv ≫ θ'.hom = 𝟙 _ := by
    refine natTrans_eq_id_of_app_unit_eq_id U hU β N hN A hA _ ?_
    rw [NatTrans.comp_app, ← h, Iso.inv_hom_id_app]
  have : θ'.hom = θ.hom := by
    rw [← Category.id_comp θ'.hom, ← Iso.hom_inv_id θ, Category.assoc, hid, Category.comp_id]
  exact Iso.ext this.symm

/-- **Two natural isomorphisms into a functor isomorphic to a reconstruction chart functor
which agree at the structure sheaf are equal.**  This is
`AlgebraicGeometry.natIso_eq_of_app_unit_eq` with the target allowed to be any functor
isomorphic to `F ↦ (β ≫ U.ι)^*F ⊗ N`, which is the form the gluing of the per-chart
comparisons needs: there the common target is the restriction to an open of the single global
functor `F ↦ g^*F ⊗ M`, and its identification with a chart functor is a composite of the
comparison isomorphisms for restriction, inverse image and the tensor product, not an
equality. -/
theorem natIso_eq_of_app_unit_eq_of_iso {X W : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U) (β : W ≅ U.toScheme)
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : Nonempty (A.obj ≅ SheafOfModules.unit X.ringCatSheaf))
    {G P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} W.ringCatSheaf}
    (ρ : P ≅ pullbackTensorFunctor (β.hom ≫ U.ι) N) (θ θ' : G ≅ P)
    (h : θ.hom.app A = θ'.hom.app A) : θ = θ' := by
  have hcomp : θ ≪≫ ρ = θ' ≪≫ ρ := by
    refine natIso_eq_of_app_unit_eq U hU β N hN A hA _ _ ?_
    simp only [Iso.trans_hom, NatTrans.comp_app, h]
  have h2 := congrArg Iso.hom hcomp
  simp only [Iso.trans_hom] at h2
  exact Iso.ext ((Iso.cancel_iso_hom_right _ _ ρ).1 h2)

end AlgebraicGeometry

end
