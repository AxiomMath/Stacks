module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SeparableTower
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Varieties with a smooth rational point

A variety over a field which has a rational point at which its structure morphism is smooth is
geometrically integral.

## Main results

* `AlgebraicGeometry.geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint`: geometric
  integrality follows from the existence of a smooth rational point.
* `AlgebraicGeometry.geometricallyIntegral_toSpecΓ_of_isRegularLocalRing`: an integral scheme
  proper over a field, with a point at which the local ring is regular and whose residue field
  is the field of global functions, is geometrically integral over that field.

## Implementation notes

A `k`-rational point is a section of the structure morphism; the underlying point is the image
of the generic point of `Spec k`, which is the unique point of that scheme.

The smooth open neighbourhood of the rational point is geometrically reduced and
geometrically normal, and it carries the section; so each of its base changes is connected and
normal, hence — being also Noetherian — irreducible. Both geometric reducedness and geometric
irreducibility then transfer from that open to the whole variety because the inclusion of a
nonempty open of an irreducible scheme is schematically dominant, a property stable under base
change.

## References

* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A quasi-compact scheme locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  ⟨⟩

/-- The base change to a field extension of a quasi-compact schematically dominant open immersion
`j : U ⟶ X` over `Spec k` receives a quasi-compact schematically dominant map to the base change
of `X`. -/
private theorem exists_isSchemeTheoreticallyDominant_pullback {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    ∃ v : pullback (j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      IsSchemeTheoreticallyDominant v ∧ QuasiCompact v := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsSchemeTheoreticallyDominant (pullback.snd j (pullback.fst f g)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (.of_hasPullback j (pullback.fst f g))
  exact ⟨(pullbackRightPullbackFstIso f g j).inv ≫ pullback.snd j (pullback.fst f g),
    inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 0CDW.** A variety over a field with a rational point at which its
structure morphism is smooth is geometrically integral. -/
@[stacks 0CDW]
theorem geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hsm : InfinitesimalLifting.SmoothAt f (s.base (genericPoint (Spec (.of k))))) :
    GeometricallyIntegral f := by
  obtain ⟨U, hxU, hUsmooth⟩ := hsm
  let j : (U : Scheme) ⟶ X := U.ι
  let fU : (U : Scheme) ⟶ Spec (.of k) := j ≫ f
  have hUsmooth' : Smooth fU := by
    let : Smooth (f.resLE ⊤ U le_top) := hUsmooth
    have hcomp : f.resLE ⊤ U le_top ≫ (⊤ : (Spec (.of k)).Opens).ι = j ≫ f := by
      simpa [j] using (Scheme.Hom.resLE_comp_ι f (U := ⊤) (V := U) le_top)
    change Smooth (j ≫ f)
    rw [← hcomp]
    infer_instance
  have : IrreducibleSpace X := inferInstance
  have : Nonempty U := ⟨⟨s.base (genericPoint (Spec (.of k))), hxU⟩⟩
  have : IrreducibleSpace U := U.ι.isOpenEmbedding.irreducibleSpace
  have : ConnectedSpace U := IrreducibleSpace.connectedSpace U
  have hsrange : Set.range s ⊆ Set.range j := by
    rintro z ⟨y, rfl⟩
    have hy : y = genericPoint (Spec (.of k)) := Subsingleton.elim _ _
    exact ⟨⟨s.base (genericPoint (Spec (.of k))), hxU⟩, by simp [j, hy]⟩
  let sU : Spec (.of k) ⟶ U := IsOpenImmersion.lift j s hsrange
  have hsU : sU ≫ fU = 𝟙 _ := by
    calc
      sU ≫ fU = (sU ≫ j) ≫ f := by simp [fU, Category.assoc]
      _ = s ≫ f := by rw [IsOpenImmersion.lift_fac j s hsrange]
      _ = 𝟙 _ := hs
  have hnormalU' : ∀ (K : Type u) [Field K] [Algebra k K],
      IsNormal (pullback fU (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ((geometricallyNormal_tfae k U fU).out 1 2).mp (isGeometricallyNormal_of_smooth fU)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_of_quasiCompact f
  have : QuasiCompact j := inferInstance
  have : QuasiCompact fU := inferInstance
  have hUdense : Dense (U : Set X) := U.2.dense ⟨s (genericPoint (Spec (.of k))), hxU⟩
  have : IsSchemeTheoreticallyDominant j := by
    rw [isSchemeTheoreticallyDominant_iff_isDominant, isDominant_iff]
    simpa [DenseRange, Scheme.Opens.range_ι, j] using hUdense
  have : GeometricallyReduced fU := geometricallyReduced_of_smooth fU
  have : GeometricallyReduced f := by
    constructor
    rw [AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    obtain ⟨v, _, _⟩ := exists_isSchemeTheoreticallyDominant_pullback (K := K) f j
    let pU := pullback fU (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    have : IsReduced pU :=
      (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp
        (GeometricallyReduced.geometrically_isReduced (f := fU))) K
    exact IsSchemeTheoreticallyDominant.isReduced v
  have : GeometricallyIrreducible f := by
    constructor
    rw [AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    obtain ⟨v, _, _⟩ := exists_isSchemeTheoreticallyDominant_pullback (K := K) f j
    let pU := pullback fU g
    have : ConnectedSpace pU :=
      (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp
        (geometricallyConnected_of_connectedSpace_of_section fU sU
          hsU).geometrically_connectedSpace) K
    have : Nonempty pU := by
      let sK : Spec (.of K) ⟶ pU := pullback.lift (g ≫ sU) (𝟙 _) (by simp [fU, hsU])
      exact ⟨sK.base (genericPoint (Spec (.of K)))⟩
    have : IsNoetherian pU :=
      isNoetherian_of_locallyOfFiniteType_of_quasiCompact (pullback.snd fU g)
    have : IrreducibleSpace pU := irreducibleSpace_of_isNormal_of_connectedSpace pU (hnormalU' K)
    have : IsDominant v := inferInstance
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set ↥(pullback f g))
    rw [← v.denseRange.closure_eq]
    simpa [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ pU).image v.base v.continuous.continuousOn).closure
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- On a proper integral scheme over a field whose global functions map isomorphically onto the
residue field at `x`, the point `x` is a rational point over the field of global functions: the
composite `Spec Γ(X, ⊤) ⟶ Spec κ(x) ⟶ X` is a section of `X.toSpecΓ`. -/
theorem fromSpecResidueField_comp_toSpecΓ_of_isIso_Γevaluation {X : Scheme.{u}} (x : X)
    [IsIso (X.Γevaluation x)] :
    (Spec.map (inv (X.Γevaluation x)) ≫ X.fromSpecResidueField x) ≫ X.toSpecΓ = 𝟙 _ := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop]
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, ⊤)).hom, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality (inv (X.Γevaluation x)), Category.id_comp,
    ← Category.assoc (X.fromSpecResidueField x).appTop, fromSpecResidueField_appTop x]
  simp

/-- **A regular point whose residue field is the field of global functions makes a proper
integral scheme geometrically integral over that field.** Let `X` be integral and proper over a
field `k`, and let `x ∈ X` be a point at which `Γ(X, 𝒪_X) ⟶ κ(x)` is an isomorphism and the local
ring is regular. Then `Γ(X, 𝒪_X)` is a field, `x` is a rational point over it at which
`X ⟶ Spec Γ(X, 𝒪_X)` is smooth, and so `X` is geometrically integral over `Γ(X, 𝒪_X)` by
[Stacks, Tag 0CDW]. -/
theorem geometricallyIntegral_toSpecΓ_of_isRegularLocalRing
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (x : X) [IsIso (X.Γevaluation x)] (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    letI : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
    GeometricallyIntegral X.toSpecΓ := by
  let A := Γ(X, ⊤)
  let : Field A := (isField_of_universallyClosed k f).toField
  let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let a : Spec (.of A) ⟶ Spec (.of k) := Spec.map α
  have hfa : X.toSpecΓ ≫ a = f := by
    dsimp [a, α]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have : IsProper (X.toSpecΓ ≫ a) := hfa ▸ inferInstance
  have : IsProper X.toSpecΓ := IsProper.of_comp (f := X.toSpecΓ) (g := a)
  have : IsVariety A X.toSpecΓ := ⟨⟩
  let s : Spec (.of A) ⟶ X := Spec.map (inv (X.Γevaluation x)) ≫ X.fromSpecResidueField x
  have hs : s ≫ X.toSpecΓ = 𝟙 _ := fromSpecResidueField_comp_toSpecΓ_of_isIso_Γevaluation x
  have hsx : s.base (genericPoint (Spec (.of A))) = x := by
    simp only [s, Scheme.Hom.comp_base, TopCat.comp_app]
    exact Scheme.fromSpecResidueField_apply x _
  refine geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint X.toSpecΓ s hs ?_
  rw [hsx]
  have hev : (Scheme.ΓSpecIso (.of A)).inv ≫ X.toSpecΓ.appTop ≫ X.Γevaluation x =
      X.Γevaluation x := by
    rw [Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_assoc _ _
  refine (smoothAt_iff_isRegularLocalRing_stalk X.toSpecΓ x ?_).mpr hreg
  let : Algebra A (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ X.toSpecΓ.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let e : X.residueField x ≃ₐ[A] A :=
    (AlgEquiv.ofBijective
      { toRingHom := (X.Γevaluation x).hom, commutes' := fun r => by
          change _ = ((Scheme.ΓSpecIso (.of A)).inv ≫ X.toSpecΓ.appTop ≫
            X.Γevaluation x).hom r
          rw [hev]; rfl }
      (ConcreteCategory.bijective_of_isIso (X.Γevaluation x))).symm
  have : Algebra.IsSeparable A (X.residueField x) := Algebra.IsSeparable.of_algHom A _ e.toAlgHom
  exact Algebra.IsSeparableExtension.of_isSeparable A _

end AlgebraicGeometry
