module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionDegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending the algebraically closed ground field of a smooth projective curve

Let `X` be a smooth projective curve over an algebraically closed field `k` and `k'/k` a field
extension. Then `X_{k'}` is a smooth projective curve over `k'` of the same genus. If `X` is
an open subscheme of `X̄` whose complement consists of closed points, the complement of
`X_{k'}` in `X̄_{k'}` has the same number of points.

## Main definitions

* `scalarExtensionOpenImmersion`: the base change `X_{k'} ⟶ X̄_{k'}` of an open immersion
  `X ⟶ X̄`.

## Main results

* `isCurve_scalarExtensionToSpec`: the scalar extension of a smooth curve over a separably
  closed field is a curve.
* `isProjectiveVariety_scalarExtension`: the scalar extension of a projective curve is projective.
* `genus_scalarExtension`: the scalar extension has the same genus.
* `natCard_compl_range_scalarExtensionOpenImmersion`: the number of points of `X̄ \ X` is
  unchanged by extending the algebraically closed ground field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The scalar extension `X_{k'}` is the pullback of `f : X ⟶ Spec k` along
`Spec k' ⟶ Spec k`. -/
theorem isPullback_scalarExtensionFst_scalarExtensionToSpec :
    IsPullback (scalarExtensionFst k k' f)
      (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  IsPullback.of_hasPullback _ _

/-- The scalar extension of a smooth scheme is smooth. -/
instance smooth_scalarExtensionToSpec [Smooth f] :
    Smooth (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) :=
  inferInstance

/-- The scalar extension of a smooth curve over a separably closed field `k` to a field
extension `k'` is a curve over `k'`. -/
@[ega "IV 4.4.4" "special case"]
theorem isCurve_scalarExtensionToSpec [IsSepClosed k] [IsCurve k f] [Smooth f] :
    IsCurve k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) := by
  have : IsNormal (scalarExtension k k' f) :=
    isNormal_of_isRegular _
      (isRegular_of_smooth_over_field (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f))
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : IrreducibleSpace (scalarExtension k k' f) :=
    GeometricallyIrreducible.irreducibleSpace
      (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) (Scheme.Hom.isOpenMap _)
  have : IsIntegral (scalarExtension k k' f) := isIntegral_of_irreducibleSpace_of_isReduced _
  refine { topologicalKrullDim_eq_one := ?_ }
  rw [topologicalKrullDim_baseChange k k' _ _ f
    (isPullback_scalarExtensionFst_scalarExtensionToSpec k' f)]
  exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)

/-- The scalar extension of a projective variety over a separably closed field is projective. -/
theorem isProjectiveVariety_scalarExtension [IsSepClosed k] [IsCurve k f] [Smooth f]
    [IsProjectiveVariety k f] :
    IsProjectiveVariety k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) :=
  have := isCurve_scalarExtensionToSpec k' f
  { isProjective := IsProjectiveMorphism.baseChange IsProjectiveVariety.isProjective _ }

/-- The genus of a proper scheme over `k` is unchanged by extending scalars to `k'`. -/
theorem genus_scalarExtension [IsProper f] :
    genus (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') f) = genus f :=
  genus_baseChange k k' _ _ f (isPullback_scalarExtensionFst_scalarExtensionToSpec k' f)

/-! ### The punctures of an affine curve are unchanged -/

section Punctures

variable {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) (j : X ⟶ Xbar) [IsOpenImmersion j]

/-- The base change of an open immersion `j : X ⟶ X̄` over `k` to `k'`, an open immersion
`X_{k'} ⟶ X̄_{k'}`. -/
def scalarExtensionOpenImmersion : scalarExtension k k' (j ≫ fbar) ⟶ scalarExtension k k' fbar :=
  (pullbackRightPullbackFstIso fbar (Spec.map (CommRingCat.ofHom (algebraMap k k'))) j).inv ≫
    pullback.snd j (scalarExtensionFst k k' fbar)

/-- The base change of an open immersion along `Spec k' ⟶ Spec k` is an open immersion. -/
instance : IsOpenImmersion (scalarExtensionOpenImmersion k' fbar j) := by
  unfold scalarExtensionOpenImmersion
  infer_instance

/-- The base change of `j` commutes with the structure morphisms of `X_{k'}` and `X̄_{k'}` to
`Spec k'`. -/
@[reassoc (attr := simp)]
theorem scalarExtensionOpenImmersion_snd :
    scalarExtensionOpenImmersion k' fbar j ≫
        Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') fbar =
      Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') (j ≫ fbar) := by
  simp [scalarExtensionOpenImmersion]

/-- The image of `X_{k'} ⟶ X̄_{k'}` is the preimage of the image of `j` under the projection
`X̄_{k'} ⟶ X̄`. -/
theorem range_scalarExtensionOpenImmersion :
    Set.range (scalarExtensionOpenImmersion k' fbar j).base =
      (scalarExtensionFst k k' fbar).base ⁻¹' Set.range j.base := by
  rw [scalarExtensionOpenImmersion, Scheme.Hom.comp_base, TopCat.coe_comp,
    (ConcreteCategory.bijective_of_isIso
      ((pullbackRightPullbackFstIso fbar _ j).inv.base)).2.range_comp,
    Scheme.Pullback.range_snd]

/-- Over an algebraically closed field `k`, the fibre of `X̄_{k'} ⟶ X̄` over a closed point
consists of exactly one point. -/
theorem existsUnique_scalarExtensionFst_eq_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType fbar] (x : Xbar) (hx : IsClosed ({x} : Set Xbar)) :
    ∃! z : scalarExtension k k' fbar, (scalarExtensionFst k k' fbar).base z = x := by
  set σ := pointOfClosedPoint fbar x hx
  set g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hσ : σ ≫ fbar = 𝟙 _ := pointOfClosedPoint_comp fbar x hx
  have : IsIso (σ ≫ fbar) := by
    rw [hσ]
    infer_instance
  let e : pullback σ (scalarExtensionFst k k' fbar) ≅ Spec (.of k') :=
    pullbackRightPullbackFstIso fbar g σ ≪≫ asIso (pullback.snd (σ ≫ fbar) g)
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have : Nonempty (Spec (.of k')) := inferInstanceAs (Nonempty (PrimeSpectrum k'))
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Subsingleton (pullback σ (scalarExtensionFst k k' fbar) : Scheme.{u}) :=
    e.hom.homeomorph.injective.subsingleton
  have : Nonempty (pullback σ (scalarExtensionFst k k' fbar) : Scheme.{u}) :=
    ⟨e.hom.homeomorph.symm (Classical.arbitrary _)⟩
  have hrange : Set.range σ.base = {x} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact pointOfClosedPoint_apply fbar x hx a
    · rintro rfl
      exact ⟨Classical.arbitrary _, pointOfClosedPoint_apply fbar _ hx _⟩
  have hmem : ∀ w, (scalarExtensionFst k k' fbar).base w = x →
      w ∈ Set.range (pullback.snd σ (scalarExtensionFst k k' fbar)).base := fun w hw => by
    rw [Scheme.Pullback.range_snd, hrange]
    exact hw
  obtain ⟨z, hz⟩ : x ∈ Set.range (scalarExtensionFst k k' fbar).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩
  refine ⟨z, hz, fun z' hz' => ?_⟩
  obtain ⟨a, rfl⟩ := hmem z hz
  obtain ⟨b, rfl⟩ := hmem z' hz'
  rw [Subsingleton.elim a b]

/-- **The number of punctures is unchanged by extending the algebraically closed ground
field**: if the complement of `j : X ⟶ X̄` consists of closed points, the complement of its base
change has the same number of points. -/
theorem natCard_compl_range_scalarExtensionOpenImmersion [IsAlgClosed k]
    [LocallyOfFiniteType fbar]
    (hcl : ∀ y, y ∉ Set.range j.base → IsClosed ({y} : Set Xbar)) :
    Nat.card ↥(Set.range (scalarExtensionOpenImmersion k' fbar j).base)ᶜ =
      Nat.card ↥(Set.range j.base)ᶜ := by
  rw [range_scalarExtensionOpenImmersion, ← Set.preimage_compl]
  refine Nat.card_congr (Equiv.ofBijective
    (fun z => ⟨(scalarExtensionFst k k' fbar).base z.1, z.2⟩) ⟨fun a b hab => ?_, fun y => ?_⟩)
  · obtain ⟨z, -, hz⟩ := existsUnique_scalarExtensionFst_eq_of_isAlgClosed k' fbar _ (hcl _ a.2)
    exact Subtype.ext ((hz a.1 rfl).trans (hz b.1 (congrArg Subtype.val hab).symm).symm)
  · obtain ⟨z, hz, -⟩ := existsUnique_scalarExtensionFst_eq_of_isAlgClosed k' fbar y.1 (hcl _ y.2)
    exact ⟨⟨z, by rw [Set.mem_preimage, hz]; exact y.2⟩, Subtype.ext hz⟩

end Punctures

end Stacks.EtaleCohomology

end
