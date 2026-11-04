module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RationalPointChart
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLocalFrobeniusData
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaGeometry

/-!
# The local ring of a compactification at a point at infinity

Let `k` be a field, `X ⟶ Spec k` a proper scheme whose base change `X_K` to a separable algebraic
extension `K` of `k` is a smooth curve, `V ⊆ X` an affine open (through an open immersion `j`)
and `y ∈ X` a point outside `V`. Then `X` is itself a smooth curve over `k` (smoothness and
dimension descend along `X_K ⟶ X`), so the local ring `𝒪_{X,y}` is a discrete valuation ring with
fraction field the function field of `V`; and some function on `V` is not in `𝒪_{X,y}`: if every
function on `V` were regular at `y`, the map `Spec 𝒪_{X,y} ⟶ V` they define would agree with
`Spec 𝒪_{X,y} ⟶ X` on the generic point, hence everywhere by separatedness, and `y` would lie in
`V`. The projection `X_K ⟶ X` is weakly étale, `K` being ind-étale over `k`.

These are the inputs at a point at infinity of a smooth compactification of a curve consumed by
`Stacks.EtaleCohomology.LAdicSheaf.IsBoundaryInertia`.

## Main results

* `Stacks.EtaleCohomology.weaklyEtale_specAlgebraMap` — `Spec K ⟶ Spec k` is weakly étale.
* `Stacks.EtaleCohomology.isCurve_and_smooth_of_fieldBaseChange` — descent of being a smooth curve.
* `Stacks.EtaleCohomology.mem_range_of_forall_mem_range_curveLocalRing` — the separatedness
  argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

-- Hom types must resolve `Quiver Scheme` through the category structure.
attribute [-instance] CategoryTheory.catToReflQuiver

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- **`Spec K ⟶ Spec k` is weakly étale for a separable algebraic extension `K / k`**: `K` is the
directed union of its finite separable, hence étale, subextensions. -/
theorem weaklyEtale_specAlgebraMap [Algebra.IsSeparable k K] :
    WeaklyEtale (specAlgebraMap k K) := by
  have hind : StacksDraft.IndEtale k K :=
    StacksDraft.indEtale_iff.mpr (ind_etale_of_isSeparable k K)
  have hw : Algebra.WeaklyEtale k K := Algebra.weaklyEtale_of_ind_etale hind
  rw [specAlgebraMap, weaklyEtale_specMap_iff]
  have he : (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra = ‹Algebra k K› :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [he]
  exact hw

variable {k} {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))

/-- **A proper scheme over `k` whose base change to `K` is a smooth curve is a smooth curve.**
Smoothness descends along the faithfully flat `Spec K ⟶ Spec k`; `X` is then reduced, it is
irreducible as the image of the irreducible `X_K`, and it has the dimension of `X_K`. -/
theorem isCurve_and_smooth_of_fieldBaseChange [IsProper fX]
    [IsCurve K (pullback.snd fX (specAlgebraMap k K))]
    [Smooth (pullback.snd fX (specAlgebraMap k K))] : IsCurve k fX ∧ Smooth fX := by
  have hsm : Smooth fX := smooth_of_smooth_fieldBaseChange fX K
  have : IsReduced X := isReduced_of_smooth fX
  have : IsIntegral (pullback fX (specAlgebraMap k K)) :=
    IsCurve.toIsVariety.toIsIntegral (k := K) (f := pullback.snd fX (specAlgebraMap k K))
  have : IrreducibleSpace X :=
    Function.Surjective.irreducibleSpace (pullback.fst fX (specAlgebraMap k K)).continuous
      (pullback.fst fX (specAlgebraMap k K)).surjective
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hdim : topologicalKrullDim X = 1 := by
    rw [← topologicalKrullDim_baseChange k K (pullback.fst fX (specAlgebraMap k K))
      (pullback.snd fX (specAlgebraMap k K)) fX (IsPullback.of_hasPullback fX _)]
    exact IsCurve.topologicalKrullDim_eq_one (k := K) (pullback.snd fX (specAlgebraMap k K))
  exact ⟨{ topologicalKrullDim_eq_one := hdim }, hsm⟩

end FieldExtension

section Separated

variable {S X V : Scheme.{u}} [IsAffine V] [IrreducibleSpace V] (j : V ⟶ X) [IsOpenImmersion j]
  {y : X} (hy : j.base (genericPoint V) ⤳ y)

omit [IsOpenImmersion j] in
/-- **A point at which every function on an affine open `V` is regular lies in `V`**, for `X`
separated over an affine base. If the map `𝒪_{X,y} → κ(η_V)` is injective and its image contains
every function on `V`, the functions on `V` define `Spec 𝒪_{X,y} ⟶ V`; it agrees with
`Spec 𝒪_{X,y} ⟶ X` on the dominant `Spec κ(η_V)`, hence everywhere, `𝒪_{X,y}` being a domain and
`X` separated; so the closed point, which maps to `y`, maps into `V`. -/
theorem mem_range_of_forall_mem_range_curveLocalRing [IsAffine S] (s : X ⟶ S) [IsSeparated s]
    (hinj : Function.Injective (curveLocalRingToFunctionField j hy).hom)
    (h : ∀ a : Γ(V, ⊤), (V.evaluation ⊤ (genericPoint V) trivial).hom a ∈
      Set.range (curveLocalRingToFunctionField j hy).hom) :
    y ∈ Set.range j.base := by
  let ψ := (curveLocalRingToFunctionField j hy).hom
  let φ := (V.evaluation ⊤ (genericPoint V) trivial).hom
  have : IsDomain (X.presheaf.stalk y) := hinj.isDomain ψ
  have : IsReduced (Spec (X.presheaf.stalk y)) :=
    (affine_isReduced_iff (X.presheaf.stalk y)).mpr (isReduced_of_injective ψ hinj)
  let eA : X.presheaf.stalk y ≃+* ψ.range :=
    RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), ψ.rangeRestrict_surjective⟩
  let θ : Γ(V, ⊤) →+* X.presheaf.stalk y :=
    eA.symm.toRingHom.comp (φ.codRestrict ψ.range fun a => h a)
  let θc : Γ(V, ⊤) ⟶ X.presheaf.stalk y := CommRingCat.ofHom θ
  have hθ : ∀ a, ψ (θ a) = φ a := fun a => by
    have h1 : eA (θ a) = φ.codRestrict ψ.range (fun a => h a) a := eA.apply_symm_apply _
    exact congrArg Subtype.val h1
  let ι : Spec (V.residueField (genericPoint V)) ⟶ Spec (X.presheaf.stalk y) :=
    Spec.map (curveLocalRingToFunctionField j hy)
  have : IsDominant ι := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap ψ)
    rw [DenseRange, dense_iff_closure_eq, PrimeSpectrum.closure_range_comap,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact PrimeSpectrum.zeroLocus_bot
  -- maps out of `Spec 𝒪_{X,y}` to an affine scheme are detected on `Spec κ(η_V)`
  have key : ∀ {R : CommRingCat.{u}} (f g : Spec (X.presheaf.stalk y) ⟶ Spec R),
      ι ≫ f = ι ≫ g → f = g := by
    intro R f g hfg
    rw [← Spec.map_preimage f, ← Spec.map_preimage g] at hfg ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at hfg
    have h2 := Spec.map_injective hfg
    congr 1
    ext r
    exact hinj (congrArg (fun χ => χ.hom r) h2)
  let g₁ : Spec (X.presheaf.stalk y) ⟶ X := Spec.map θc ≫ V.isoSpec.inv ≫ j
  have hev : Spec.map (V.evaluation ⊤ (genericPoint V) trivial) ≫ V.isoSpec.inv =
      V.fromSpecResidueField (genericPoint V) := by
    rw [← cancel_mono V.isoSpec.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    show _ = V.fromSpecResidueField (genericPoint V) ≫ V.toSpecΓ
    rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
      ← Spec.map_comp]
    rfl
  have hU : ι ≫ g₁ = ι ≫ X.fromSpecStalk y := by
    have h1 : θc ≫ curveLocalRingToFunctionField j hy =
        V.evaluation ⊤ (genericPoint V) trivial := by
      ext a
      exact hθ a
    show Spec.map (curveLocalRingToFunctionField j hy) ≫ Spec.map θc ≫
      V.isoSpec.inv ≫ j = _
    rw [← Spec.map_comp_assoc, h1, ← Category.assoc, hev]
    exact (specMap_curveLocalRingToFunctionField_comp_fromSpecStalk j hy).symm
  have hs : g₁ ≫ s = X.fromSpecStalk y ≫ s := by
    rw [← cancel_mono S.isoSpec.hom]
    simp only [Category.assoc]
    apply key
    rw [← Category.assoc ι g₁, hU, Category.assoc]
  have hfg : g₁ = X.fromSpecStalk y := ext_of_isDominant_of_isSeparated s hs ι hU
  refine ⟨(Spec.map θc ≫ V.isoSpec.inv).base
    (closedPoint (X.presheaf.stalk y)), ?_⟩
  have h3 := congrArg (fun g : Spec (X.presheaf.stalk y) ⟶ X =>
    g.base (closedPoint (X.presheaf.stalk y))) hfg
  simp only [g₁] at h3
  rw [Scheme.fromSpecStalk_closedPoint] at h3
  exact h3

end Separated

end Stacks.EtaleCohomology

end
