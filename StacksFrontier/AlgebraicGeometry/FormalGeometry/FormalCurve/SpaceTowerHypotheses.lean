module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFromThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus

/-!
# Properness, separatedness and dimension along a tower over a formal curve

Let `X₀ ⟶ X₁ ⟶ ⋯` be a cartesian tower of algebraic spaces over the adic thickenings
`Sₙ = Spec (A / I ^ (n + 1))` of a Noetherian ring. If `X₀ ⟶ S₀` is proper and `dim X₀ ≤ 1`, then
every member `Xₙ` is separated and locally Noetherian, and its local rings have dimension at most
one.

## Main results

* `AlgebraicGeometry.Space.exists_adicTower_thickening_iso`: each member is a finite-order
  thickening of the next, identified with the inverse image of `Sₙ ⊆ Sₙ₊₁`.
* `AlgebraicGeometry.Space.isProper_adicTower`: every `Xₙ ⟶ Sₙ` is proper.
* `AlgebraicGeometry.Space.isAbsolutelySeparated_adicTower`,
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_adicTower`: every `Xₙ`
  is separated and locally Noetherian.
* `AlgebraicGeometry.Space.dimension_adicTower_eq`,
  `AlgebraicGeometry.Space.localRingDimension_le_one_adicTower`: the dimension is constant
  along the tower, and every local ring has dimension at most one.
* `AlgebraicGeometry.Space.isRepresentable_of_forall_mem_range`: an algebraic space each of
  whose points lies in a representable open subspace is representable.

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- The transition morphism between consecutive adic thickening objects is a finite-order
thickening of the algebraic spaces they represent. -/
theorem isFiniteOrderThickening_range_adicThickeningSuccMap [IsNoetherianRing A] (n : ℕ) :
    IsFiniteOrderThickening B (Spec (.of A)) hS
      ((schemeSpaceFunctor B (Spec (.of A)) hS).obj (adicThickeningObject A I B hS hSn (n + 1)))
      (Subfunctor.range (yoneda.map (adicThickeningSuccMap A I B hS hSn n))) := by
  have h : Stacks.Thickenings.IsThickening (adicThickeningSucc A I n) :=
    ⟨inferInstance, (adicThickeningSucc A I n).surjective⟩
  obtain ⟨-, m, hm⟩ :=
    Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing h
      (isNoetherianRing_of_ringEquiv _
        (Scheme.ΓSpecIso (.of (A ⧸ I ^ (n + 1 + 1)))).commRingCatIsoToRingEquiv.symm)
  exact ⟨m, isNthOrderThickening_range_yoneda_map B _ hS m _
    ⟨inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion (adicThickeningSucc A I n)), hm⟩⟩

section Tower

variable [IsNoetherianRing A]
  (X : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
  (hX : ∀ n, IsAlgebraicSpace B (Spec (.of A)) hS (X n))
  (p : ∀ n, X n ⟶ yoneda.obj (adicThickeningObject A I B hS hSn n))
  (i : ∀ n, X n ⟶ X (n + 1))
  (hcart : ∀ n, IsPullback (i n) (p n) (p (n + 1))
    (yoneda.map (adicThickeningSuccMap A I B hS hSn n)))

include hX hcart in
/-- Each member of the tower is a finite-order thickening of the next: `Xₙ` is identified with
the inverse image of the finite-order thickening `Sₙ ⊆ Sₙ₊₁` in `Xₙ₊₁`, and under this
identification `pₙ` is the induced map onto `Sₙ`. -/
theorem exists_adicTower_thickening_iso (n : ℕ) :
    ∃ (G : Subfunctor (X (n + 1))) (_ : IsFiniteOrderThickening B _ hS ⟨X (n + 1), hX (n + 1)⟩ G)
      (Y : Subfunctor (yoneda.obj (adicThickeningObject A I B hS hSn (n + 1))))
      (_ : IsFiniteOrderThickening B _ hS
        ((schemeSpaceFunctor B (Spec (.of A)) hS).obj (adicThickeningObject A I B hS hSn (n + 1)))
        Y)
      (e : X n ≅ G.toFunctor) (r : yoneda.obj (adicThickeningObject A I B hS hSn n) ≅ Y.toFunctor)
      (g : G.toFunctor ⟶ Y.toFunctor),
      IsPullback g G.ι Y.ι (p (n + 1)) ∧ e.hom ≫ g = p n ≫ r.hom := by
  let Y' := (schemeSpaceFunctor B (Spec (.of A)) hS).obj (adicThickeningObject A I B hS hSn (n + 1))
  let Y : Subfunctor (yoneda.obj (adicThickeningObject A I B hS hSn (n + 1))) :=
    Subfunctor.range (yoneda.map (adicThickeningSuccMap A I B hS hSn n))
  let X' : AlgebraicSpaces B (Spec (.of A)) hS := ⟨X (n + 1), hX (n + 1)⟩
  let f : X' ⟶ Y' := ObjectProperty.homMk (p (n + 1))
  have hYfin : IsFiniteOrderThickening B _ hS Y' Y :=
    isFiniteOrderThickening_range_adicThickeningSuccMap A I B hS hSn n
  have hXfin := isFiniteOrderThickening_preimage B _ hS Y f hYfin
  have hmono0 : Mono (adicThickeningSuccMap A I B hS hSn n) :=
    (BigFppfOver.toScheme B (Spec (.of A)) hS).mono_of_mono_map
      (inferInstanceAs (Mono (adicThickeningSucc A I n)))
  let r := Subfunctor.toRange (yoneda.map (adicThickeningSuccMap A I B hS hSn n))
  have hr : r ≫ Y.ι = yoneda.map (adicThickeningSuccMap A I B hS hSn n) :=
    Subfunctor.toRange_ι _
  have hpb : IsPullback (i n) (p n ≫ r) (p (n + 1)) Y.ι :=
    IsPullback.of_iso (hcart n) (Iso.refl _) (Iso.refl _) (asIso r) (Iso.refl _) (by simp)
      (by simp) (by simp) (by simp [hr])
  let e := hpb.flip.isoIsPullback _ _ (Subfunctor.isPullback_preimage (p (n + 1)) Y)
  exact ⟨Y.preimage (p (n + 1)), hXfin, Y, hYfin, e, asIso r, Y.fromPreimage (p (n + 1)),
    Subfunctor.isPullback_preimage (p (n + 1)) Y, hpb.flip.isoIsPullback_hom_fst _ _ _⟩

include hX hcart in
/-- If one member of the tower is proper over its thickening then so is the next. -/
theorem isProper_adicTower_succ (n : ℕ) (hn : IsProper B (Spec (.of A)) hS (p n)) :
    IsProper B (Spec (.of A)) hS (p (n + 1)) := by
  obtain ⟨G, hG, Y, hY, e, r, g, hpb, he⟩ :=
    exists_adicTower_thickening_iso A I B hS hSn X hX p i hcart n
  let M : CartesianFiniteOrderMorphismOfThickenings B (Spec (.of A)) hS :=
    { X' := ⟨X (n + 1), hX (n + 1)⟩
      Y' := (schemeSpaceFunctor B (Spec (.of A)) hS).obj
        (adicThickeningObject A I B hS hSn (n + 1))
      X := G
      Y := Y
      sourceThickening := hG.choose_spec.1
      targetFiniteOrder := hY
      morphism := Arrow.homMk g (p (n + 1)) hpb.w
      cartesian := hpb }
  refine (M.isProper_iff).1 ?_
  have hf : M.f = e.inv ≫ p n ≫ r.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
    rfl
  have hYalg : IsAlgebraicSpace B _ hS Y.toFunctor := hY.choose_spec.1.1.1
  rw [hf]
  exact isProper_comp' B _ hS _ _ (hX n) hYalg (isProper_of_isIso B _ hS e.inv)
    (isProper_comp' B _ hS _ _ (isAlgebraicSpace_yoneda B _ hS _) hYalg hn
      (isProper_of_isIso B _ hS r.hom))

include hX hcart in
/-- Every member of the tower is proper over its thickening once the first one is. -/
theorem isProper_adicTower (h₀ : IsProper B (Spec (.of A)) hS (p 0)) (n : ℕ) :
    IsProper B (Spec (.of A)) hS (p n) := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact isProper_adicTower_succ A I B hS hSn X hX p i hcart n ih

include hX hcart in
/-- Every member of the tower is a separated algebraic space, once the first one is proper over
its thickening. -/
theorem isAbsolutelySeparated_adicTower (h₀ : IsProper B (Spec (.of A)) hS (p 0)) (n : ℕ) :
    IsAbsolutelySeparated B (Spec (.of A)) hS B.contains_terminal (X n) :=
  isAbsolutelySeparated_of_isSeparated_to_affine B _ hS B.contains_terminal
    (adicThickeningObject A I B hS hSn n)
    (inferInstanceAs (IsAffine (adicThickening A I n))) (p n)
    (isProper_adicTower A I B hS hSn X hX p i hcart h₀ n).1

include hX hcart in
/-- Every member of the tower is locally Noetherian, once the first one is proper over its
thickening. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_adicTower
    (h₀ : IsProper B (Spec (.of A)) hS (p 0)) (n : ℕ) :
    HasEtaleLocalProperty B (Spec (.of A)) hS (X n)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B _ hS (hX n)
    (isAlgebraicSpace_yoneda B _ hS _) (p n)
    (isProper_adicTower A I B hS hSn X hX p i hcart h₀ n).2.1.1
    (hasEtaleLocalProperty_of_representable B _ hS _ _ (adicThickeningObject A I B hS hSn n)
      (Iso.refl _) (inferInstanceAs (IsLocallyNoetherian (adicThickening A I n))))

attribute [local instance] pointTopology in
include hX hcart in
/-- All members of the tower have the same dimension, once the first one is proper over its
thickening. -/
theorem dimension_adicTower_eq (h₀ : IsProper B (Spec (.of A)) hS (p 0)) (n : ℕ) :
    dimension B (Spec (.of A)) hS (X n) (hX n) = dimension B (Spec (.of A)) hS (X 0) (hX 0) := by
  have hdec : ∀ m, IsDecentSpace B _ hS (X m) := fun m ↦
    isDecentSpace_of_isAbsolutelyQuasiSeparated B _ hS (X m) (hX m)
      (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B _ hS B.contains_terminal (X m)
        (isAbsolutelySeparated_adicTower A I B hS hSn X hX p i hcart h₀ m))
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, ← topologicalKrullDim_points_eq_dimension_of_isDecentSpace B _ hS (hX n) (hdec n),
      ← topologicalKrullDim_points_eq_dimension_of_isDecentSpace B _ hS (hX (n + 1))
        (hdec (n + 1))]
    obtain ⟨G, hG, -, -, e, -⟩ := exists_adicTower_thickening_iso A I B hS hSn X hX p i hcart n
    rw [← IsHomeomorph.topologicalKrullDim_eq _
        (isHomeomorph_pointsMap_ι_of_isThickening B _ hS hG.choose_spec.1),
      ← IsHomeomorph.topologicalKrullDim_eq _ (pointsHomeomorphOfIso B _ hS e).isHomeomorph]

attribute [local instance] pointTopology in
include hX hcart in
/-- The local rings of every member of the tower have dimension at most one, when the first
member is proper over its thickening and of dimension at most one. -/
theorem localRingDimension_le_one_adicTower (h₀ : IsProper B (Spec (.of A)) hS (p 0))
    (hdim : dimension B (Spec (.of A)) hS (X 0) (hX 0) ≤ 1) (n : ℕ)
    (x : points B (Spec (.of A)) hS (X n)) :
    localRingDimension B (Spec (.of A)) hS x ≤ 1 := by
  exact_mod_cast (le_iSup (fun y : points B (Spec (.of A)) hS (X n) ↦
    (localRingDimension B (Spec (.of A)) hS y : WithBot ℕ∞)) x).trans
    ((dimension_eq_iSup_localRingDimension B _ hS (X n) (hX n)).symm.le.trans
      ((dimension_adicTower_eq A I B hS hSn X hX p i hcart h₀ n).le.trans hdim))

end Tower

/-- An algebraic space each of whose points lies in a representable open subspace is
representable. -/
theorem isRepresentable_of_forall_mem_range {F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of A)) hS F)
    (h : ∀ x : points B (Spec (.of A)) hS F, ∃ G : Subfunctor F,
      IsOpenSubspace B (Spec (.of A)) hS G ∧ G.toFunctor.IsRepresentable ∧
        x ∈ Set.range (pointsMap B (Spec (.of A)) hS G.toFunctor G.ι)) :
    F.IsRepresentable :=
  isRepresentable_of_surjective_pointsMap_schematicLocus B _ hS hF fun x ↦
    (mem_range_pointsMap_schematicLocus_iff B _ hS F x).2 (h x)

end AlgebraicGeometry.Space

end
