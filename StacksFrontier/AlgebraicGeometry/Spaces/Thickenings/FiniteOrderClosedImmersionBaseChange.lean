module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingAffineSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# Closed immersions detected on a finite-order thickening of the target

Let `Y ⊆ Y'` be a finite-order thickening of algebraic spaces and `f : X' ⟶ Y'` a morphism of
algebraic spaces whose base change `X' ×_{Y'} Y ⟶ Y` is a closed immersion.  Then `f` is a closed
immersion.  This is the case of Stacks 08B2 in which the closed immersion `Y ⟶ Y'`, bijective on
points, is a finite-order thickening; it is part (1) of Stacks 09ZZ read in the direction from
the thickening to the ambient space
(`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isClosedImmersion_iff`), with
the source thickening `X' ×_{Y'} Y ⊆ X'` produced by base change (Stacks 09ZX).

The library's Stacks 08B2, `AlgebraicGeometry.Space.isClosedImmersion_of_infinitesimal_baseChange`,
cannot be used in its place: it carries, as the hypothesis `h07SQ`, Stacks 07SQ for every descent
situation over every index type of the site's universe, with no bound on the index, which the
library's own Stacks 07SQ
(`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`) records as false in
this size model.

The application is to the adic fibres `X_n = X ×_S Spec(A / I^{n+1})` of an algebraic space over
`S = Spec A`: `X_n ⊆ X_{n+1}` is a first-order thickening, so a morphism `Z_{n+1} ⟶ X_{n+1}` whose
base change to `X_n` is a closed immersion is itself one
(`AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_adicFibreSucc`), and by induction a
cartesian tower over the adic fibres is a tower of closed immersions as soon as its first member
is (`AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_adicFibreSucc_tower`).

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_of_isFiniteOrderThickening`.
* `AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_adicFibreSucc` and
  `AlgebraicGeometry.Space.isClosedImmersion_of_isPullback_adicFibreSucc_tower`.

## References

* [Stacks Project, Tag 08B2](https://stacks.math.columbia.edu/tag/08B2)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of algebraic spaces whose base change to a finite-order thickening of its
target is a closed immersion is a closed immersion.**  Here the thickening is a subfunctor
`G ⊆ Y'` of finite order, reached from `Y` through an isomorphism `e`, and the square
`X ⟶ X'` over `Y ⟶ Y'` is cartesian.  This is the case of Stacks 08B2 for a finite-order
thickening, deduced from part (1) of Stacks 09ZZ. -/
theorem isClosedImmersion_of_isPullback_of_isFiniteOrderThickening {Y' X' : AlgebraicSpaces B S hS}
    (G : Subfunctor Y'.1) (hG : IsFiniteOrderThickening B S hS Y' G)
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Y ≅ G.toFunctor) (t : X ⟶ X'.1) (j : X ⟶ Y)
    (f : X' ⟶ Y') (sq : IsPullback t j f.hom (e.hom ≫ G.ι)) (hj : IsClosedImmersion B S hS j) :
    IsClosedImmersion B S hS f.hom := by
  let M : CartesianFiniteOrderMorphismOfThickenings B S hS :=
    { X' := X'
      Y' := Y'
      X := G.preimage f.hom
      Y := G
      sourceThickening := isThickening_preimage B S hS G f hG.choose_spec.1
      targetFiniteOrder := hG
      morphism := Arrow.homMk (G.fromPreimage f.hom) f.hom (Subfunctor.fromPreimage_ι G f.hom)
      cartesian := Subfunctor.isPullback_fromPreimage G f.hom }
  have sq' : IsPullback (j ≫ e.hom) t G.ι f.hom := by
    refine IsPullback.of_iso sq.flip (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hM : IsClosedImmersion B S hS (G.fromPreimage f.hom) := by
    rw [(Iso.eq_inv_comp _).2
      (sq'.isoIsPullback_hom_fst _ _ (Subfunctor.isPullback_fromPreimage G f.hom))]
    exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
      (isClosedImmersion_comp B S hS _ _ hj (isClosedImmersion_of_isIso B S hS _))
  exact M.isClosedImmersion_iff.1 hM

end General

section AdicFibre

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- The adic fibre `X_n` is the base change of `X_{n+1}` along `Spec(A / I^{n+1}) ⟶
Spec(A / I^{n+2})`. -/
theorem isPullback_adicFibreSucc_adicThickeningSuccMap
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    IsPullback (adicFibreSucc A I B hS hSn fX n)
      (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))))
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n)) := by
  refine IsPullback.of_right ?_ (adicFibreSucc_snd A I B hS hSn fX n)
    (IsPullback.of_hasPullback fX (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))))
  rw [adicFibreSucc_fst, ← yoneda.map_comp, adicThickeningSuccMap_adicThickeningMap]
  exact IsPullback.of_hasPullback fX _

/-- **A morphism into `X_{n+1}` whose base change to `X_n` is a closed immersion is a closed
immersion**, for the adic fibres `X_n = X ×_S Spec(A / I^{n+1})` of a presheaf `X` over
`S = Spec A`: `X_n ⊆ X_{n+1}` is a first-order thickening. -/
theorem isClosedImmersion_of_isPullback_adicFibreSucc
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) {Z Z' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hZ' : IsAlgebraicSpace B (Spec (.of A)) hS Z')
    (j : Z ⟶ adicFibre A I B hS hSn fX n) (j' : Z' ⟶ adicFibre A I B hS hSn fX (n + 1))
    (t : Z ⟶ Z') (h : IsPullback t j j' (adicFibreSucc A I B hS hSn fX n))
    (hj : IsClosedImmersion B (Spec (.of A)) hS j) :
    IsClosedImmersion B (Spec (.of A)) hS j' := by
  let T' := adicThickeningObject A I B hS hSn (n + 1)
  let ι0 := adicThickeningSuccMap A I B hS hSn n
  have hι0 : Stacks.Thickenings.IsNthOrderThickening 1
      ((BigFppfOver.toScheme B (Spec (.of A)) hS).map ι0) :=
    AlgebraicGeometry.isFirstOrderThickening_adicThickeningSucc A I n
  have : Mono (yoneda.map ι0) := mono_yoneda_map_of_isClosedImmersion ι0 hι0.1
  let G0 : Subfunctor ((schemeSpaceFunctor B (Spec (.of A)) hS).obj T').1 :=
    Subfunctor.range (yoneda.map ι0)
  let Y' : AlgebraicSpaces B (Spec (.of A)) hS :=
    ⟨adicFibre A I B hS hSn fX (n + 1), isAlgebraicSpace_adicFibre A I B hS hSn hX fX (n + 1)⟩
  let q : Y' ⟶ (schemeSpaceFunctor B (Spec (.of A)) hS).obj T' :=
    ObjectProperty.homMk (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))))
  let G : Subfunctor Y'.1 := G0.preimage q.hom
  have hG : IsFiniteOrderThickening B (Spec (.of A)) hS Y' G :=
    ⟨1, isNthOrderThickening_preimage B (Spec (.of A)) hS G0 q
      (isNthOrderThickening_range_yoneda_map B (Spec (.of A)) hS 1 ι0 hι0)⟩
  let r := rangeIsoOfMono B (Spec (.of A)) hS (yoneda.map ι0)
  have sq1 : IsPullback (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ r.hom)
      (adicFibreSucc A I B hS hSn fX n) G0.ι q.hom :=
    IsPullback.of_iso (isPullback_adicFibreSucc_adicThickeningSuccMap A I B hS hSn fX n).flip
      (Iso.refl _) r (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      ((Category.comp_id _).trans (rangeIsoOfMono_hom_ι B (Spec (.of A)) hS (yoneda.map ι0)).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let e := sq1.isoIsPullback _ _ (Subfunctor.isPullback_fromPreimage G0 q.hom)
  have he : e.hom ≫ G.ι = adicFibreSucc A I B hS hSn fX n :=
    sq1.isoIsPullback_hom_snd _ _ (Subfunctor.isPullback_fromPreimage G0 q.hom)
  exact isClosedImmersion_of_isPullback_of_isFiniteOrderThickening B (Spec (.of A)) hS
    (X' := ⟨Z', hZ'⟩) G hG e t j (ObjectProperty.homMk j') (by rwa [he]) hj

/-- **A cartesian tower over the adic fibres is a tower of closed immersions as soon as its
first member is a closed immersion.** -/
theorem isClosedImmersion_of_isPullback_adicFibreSucc_tower
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (Z : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
    (hZ : ∀ n, IsAlgebraicSpace B (Spec (.of A)) hS (Z n))
    (j : ∀ n, Z n ⟶ adicFibre A I B hS hSn fX n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicFibreSucc A I B hS hSn fX n))
    (hj : IsClosedImmersion B (Spec (.of A)) hS (j 0)) (n : ℕ) :
    IsClosedImmersion B (Spec (.of A)) hS (j n) := by
  induction n with
  | zero => exact hj
  | succ n ih =>
    exact isClosedImmersion_of_isPullback_adicFibreSucc A I B hS hSn hX fX n (hZ (n + 1))
      (j n) (j (n + 1)) (t n) (hcart n) ih

end AdicFibre

end AlgebraicGeometry.Space

end
