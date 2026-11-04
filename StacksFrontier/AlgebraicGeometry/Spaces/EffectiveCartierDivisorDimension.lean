module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# An effective Cartier divisor drops the dimension of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `D ⊆ X` be an effective Cartier
divisor.  At a point `x ∈ |D|` at which the dimension of `X` is finite, the dimension of `D` is
strictly smaller than the dimension of `X`.  This is Stacks 083T.

## Main results

* `AlgebraicGeometry.Space.dimensionAtPoint_lt_of_isEffectiveCartierDivisor`: **Stacks 083T.**
  At a point of an effective Cartier divisor `D ⊆ X`, the dimension of `D` is strictly below the
  finite dimension of `X`.
* `AlgebraicGeometry.Space.dimensionAtPoint_closedSubspace_lt`: the same inequality under the
  weaker hypothesis that the inverse image of the closed subspace is an effective Cartier
  divisor on every étale scheme chart, which is condition (3) of Stacks 083C.

## Implementation notes

Finiteness of the ambient dimension is stated as `dimensionAtPoint … < ⊤`, the dimension at a
point taking values in `WithBot ℕ∞`.

## References

* [Stacks Project, Tag 083T](https://stacks.math.columbia.edu/tag/083T)
* [Stacks Project, Tag 056N](https://stacks.math.columbia.edu/tag/056N)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- If the inverse image of a subfunctor `D ⊆ F` along a morphism `g : h_U ⟶ F` from a
represented presheaf is the range of `h_j` for a monomorphism `h_j : h_R ⟶ h_U` of represented
presheaves, then `h_R` is the fibre product `D ×_F h_U`. -/
private theorem isPullback_yoneda_map_of_preimage_eq_range
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : Subfunctor F) {U R : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ F) (j : R ⟶ U) [Mono (yoneda.map j)]
    (hpre : D.preimage g = Subfunctor.range (yoneda.map j)) :
    ∃ a : yoneda.obj R ⟶ D.toFunctor, IsPullback (yoneda.map j) a g D.ι := by
  have hrange : Subfunctor.range (yoneda.map j) ≤ D.preimage g := hpre.ge
  let k : yoneda.obj R ⟶ (D.preimage g).toFunctor := Subfunctor.lift (yoneda.map j) hrange
  have hk : k ≫ (D.preimage g).ι = yoneda.map j := Subfunctor.lift_ι (yoneda.map j) hrange
  have hepi : Epi k := by
    rw [NatTrans.epi_iff_epi_app]
    intro t
    refine ConcreteCategory.epi_of_surjective _ fun z => ?_
    have hz : z.val ∈ (Subfunctor.range (yoneda.map j)).obj t := by
      rw [← hpre]; exact z.property
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, ?_⟩
    apply Subtype.ext
    show (yoneda.map j).app t w = z.val
    simpa using hw
  have hmono : Mono k := by
    refine ⟨fun {_} f₁ f₂ h => ?_⟩
    apply (cancel_mono (yoneda.map j)).1
    simpa only [Category.assoc, hk] using congrArg (fun φ => φ ≫ (D.preimage g).ι) h
  have : IsIso k := (isIso_iff_mono_and_epi k).2 ⟨hmono, hepi⟩
  have hiso : IsPullback (asIso k).hom (yoneda.map j) (D.preimage g).ι (𝟙 (yoneda.obj U)) :=
    IsPullback.of_horiz_isIso ⟨by rw [show (asIso k).hom = k from rfl, hk]; simp⟩
  exact ⟨(asIso k).hom ≫ D.fromPreimage g,
    by simpa using (hiso.paste_horiz (Subfunctor.isPullback_preimage g D)).flip⟩

/-- Let `D ⊆ X` be a closed subspace of an algebraic space `X` over `S` whose inverse image is
an effective Cartier divisor on every étale scheme chart of `X`.  At a point `x` of `|D|` at
which the dimension of `X` is finite, the dimension of `D` is strictly smaller than the
dimension of `X`. -/
theorem dimensionAtPoint_closedSubspace_lt (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : HasEffectiveCartierEtalePullbacks B S hS X D)
    (x : points B S hS D.1.toFunctor)
    (hfin : dimensionAtPoint B S hS X.1 X.2
      (pointsMap B S hS D.1.toFunctor D.1.ι x) < ⊤) :
    dimensionAtPoint B S hS D.1.toFunctor D.2.1 x <
      dimensionAtPoint B S hS X.1 X.2 (pointsMap B S hS D.1.toFunctor D.1.ι x) := by
  set T := BigFppfOver.toScheme B S hS with hT
  set y := pointsMap B S hS D.1.toFunctor D.1.ι x with hy
  obtain ⟨U, g, hgChart, p, hp⟩ := exists_etale_chart_at_point B S hS X.1 X.2 y
  obtain ⟨I, R, j, e, hI, hmap, hpre⟩ := hD U g (isEtale_of_presheaf_etale B S hS hgChart)
  have hmonoj : Mono j := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map j) := by
      rw [hT, hmap]; infer_instance
    exact Functor.mono_of_mono_map T inferInstance
  have : Mono (yoneda.map j) := Functor.map_mono yoneda j
  obtain ⟨a, hcart⟩ :=
    isPullback_yoneda_map_of_preimage_eq_range B S hS D.1 g j hpre
  obtain ⟨w, hwU, hwD⟩ := exists_point_of_isPullback_presheaf B S hS hcart
    (p.class B S hS (yoneda.obj U)) x hp
  obtain ⟨q, rfl⟩ := Quot.exists_rep w
  set qU := FieldValuedPoint.map B S hS (yoneda.obj R) (yoneda.map j) q with hqU
  have hqUclass : qU.class B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U) := hwU
  have hdimXU : dimensionAtPoint B S hS X.1 X.2 y =
      topologicalKrullDimAt (T.obj U) (schemePoint B S hS U qU) :=
    dimensionAtPoint_eq_of_etale_chart B S hS X.1 X.2 y U g hgChart qU
      (by rw [hqUclass]; exact hp)
  set yR := schemePoint B S hS R q with hyR
  set yI := e.hom yR with hyI
  have hpointI : I.subschemeι yI = schemePoint B S hS U qU := by
    rw [hyI, show I.subschemeι (e.hom yR) = (e.hom ≫ I.subschemeι) yR from rfl, ← hmap, hqU]
    exact (schemePoint_map_yoneda B S hS j q).symm
  have hdrop := topologicalKrullDimAt_subscheme_lt I hI yI
    (by rw [hpointI, ← hdimXU]; exact hfin)
  have hdimD : dimensionAtPoint B S hS D.1.toFunctor D.2.1 x =
      topologicalKrullDimAt (T.obj R) yR :=
    dimensionAtPoint_eq_of_etale_chart B S hS D.1.toFunctor D.2.1 x R a
      (presheaf_etale_of_isEtale B S hS
        (isEtale_of_isPullback_yoneda B S hS hcart
          (isEtale_of_presheaf_etale B S hS hgChart))) q hwD
  calc
    dimensionAtPoint B S hS D.1.toFunctor D.2.1 x
        = topologicalKrullDimAt (T.obj R) yR := hdimD
    _ = topologicalKrullDimAt I.subscheme yI :=
      topologicalKrullDimAt_eq_of_homeomorph e.hom.homeomorph yR
    _ < topologicalKrullDimAt (T.obj U) (I.subschemeι yI) := hdrop
    _ = dimensionAtPoint B S hS X.1 X.2 y := by rw [hpointI, ← hdimXU]

/-- Let `D ⊆ X` be an effective Cartier divisor on an algebraic space `X` over a scheme `S`, and
let `x` be a point of `|D|` at which the dimension of `X` is finite.  Then the dimension of `D`
at `x` is strictly smaller than the dimension of `X` at the image of `x`. -/
@[stacks 083T]
theorem dimensionAtPoint_lt_of_isEffectiveCartierDivisor (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D)
    (x : points B S hS D.1.toFunctor)
    (hfin : dimensionAtPoint B S hS X.1 X.2
      (pointsMap B S hS D.1.toFunctor D.1.ι x) < ⊤) :
    dimensionAtPoint B S hS D.1.toFunctor D.2.1 x <
      dimensionAtPoint B S hS X.1 X.2 (pointsMap B S hS D.1.toFunctor D.1.ι x) :=
  dimensionAtPoint_closedSubspace_lt B S hS X D
    (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D hD) x hfin

end AlgebraicGeometry.Space

end
