module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Fibers
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.SpreadOutPreliminaries
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Schemes unramified over a field, by geometric reducedness

Let `k` be a field and `f : X ⟶ Spec k` locally of finite type. Then `f` is unramified exactly
when it is locally quasi-finite and geometrically reduced. This is the scheme case of the step
in the proof of Stacks 0DSW that identifies its conditions (3)(b) and (3)(c): an algebraic space
locally of finite type over `k` is unramified over `k` if and only if it is geometrically reduced
and of dimension zero.

## Main results

* `AlgebraicGeometry.geometricallyReduced_of_unramified_over_field`: a scheme unramified over a
  field is geometrically reduced over it.
* `AlgebraicGeometry.unramified_of_locallyQuasiFinite_of_geometricallyReduced`: a scheme locally
  quasi-finite and geometrically reduced over a field is unramified over it.
* `AlgebraicGeometry.unramified_iff_locallyQuasiFinite_and_geometricallyReduced`: the
  equivalence, for a scheme locally of finite type over a field.

## Implementation notes

The hard direction is the source's argument: an affine open `U` of `X` is quasi-compact and
locally quasi-finite over the Artinian scheme `Spec k`, hence finite and so proper over `k`, and
the global sections of a geometrically reduced proper scheme over `k` form an étale `k`-algebra
by Stacks 0BUG (`AlgebraicGeometry.etale_globalSections_of_geometricallyReduced`). So `U` is
étale over `k`, and formal unramifiedness is local on the source. The easy direction is that a
base change of an unramified scheme over `k` to a field `K` is unramified over `K`, hence a
coproduct of spectra of fields by Stacks 02G7, hence reduced; unramified morphisms are moreover
locally quasi-finite.

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 02G7](https://stacks.math.columbia.edu/tag/02G7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme unramified over a field `k` is geometrically reduced over `k`: its base change to
any field `K` is unramified over `K`, hence by Stacks 02G7 a coproduct of spectra of fields. -/
@[sga "3 XI 1.3" "(i)(a)⇒(d)"]
theorem geometricallyReduced_of_unramified_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Unramified f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  obtain ⟨I, L, hL, _, _, _, e, _⟩ :=
    (unramified_iff_iso_coproduct_spectra_finite_separable K snd).mp
      (unramified_isStableUnderBaseChange.of_isPullback h inferInstance)
  have hsum : IsReduced (∐ fun i : I => Spec (.of (L i))) := by
    let 𝒰 := sigmaOpenCover (fun i : I => Spec (.of (L i)))
    have hcomp : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
      intro i
      let : Field (L i) := hL i
      show IsReduced (Spec (.of (L i)))
      infer_instance
    exact IsReduced.of_openCover _ 𝒰
  exact isReduced_of_isOpenImmersion e.hom

/-- An affine scheme which is finite and geometrically reduced over a field `k` is étale over
`k`: its ring of global sections is an étale `k`-algebra by Stacks 0BUG. -/
@[ega "IV 17.15.11" "c ⇒ a"]
theorem etale_of_isAffine_of_isFinite_of_geometricallyReduced (k : Type u) [Field k]
    {U : Scheme.{u}} [IsAffine U] (g : U ⟶ Spec (.of k)) [IsFinite g]
    [GeometricallyReduced g] : Etale g := by
  obtain ⟨het, -⟩ :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced k g
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  have hφ : ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.Etale := het
  have he : (Scheme.ΓSpecIso (.of k)).hom.hom.Etale :=
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)
  convert RingHom.Etale.stableUnderComposition _ _ he hφ using 1
  rw [← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]

/-- A scheme locally quasi-finite and geometrically reduced over a field `k`, and locally of
finite type over it, is unramified over `k`. -/
@[sga "3 XI 1.3" "(i)(d)⇒(a)"]
theorem unramified_of_locallyQuasiFinite_of_geometricallyReduced (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [GeometricallyReduced f] : Unramified f := by
  refine (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr ⟨inferInstance, ?_⟩
  let : IsZariskiLocalAtSource (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @FormallyUnramified) (Q := @RingHom.FormallyUnramified)
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @FormallyUnramified)
    (fun U : X.affineOpens ↦ (U : X.Opens)) (iSup_affineOpens_eq_top X)).mpr fun U ↦ ?_
  have : IsAffine (U : X.Opens).toScheme := U.2
  have : GeometricallyReduced ((U : X.Opens).ι ≫ f) :=
    ConnectedComponentSection.geometricallyReduced_comp_opens f U
  have : IsFinite ((U : X.Opens).ι ≫ f) := IsFinite.of_locallyQuasiFinite _
  have : Etale ((U : X.Opens).ι ≫ f) :=
    etale_of_isAffine_of_isFinite_of_geometricallyReduced k _
  infer_instance

/-- A scheme locally of finite type over a field `k` is unramified over `k` exactly when it is
locally quasi-finite and geometrically reduced over `k`. -/
@[ega "IV 17.4.3" "special case", sga "3 XI 1.3" "(i)(a)⇔(d), special case"]
theorem unramified_iff_locallyQuasiFinite_and_geometricallyReduced (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Unramified f ↔ LocallyQuasiFinite f ∧ GeometricallyReduced f :=
  ⟨fun _ ↦ ⟨inferInstance, geometricallyReduced_of_unramified_over_field k f⟩,
    fun ⟨_, _⟩ ↦ unramified_of_locallyQuasiFinite_of_geometricallyReduced k f⟩

end AlgebraicGeometry
