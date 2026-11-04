module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal

/-!
# Restriction to an open subspace preserves `m`-pseudo-coherence

Let `X` be a ringed space and let `W` be an open of `X`. This file proves that the restriction to
`W` of an `m`-pseudo-coherent complex of `𝒪_X`-modules is `m`-pseudo-coherent, and likewise for an
object of the derived category.

Since `m`-pseudo-coherence of `𝒦|_W` is tested on the open subspaces of `X|W`, an approximation
over an open `U` of `X` is read over a doubly restricted space `(X|U)|V`, through the inverse `Ψ`
of the comparison equivalence `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compareEquiv`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compareInverse` is the inverse `Ψ` of the
  comparison equivalence, `OXMod (X|W') ⥤ OXMod ((X|U)|V)`.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.inverseUnitIso` is `Ψ 𝒪_{X|W'} ≅ 𝒪_{(X|U)|V}`.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.restrictCompareInverseIso` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.restrictComplexCompareInverseIso` are the
  compatibility of `Ψ` with restriction, for modules and for complexes.

## Main results

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.isStrictlyPerfect_compareInverse`: `Ψ`
  carries strictly perfect complexes to strictly perfect complexes.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.exists_approximation_sub`: an approximation
  over `X|W'` read over the doubly restricted space `(X|U)|V`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_restrictComplex` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules`: restriction to an
  open subspace preserves `m`-pseudo-coherence.

## Implementation notes

The pair of corresponding opens is
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofBase`, not `ofSub`: here the open of `X` is
given — it is the intersection of the open `U` carrying the approximation with the open `W` being
restricted to — and the open of `X|W` is its preimage.

Every binder is written at the `StrictlyPerfect.OXMod` spelling of the category of `𝒪`-modules,
and the derived categories of `X` and of its open subspaces are hypotheses with independent
universes.

## References

* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- An exact functor carries an approximation to an approximation, up to an isomorphism. -/
private theorem homologyMap_map_comp_hom {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex C ℤ} {R : CochainComplex D ℤ} (α : P ⟶ Q)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ≅ R) (m : ℤ)
    (hα : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) j)) ∧
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) m) :=
  ⟨fun j hj => CategoryTheory.isIso_homologyMap_comp _ _ j
    (CategoryTheory.isIso_homologyMap_mapHomologicalComplex F α j (hα j hj))
    (CategoryTheory.isIso_homologyMap_of_iso _ j),
  CategoryTheory.epi_homologyMap_comp _ _ m
    (CategoryTheory.epi_homologyMap_mapHomologicalComplex F α m hα₀)
    (CategoryTheory.epi_homologyMap_of_iso _ m)⟩

namespace CorrespondingOpens

variable {U : Opens X.carrier} (D : CorrespondingOpens X U)

/-! ### The inverse of the comparison equivalence -/

/-- **The inverse `Ψ : OXMod (X|W) ⥤ OXMod ((X|U)|V)` of the comparison equivalence**
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.compareEquiv`. -/
public def compareInverse : OXMod.{u, u} (D.basespace) ⥤ OXMod.{u, u} (D.subspace) :=
  (D.compareEquiv).inverse

/-- `Ψ` is an equivalence, being the inverse of one. -/
public instance compareInverse_isEquivalence : (D.compareInverse).IsEquivalence :=
  inferInstanceAs ((D.compareEquiv).inverse.IsEquivalence)

/-- `Ψ` is additive, being the inverse of an additive equivalence. -/
public instance compareInverse_additive : (D.compareInverse).Additive :=
  haveI : (D.compareEquiv).functor.Additive := D.compare_additive
  inferInstanceAs ((D.compareEquiv).inverse.Additive)

/-- `Ψ` preserves finite limits, being an equivalence. -/
public instance compareInverse_preservesFiniteLimits :
    PreservesFiniteLimits (D.compareInverse) :=
  inferInstance

/-- `Ψ` preserves finite colimits, being an equivalence. -/
public instance compareInverse_preservesFiniteColimits :
    PreservesFiniteColimits (D.compareInverse) :=
  inferInstance

/-! ### `Ψ` takes the structure module to the structure module -/

/-- **`Ψ 𝒪_{X|W} ≅ 𝒪_{(X|U)|V}`**: the image under `Ψ` of the inverse of
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.unitIso`, followed by the inverse of the unit
of the equivalence at `𝒪_{(X|U)|V}`. -/
public def inverseUnitIso :
    (D.compareInverse).obj (structureModule (D.basespace)) ≅ structureModule (D.subspace) :=
  (D.compareInverse).mapIso (D.unitIso).symm ≪≫
    ((D.compareEquiv).unitIso.app (structureModule (D.subspace))).symm

/-! ### Strict perfection -/

/-- **`Ψ` preserves being a direct summand of a finite free module.** -/
public theorem isDirectSummandOfFiniteFree_compareInverse {A : OXMod.{u, u} (D.basespace)}
    (hA : IsDirectSummandOfFiniteFree A) :
    IsDirectSummandOfFiniteFree ((D.compareInverse).obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hA
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map (D.compareInverse)).trans
      (((D.compareInverse).retractMapBiproduct
          (fun _ : Fin n => structureModule (D.basespace))).trans
        (Retract.ofIso (biproduct.mapIso fun _ => D.inverseUnitIso)))⟩⟩

/-- **`Ψ` carries a strictly perfect complex of `𝒪_{X|W}`-modules to a strictly perfect complex of
`𝒪_{(X|U)|V}`-modules.** -/
public theorem isStrictlyPerfect_compareInverse
    {P : CochainComplex (OXMod.{u, u} (D.basespace)) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect
      (((D.compareInverse).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz => hi ((D.compareInverse).isZero_obj hz)
  directSummand i := D.isDirectSummandOfFiniteFree_compareInverse (hP.directSummand i)

/-! ### Compatibility of `Ψ` with restriction -/

/-- **`(·)|_W ⋙ Ψ ≅ (·)|_U ⋙ (·)|_V`**: restricting `𝒪_X`-modules to the open `W` of `X` and
comparing back along `Ψ` is restricting them to `U` and then to the open `V` of `X|U`.

This is `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso` with the comparison
moved to the other side of the isomorphism, using the unit of the equivalence. -/
public def restrictCompareInverseIso :
    restrictModules X D.base ⋙ D.compareInverse ≅
      restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) D.sub :=
  Functor.isoWhiskerRight (D.tripleRestrictIso).symm (D.compareInverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictModules X U)
      (Functor.associator (restrictModules (X.restrict U.isOpenEmbedding) D.sub) (D.compare)
        (D.compareInverse)) ≪≫
    Functor.isoWhiskerLeft (restrictModules X U) (Functor.isoWhiskerLeft
      (restrictModules (X.restrict U.isOpenEmbedding) D.sub) ((D.compareEquiv).unitIso).symm) ≪≫
    Functor.isoWhiskerLeft (restrictModules X U)
      (restrictModules (X.restrict U.isOpenEmbedding) D.sub).rightUnitor

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.restrictCompareInverseIso` on complexes:
applying `Ψ` degreewise to the restriction to `W` of a complex `𝒦` of `𝒪_X`-modules gives the
restriction to `V` of the restriction to `U` of `𝒦`. -/
public def restrictComplexCompareInverseIso (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    ((D.compareInverse).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex K D.base) ≅
      restrictComplex (restrictComplex K U) D.sub :=
  (Functor.mapHomologicalComplexCompIso (D.restrictCompareInverseIso)
      (ComplexShape.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) D.sub))
      (ComplexShape.up ℤ)).app K).symm

/-! ### Carrying an approximation into the doubly restricted space -/

/-- **An approximation over an open of `X` read over a doubly restricted space.** Let `𝒦` be a
complex of `𝒪_X`-modules and suppose that over the open `W` of `X` it receives a morphism from a
strictly perfect complex which is an isomorphism on cohomology above `m` and an epimorphism in
degree `m`. Then `(𝒦|_U)|_V` receives such a morphism from a strictly perfect complex of
`𝒪_{(X|U)|V}`-modules. -/
public theorem exists_approximation_sub (K : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    {P : CochainComplex (OXMod.{u, u} (D.basespace)) ℤ} (hP : IsStrictlyPerfect P)
    (α : P ⟶ restrictComplex K D.base)
    (hα : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P' : CochainComplex (OXMod.{u, u} (D.subspace)) ℤ, IsStrictlyPerfect P' ∧
      ∃ β : P' ⟶ restrictComplex (restrictComplex K U) D.sub,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) := by
  exact ⟨_, D.isStrictlyPerfect_compareInverse hP, _,
    homologyMap_map_comp_hom D.compareInverse α (D.restrictComplexCompareInverseIso K) m hα hα₀⟩

end CorrespondingOpens

/-! ### Restriction preserves `m`-pseudo-coherence -/

/-- **The restriction of an `m`-pseudo-coherent complex to an open subspace is
`m`-pseudo-coherent.** -/
public theorem isPseudoCoherentComplexFrom_restrictComplex
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ) (hK : IsPseudoCoherentComplexFrom K m)
    (W : Opens X.carrier) : IsPseudoCoherentComplexFrom (restrictComplex K W) m := by
  intro q
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := hK (show ↥W from q).1
  refine ⟨(CorrespondingOpens.ofBase (X := X) (U := W) (W := U ⊓ W) inf_le_right).sub,
    ((CorrespondingOpens.ofBase (X := X) (U := W) (W := U ⊓ W) inf_le_right).mem_sub_iff
      (show ↥W from q)).2 ⟨hxU, (show ↥W from q).2⟩, ?_⟩
  have h := homologyMap_map_comp_hom (restrictModulesOfLE X (inf_le_left : U ⊓ W ≤ U)) α
    (restrictComplexOfLEIso X (inf_le_left : U ⊓ W ≤ U) K) m hα hα₀
  exact CorrespondingOpens.exists_approximation_sub _ K m
    (isStrictlyPerfect_restrictModulesOfLE (inf_le_left : U ⊓ W ≤ U) hP) _ h.1 h.2

/-- **The derived restriction of an `m`-pseudo-coherent object to an open subspace is
`m`-pseudo-coherent.** -/
public theorem isPseudoCoherentFrom_derivedRestrictModules
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ V : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) (hE : IsPseudoCoherentFrom E m)
    (W : Opens X.carrier) :
    IsPseudoCoherentFrom ((derivedRestrictModules X W).obj E) m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨restrictComplex K W, isPseudoCoherentComplexFrom_restrictComplex K m hK W,
    ⟨(derivedRestrictModulesObjQIso X W K).symm ≪≫ (derivedRestrictModules X W).mapIso e⟩⟩

end AlgebraicGeometry.RingedSpace

end
