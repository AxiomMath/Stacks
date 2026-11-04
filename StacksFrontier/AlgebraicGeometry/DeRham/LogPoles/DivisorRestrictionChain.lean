module

public import StacksFrontier.AlgebraicGeometry.DeRham.BasePushforwardRelativeBase
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorDeRhamPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogPolesRestrictionMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.PushforwardModuleRefinement

/-!
# The restriction of forms to a divisor is the canonical map of de Rham complexes

Let `f : X ⟶ S` be a morphism of schemes and `i : Y ⟶ X` the closed immersion of an effective
Cartier divisor. There are two maps `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` of `ℤ`-indexed complexes of
`f^{-1}𝒪_S`-modules: the restriction of forms of the proof of [Stacks, Tag 0FUQ]
(`AlgebraicGeometry.Scheme.Hom.divisorRestrictionInt` followed by the identification
`Stacks.LineBundle.divisorDeRhamIntHom`), with values in the direct image over the base rings
`AlgebraicGeometry.Scheme.Hom.basePushforward`, and the canonical map of Section 07HX,
`Stacks.DeRham.BlowupTriangle.chain`, with values in the pushforward of modules along
`Stacks.DeRhamSmooth.relativeBase`. The two direct images are equal
(`AlgebraicGeometry.Scheme.Hom.basePushforward_eq_modulePushforward`), and the two maps agree
across that equality.

## Main results

* `HomologicalComplex.mapHomologicalComplexExtendIso_eq_mapExtendIso`: the two comparisons of
  extension by zero with a functor applied degreewise agree.
* `Stacks.LineBundle.divisorRestriction_heq_chain`: the restriction of forms is the canonical map.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasZeroObject A] [HasZeroObject B] (F : A ⥤ B) [F.Additive]

/-- **The two comparisons of extension by zero with a functor applied degreewise agree**:
`HomologicalComplex.mapHomologicalComplexExtendIso` and `Stacks.DerivedIndexing.mapExtendIso` are
the same isomorphism. -/
theorem mapHomologicalComplexExtendIso_eq_mapExtendIso (K : HomologicalComplex A c)
    (e : c.Embedding c') :
    mapHomologicalComplexExtendIso F K e = Stacks.DerivedIndexing.mapExtendIso F e K := by
  refine Iso.ext (Hom.ext (funext fun i' ↦ ?_))
  change (extendMapXIso F K (e.r i')).hom = (Stacks.DerivedIndexing.mapExtendXIso F K (e.r i')).hom
  rcases h : e.r i' with _ | a
  · exact (F.map_isZero (extend.isZero_X K rfl)).eq_of_tgt _ _
  · rfl

end HomologicalComplex

namespace Stacks.LineBundle

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]

/-- In each degree the restriction of forms of [Stacks, Tag 0FUQ], followed by the identification
of `i_*Ω^p_{Y/S}` with the direct image over the base rings, has the same sections as the
canonical map of Section 07HX. -/
theorem divisorRestrictionBase_comp_divisorDeRhamBaseHom_val_app (n : ℕ)
    (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (x : ((Scheme.Hom.deRhamComplex f).X n).val.obj U) :
    (((Scheme.Hom.divisorRestrictionBase f I ≫ divisorDeRhamBaseHom f I).f n).val.app U).hom x =
      (((Stacks.DeRhamPullback.deRhamPushforwardChain I.subschemeι f).f n).val.app U).hom x := by
  have hab := (Scheme.Hom.toSheaf_divisorRestrictionBase_comp_divisorDeRhamAbIso f I).trans
    (Stacks.DeRhamPullback.deRhamAbelianPushforwardMap_eq_toSheaf_map I.subschemeι f (by simp))
  exact congrArg (fun φ ↦ ((φ.f n).hom.app U).hom x) hab

/-- **The restriction of forms is the canonical map of de Rham complexes**: the restriction of
forms `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` of [Stacks, Tag 0FUQ], with values in the direct image over the
base rings, and the canonical map of Section 07HX, with values in the pushforward along
`relativeBase`, agree across the equality of the two direct images. -/
theorem divisorRestriction_heq_chain :
    HEq (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I)
      (Stacks.DeRham.BlowupTriangle.chain I.subschemeι f) := by
  have hJ := Scheme.Hom.basePushforward_eq_modulePushforward I.subschemeι f
  have key : ∀ (J : SheafOfModules.{u} (Scheme.Hom.baseRingSheaf (I.subschemeι ≫ f)) ⥤
        SheafOfModules.{u} (Scheme.Hom.baseRingSheaf f)) [J.Additive]
      (hJ : J = RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.DeRhamSmooth.relativeBase I.subschemeι f))
      (φ : Scheme.Hom.deRhamComplex f ⟶
        (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)))
      (hφ : ∀ n U x, HEq (((φ.f n).val.app U).hom x)
        ((((Stacks.DeRhamPullback.deRhamPushforwardChain I.subschemeι f).f n).val.app U).hom x)),
      HEq (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.mapHomologicalComplexExtendIso J
            (Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)) ComplexShape.embeddingUpNat).hom)
        (Stacks.DeRham.BlowupTriangle.chain I.subschemeι f) := by
    intro J _ hJ φ hφ
    subst hJ
    have : φ = Stacks.DeRhamPullback.deRhamPushforwardChain I.subschemeι f :=
      HomologicalComplex.hom_ext _ _ fun n ↦
        SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
          ModuleCat.hom_ext (LinearMap.ext fun x ↦ eq_of_heq (hφ n U x)))
    subst this
    refine heq_of_eq ?_
    unfold Stacks.DeRham.BlowupTriangle.chain
    exact congrArg (HomologicalComplex.extendMap
        (Stacks.DeRhamPullback.deRhamPushforwardChain I.subschemeι f)
        ComplexShape.embeddingUpNat ≫ ·)
      (congrArg Iso.hom (HomologicalComplex.mapHomologicalComplexExtendIso_eq_mapExtendIso _ _ _))
  have := key _ hJ _ (fun n U x ↦
    heq_of_eq (divisorRestrictionBase_comp_divisorDeRhamBaseHom_val_app f I n U x))
  refine HEq.trans (heq_of_eq ?_) this
  simp only [Scheme.Hom.divisorRestrictionInt, divisorDeRhamIntHom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (HomologicalComplex.extendMap_comp _ _ _).symm)

end Stacks.LineBundle

end
