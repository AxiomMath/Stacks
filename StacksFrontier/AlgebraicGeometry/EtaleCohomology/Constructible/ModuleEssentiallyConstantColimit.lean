module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EssentiallyConstantColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration

/-!
# Essentially constant colimits of constructible sheaves of modules

Let `X` be a quasi-compact quasi-separated scheme of a big étale site, let `Λ` be a Noetherian
ring and let `F = colim_{i ∈ I} F_i` be a filtered colimit of sheaves of `Λ`-modules on
`X_étale`. If `F` and all the `F_i` are constructible, then the ind-object `F_i` is essentially
constant with value `F`.

## Main results

* `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit`:
  a filtered system of constructible sheaves of modules with constructible colimit is essentially
  constant with value its colimit.

## References

* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' v u

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Let `X` be a quasi-compact quasi-separated scheme, let `Λ` be a
Noetherian ring, and let `F = colim_{i ∈ I} F_i` be a filtered colimit of sheaves of `Λ`-modules
on `X_étale`. If `F` and all the `F_i` are constructible, then the ind-object `F_i` is essentially
constant with value `F`. -/
@[stacks 095P "part (3), with 095N discharged"]
public theorem exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit
    (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleModuleSheaf B X R (F.obj i))
    (hcolim : IsConstructibleModuleSheaf B X R t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r :=
  isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit B X R
    (fun G => (isConstructibleModuleSheaf_iff_qcqsShriekPresentation B X R G).1) F t ht hF hcolim

end AlgebraicGeometry

end
