module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleSets
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject

/-!
# A filtered colimit of constructible étale sheaves is essentially constant

Let `X` be a quasi-compact quasi-separated scheme and let `F = colim_{i ∈ I} F_i` be a filtered
colimit of étale sheaves on `X`. If `F` and all the `F_i` are constructible — as sheaves of sets,
of abelian groups, or of modules over a Noetherian ring — then the ind-object `F_i` is essentially
constant with value `F`. This is Stacks 095P.

Essential constancy with value `F` is
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith`
(Stacks 05PU(1)): a stage `i` and a retraction `r : F ⟶ F_i` of the coprojection which is cofinal,
in the sense that out of every stage some transition map factors through `F`. Both clauses come
from compactness of the constructible sheaves involved, which is Stacks 09Z4: the identity of `F`
is a morphism into the colimit, so it factors through some `F_i`, giving `r`; and the two
morphisms `F_j ⟶ F ⟶ F_i` and `𝟙 F_j` have the same image in `F`, so they agree after a further
transition map, which is the cofinality clause.

The compactness statements of Stacks 09Z4 for sheaves of sets and of modules take the
presentation lemmas Stacks 09Y9 (sets) and Stacks 095N (modules) as named hypotheses, so the set
and module cases here take them too. They are helper lemmas: the unconditional parts (1) and (3) of
Stacks 095P apply them with those hypotheses supplied, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/SetEssentiallyConstantColimit.lean`
and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleEssentiallyConstantColimit`.
In the abelian case Stacks 095N for `ℤ`-modules is supplied here, by
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`.

## Main results

* `AlgebraicGeometry.isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit` — the case of
  sheaves of sets, with Stacks 09Y9 as a hypothesis.
* `AlgebraicGeometry.isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit` — **Stacks
  095P, part (2)**.
* `AlgebraicGeometry.isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit` — the case of
  sheaves of modules, with Stacks 095N as a hypothesis.

## Implementation notes

The colimit is given as a colimit cocone rather than existentially, so the conclusion names `F`
and its coprojections and is not merely the assertion that *some* value exists. The index category
is required to be essentially small at the coefficient universe of the small étale site, which is
where compactness is available; nothing else is assumed of it beyond being filtered.

`X` is quasi-compact and quasi-separated, not Noetherian. The Noetherian hypothesis in part (3) is
on the coefficient ring `Λ`, carried by `AlgebraicGeometry.IsConstructibleModuleSheaf`.

## References

* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v' v u

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A filtered colimit of finitely presentable objects with finitely presentable colimit is
essentially constant with value the colimit. -/
private theorem exists_isEssentiallyConstantWith_of_isFinitelyPresentable
    {C : Type*} [Category C] {I : Type v} [Category.{v'} I] [IsFiltered I]
    [EssentiallySmall.{u + 1} I] {F : I ⥤ C} {t : Cocone F} (ht : IsColimit t)
    (hcolim : IsFinitelyPresentable.{u + 1} t.pt)
    (hF : ∀ j, IsFinitelyPresentable.{u + 1} (F.obj j)) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  have : IsCardinalFiltered I Cardinal.aleph0.{u + 1} :=
    (isCardinalFiltered_aleph0_iff I).2 ‹IsFiltered I›
  obtain ⟨i, r, hr⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit (κ := Cardinal.aleph0.{u + 1}) ht (𝟙 t.pt)
  refine ⟨i, r, ⟨hr, fun j ↦ ?_⟩⟩
  have := hF j
  obtain ⟨k, τ, σ, hστ⟩ :=
    IsCardinalPresentable.exists_eq_of_isColimit (κ := Cardinal.aleph0.{u + 1}) ht
      (𝟙 (F.obj j)) (t.ι.app j ≫ r) (by simp [Category.assoc, hr])
  exact ⟨k, σ, τ, by simpa using hστ⟩

/-- Let `X` be a quasi-compact quasi-separated scheme on which every constructible sheaf of sets
admits a finite coequalizer presentation by sheaves represented by quasi-compact quasi-separated
étale objects (the hypothesis `h09Y9`), and let `F = colim_{i ∈ I} F_i` be a filtered colimit of
sheaves of sets on `X_étale`. If `F` and all the `F_i` are constructible, then the ind-object `F_i`
is essentially constant with value `F`.

This is a helper lemma. It is used by the unconditional
`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit` (Stacks
095P, part (1)) in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/SetEssentiallyConstantColimit.lean`,
which supplies `h09Y9` by Stacks 09Y9. -/
public theorem isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (h09Y9 : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X G → HasFiniteQCSRepresentableCoequalizerPresentation B X G)
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i))
    (hcolim : IsConstructibleSetSheaf B X t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  exact exists_isEssentiallyConstantWith_of_isFinitelyPresentable ht
    (isFinitelyPresentable_of_isConstructibleSetSheaf B X h09Y9 _ hcolim)
    fun j ↦ isFinitelyPresentable_of_isConstructibleSetSheaf B X h09Y9 _ (hF j)

/-- **Stacks 095P, part (2).** Let `X` be a quasi-compact quasi-separated scheme and let
`F = colim_{i ∈ I} F_i` be a filtered colimit of abelian sheaves on `X_étale`. If `F` and all the
`F_i` are constructible, then the ind-object `F_i` is essentially constant with value `F`.

Nothing beyond the instance hypotheses is assumed: the input of the sheaves-of-abelian-groups case
of Stacks 09Z4, Stacks 095N for `ℤ`-modules, is
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`. -/
@[stacks 095P "part (2), sheaves of abelian groups"]
public theorem isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleAbelianSheaf B X (F.obj i))
    (hcolim : IsConstructibleAbelianSheaf B X t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  have hpres := hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X
  exact exists_isEssentiallyConstantWith_of_isFinitelyPresentable ht
    (isFinitelyPresentable_of_isConstructibleAbelianSheaf B X hpres _ hcolim)
    fun j ↦ isFinitelyPresentable_of_isConstructibleAbelianSheaf B X hpres _ (hF j)

/-- Let `X` be a quasi-compact quasi-separated scheme and `Λ` a Noetherian ring such that every
constructible sheaf of `Λ`-modules on `X_étale` is the cokernel of a map between finite direct sums
of extensions by zero of constant free rank-one module sheaves at quasi-compact quasi-separated
étale objects (the hypothesis `h095N`), and let `F = colim_{i ∈ I} F_i` be a filtered colimit of
sheaves of `Λ`-modules on `X_étale`. If `F` and all the `F_i` are constructible, then the
ind-object `F_i` is essentially constant with value `F`.

This is a helper lemma. It is used by the unconditional
`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit`
(Stacks 095P, part (3)) in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleEssentiallyConstantColimit`,
which supplies `h095N` by Stacks 095N. -/
public theorem isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit
    (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]
    (h095N : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
          (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
            QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) G)
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleModuleSheaf B X R (F.obj i))
    (hcolim : IsConstructibleModuleSheaf B X R t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  exact exists_isEssentiallyConstantWith_of_isFinitelyPresentable ht
    (isFinitelyPresentable_of_isConstructibleModuleSheaf B X R h095N _ hcolim)
    fun j ↦ isFinitelyPresentable_of_isConstructibleModuleSheaf B X R h095N _ (hF j)

end AlgebraicGeometry

end
