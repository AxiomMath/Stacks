module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Permanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Properties of morphisms of schemes which are étale local on the source and target

Local finite presentation, smoothness, flatness, the conjunction of local finite type and
local quasi-finiteness, étaleness, unramifiedness and G-unramifiedness are each Zariski local
on the source and on the target, stable under base change, preserved by composition with an
étale morphism on either side, and descend along a surjective étale morphism of sources. So
each of them is étale local on the source, étale local on the target, and — through the
criterion of Tag 04R2 — étale local on the source and target.

Local finite type is treated separately in
`StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/FiniteType.lean`.

## Main definitions

There are no new definitions.

## Main results

For each of `AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.Smooth`,
`AlgebraicGeometry.Flat`,
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`,
`AlgebraicGeometry.Etale`, `AlgebraicGeometry.Unramified` and
`AlgebraicGeometry.GUnramified`:

* an `AlgebraicGeometry.MorphismProperty.IsLocalAtSource _ Scheme.etalePrecoverage` instance,
* an `AlgebraicGeometry.MorphismProperty.IsLocalAtTarget _ Scheme.etalePrecoverage` instance,
* a `CategoryTheory.MorphismProperty.RespectsRight _ @IsOpenImmersion` instance, and
* an `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` theorem.

* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_gUnramified`: **Stacks 04R3**, item (10),
  the G-unramified one.

## Implementation notes

All of the work is in
`AlgebraicGeometry.isLocalAtSource_etalePrecoverage_of_zariski_of_descent` and
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_zariski_of_descent`; what is supplied
here, per property, is the descent along a surjective étale morphism of sources, and the
preservation under composition with an étale morphism, which for the first five properties is
typeclass inference from the fact that an étale morphism has the property and the property is
stable under composition. For unramifiedness and G-unramifiedness there is no instance
producing the property of a composite from the property of its two factors, so the
composition stability is applied by name, through
`CategoryTheory.MorphismProperty.comp_mem`, to the étaleness of the one factor.

The descent inputs are Tag 02KL for local finite presentation, Tag 05B5 for smoothness, Tag
02JZ for flatness, Tag 0GWS together with Tag 02KL for the conjunction of local finite type
and local quasi-finiteness, and Tag 02K6 together with Tag 02KL for étaleness. For
unramifiedness and G-unramifiedness the descent is the argument of Tag 03YV in the form
recorded by Tag 02HE: the finiteness half is Tag 02KL and the formal half is the stalkwise
descent of formal unramifiedness along a surjective smooth morphism,
`Stacks.Etale.formallyUnramified_stalkMap`, an étale morphism being smooth. Flatness does
*not* need the fppf-refinement form of Tag 06NB: Tag 02JZ,
`AlgebraicGeometry.flat_of_comp_of_surjective_flat`, already descends flatness along a
surjective flat morphism, and an étale morphism is flat.

Two of the five descent steps are not proved here but imported from
`StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent`, which collects the descent
of a property of morphisms of schemes along a surjective étale morphism of sources:
`AlgebraicGeometry.locallyQuasiFinite_of_comp_surjective_etale` for the conjunction of local
finite type and local quasi-finiteness, and `Stacks.Etale.etale_of_comp_surjective_etale`
for étaleness.

The Zariski localities that the two upgrades take as instance arguments have to be passed by
name rather than found by typeclass inference: the goal `IsZariskiLocalAtSource P` for a
concrete `P` does not unify with the conclusion of
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`, and likewise at the
target. For the conjunction the two components are passed by name and
`CategoryTheory.MorphismProperty.IsLocalAtSource.inf` is applied to them.

All seven localities are stated for the étale precoverage only, which is weaker than Stacks
036O ("fppf local on the source") and than Stacks 02KX ("fpqc local on the base"); neither of
those tags is claimed here. That does not hold Stacks 04R3 back, because the conclusion of
Tag 04R3 is étale locality on the source-and-target and the criterion of Tag 04R2 it is read
off from asks only for étale locality on each of the source and the target: the fppf and fpqc
statements the source cites are stronger than what the conclusion needs. So item (10) of
Tag 04R3, the G-unramified one, is recorded here on
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_gUnramified`. The other nine items are
recorded elsewhere, each in the file dedicated to its property, which is why the four
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` theorems in this file for local finite
presentation, smoothness, flatness and the conjunction of local finite type with local
quasi-finiteness carry no tag: they would duplicate a registration that already exists.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks Project, Tag 02K6](https://stacks.math.columbia.edu/tag/02K6)
* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
* [Stacks Project, Tag 03YV](https://stacks.math.columbia.edu/tag/03YV)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
* [Stacks Project, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Local finite presentation -/

/-- Local finite presentation descends along a surjective étale morphism of sources: an étale
morphism is flat and locally of finite presentation, so Tag 02KL applies. -/
@[sga "4 IV 8.5.5" "special case"]
private theorem locallyOfFinitePresentation_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) (hs : Surjective α) (het : Etale α)
    (hαk : LocallyOfFinitePresentation (α ≫ k)) : LocallyOfFinitePresentation k :=
  have : Surjective α := hs
  have : Etale α := het
  have : LocallyOfFinitePresentation (α ≫ k) := hαk
  locallyOfFinitePresentation_of_comp_of_fppf α k

/-- Local finite presentation of a morphism of schemes is étale local on the source. -/
instance isLocalAtSource_etalePrecoverage_locallyOfFinitePresentation :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf => have : Etale g := hg; have : LocallyOfFinitePresentation f := hf;
      inferInstance)
    locallyOfFinitePresentation_of_comp_surjective_etale

/-- Local finite presentation of a morphism of schemes is étale local on the target. -/
@[sga "4 IV 8.5.5" "special case"]
instance isLocalAtTarget_etalePrecoverage_locallyOfFinitePresentation :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg => have : Etale g := hg; have : LocallyOfFinitePresentation f := hf;
      inferInstance)
    locallyOfFinitePresentation_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves local finite presentation: an open
immersion is étale, hence locally of finite presentation. -/
instance respectsRight_isOpenImmersion_locallyOfFinitePresentation :
    MorphismProperty.RespectsRight
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := by
    have : IsOpenImmersion g := hg
    have : LocallyOfFinitePresentation f := hf
    infer_instance

/-- **Local finite presentation is étale local on the source and target.** -/
@[sga "4 IV 8.5.5" "special case"]
theorem isEtaleLocalOnSourceAndTarget_locallyOfFinitePresentation :
    IsEtaleLocalOnSourceAndTarget
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

/-! ### Smoothness -/

/-- Smoothness descends along a surjective étale morphism of sources: an étale morphism is
flat and locally of finite presentation, so Tag 05B5 applies. -/
private theorem smooth_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) (hs : Surjective α) (het : Etale α)
    (hαk : Smooth (α ≫ k)) : Smooth k :=
  have : Surjective α := hs
  have : Etale α := het
  have : Smooth (α ≫ k) := hαk
  Stacks.Smooth.smooth_of_comp_of_fppf α k

/-- Smoothness of a morphism of schemes is étale local on the source. -/
instance isLocalAtSource_etalePrecoverage_smooth :
    MorphismProperty.IsLocalAtSource (@Smooth.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf => have : Etale g := hg; have : Smooth f := hf; inferInstance)
    smooth_of_comp_surjective_etale

/-- Smoothness of a morphism of schemes is étale local on the target. -/
@[ega "IV 17.3.2" "partial"]
instance isLocalAtTarget_etalePrecoverage_smooth :
    MorphismProperty.IsLocalAtTarget (@Smooth.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg => have : Etale g := hg; have : Smooth f := hf; inferInstance)
    smooth_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves smoothness: an open immersion is étale,
hence smooth. -/
instance respectsRight_isOpenImmersion_smooth :
    MorphismProperty.RespectsRight (@Smooth.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := by
    have : IsOpenImmersion g := hg
    have : Smooth f := hf
    infer_instance

/-- **Smoothness is étale local on the source and target.** -/
theorem isEtaleLocalOnSourceAndTarget_smooth :
    IsEtaleLocalOnSourceAndTarget (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

/-! ### Flatness -/

/-- Flatness descends along a surjective étale morphism of sources: an étale morphism is
flat, so Tag 02JZ applies. -/
private theorem flat_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) (hs : Surjective α) (het : Etale α)
    (hαk : Flat (α ≫ k)) : Flat k :=
  have : Surjective α := hs
  have : Etale α := het
  have : Flat (α ≫ k) := hαk
  flat_of_comp_of_surjective_flat α k

/-- Flatness of a morphism of schemes is étale local on the source. -/
instance isLocalAtSource_etalePrecoverage_flat :
    MorphismProperty.IsLocalAtSource (@Flat.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf => have : Etale g := hg; have : Flat f := hf; inferInstance)
    flat_of_comp_surjective_etale

/-- Flatness of a morphism of schemes is étale local on the target. -/
instance isLocalAtTarget_etalePrecoverage_flat :
    MorphismProperty.IsLocalAtTarget (@Flat.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg => have : Etale g := hg; have : Flat f := hf; inferInstance)
    flat_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves flatness: an open immersion is étale,
hence flat. -/
instance respectsRight_isOpenImmersion_flat :
    MorphismProperty.RespectsRight (@Flat.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := by
    have : IsOpenImmersion g := hg
    have : Flat f := hf
    infer_instance

/-- **Flatness is étale local on the source and target.** -/
theorem isEtaleLocalOnSourceAndTarget_flat :
    IsEtaleLocalOnSourceAndTarget (@Flat.{u} : MorphismProperty Scheme.{u}) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

/-! ### Local quasi-finiteness together with local finite type -/

/-- An étale morphism of schemes is locally of finite type and locally quasi-finite, which is
Tag 03II. -/
private theorem locallyOfFiniteType_inf_locallyQuasiFinite_of_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) (hg : Etale g) :
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) g :=
  have : Etale g := hg
  locallyQuasiFinite_of_etale g

/-- Local finite type together with local quasi-finiteness of a morphism of schemes is étale
local on the source. -/
instance isLocalAtSource_etalePrecoverage_locallyOfFiniteType_inf_locallyQuasiFinite :
    MorphismProperty.IsLocalAtSource
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
  have _ : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite.{u})
  have _ : IsZariskiLocalAtSource
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.inf _ _
  have _ : MorphismProperty.IsStableUnderComposition
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderComposition.inf
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf =>
      MorphismProperty.comp_mem _ g f
        (locallyOfFiniteType_inf_locallyQuasiFinite_of_etale g hg) hf)
    locallyQuasiFinite_of_comp_surjective_etale

/-- Local finite type together with local quasi-finiteness of a morphism of schemes is étale
local on the target. -/
instance isLocalAtTarget_etalePrecoverage_locallyOfFiniteType_inf_locallyQuasiFinite :
    MorphismProperty.IsLocalAtTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
  have _ : IsZariskiLocalAtTarget (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyQuasiFinite.{u})
  have _ : IsZariskiLocalAtTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  have _ : MorphismProperty.IsStableUnderComposition
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderComposition.inf
  have _ : MorphismProperty.IsStableUnderBaseChange
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg =>
      MorphismProperty.comp_mem _ f g hf
        (locallyOfFiniteType_inf_locallyQuasiFinite_of_etale g hg))
    locallyQuasiFinite_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves local finite type together with local
quasi-finiteness: an open immersion is étale, hence has both properties. -/
instance respectsRight_isOpenImmersion_locallyOfFiniteType_inf_locallyQuasiFinite :
    MorphismProperty.RespectsRight
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf :=
    have : IsOpenImmersion g := hg
    have _ : MorphismProperty.IsStableUnderComposition
        ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
      MorphismProperty.IsStableUnderComposition.inf
    MorphismProperty.comp_mem _ f g hf
      (locallyOfFiniteType_inf_locallyQuasiFinite_of_etale g inferInstance)

/-- **Local finite type together with local quasi-finiteness is étale local on the source and
target.** -/
theorem isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite :
    IsEtaleLocalOnSourceAndTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

/-! ### Étaleness -/

/-- Étaleness of a morphism of schemes is étale local on the source. -/
instance isLocalAtSource_etalePrecoverage_etale :
    MorphismProperty.IsLocalAtSource (@Etale.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf => have : Etale g := hg; have : Etale f := hf; inferInstance)
    (fun α k hs het hαk =>
      have : Surjective α := hs
      have : Etale α := het
      have : Etale (α ≫ k) := hαk
      Stacks.Etale.etale_of_comp_surjective_etale α k)

/-- Étaleness of a morphism of schemes is étale local on the target. -/
instance isLocalAtTarget_etalePrecoverage_etale :
    MorphismProperty.IsLocalAtTarget (@Etale.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg => have : Etale g := hg; have : Etale f := hf; inferInstance)
    (fun α k hs het hαk =>
      have : Surjective α := hs
      have : Etale α := het
      have : Etale (α ≫ k) := hαk
      Stacks.Etale.etale_of_comp_surjective_etale α k)

/-- Postcomposition with an open immersion preserves étaleness: an open immersion is
étale. -/
instance respectsRight_isOpenImmersion_etale :
    MorphismProperty.RespectsRight (@Etale.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := by
    have : IsOpenImmersion g := hg
    have : Etale f := hf
    infer_instance

/-! ### Unramifiedness -/

/-- Formal unramifiedness descends along a surjective étale morphism of sources, stalkwise along
a surjective smooth morphism. -/
private theorem formallyUnramified_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) [Surjective α] [Etale α]
    [FormallyUnramified (α ≫ k)] : FormallyUnramified k :=
  HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
    (Stacks.Etale.formallyUnramified_stalkMap α k)

/-- Unramifiedness descends along a surjective étale morphism of sources: unramifiedness is
local finite type together with formal unramifiedness (Tag 02HE), the first half descends by
Tag 02KL because an étale morphism is flat and locally of finite presentation, and the second
half descends stalkwise along a surjective smooth morphism, an étale morphism being smooth. -/
@[ega "IV 17.7.7" "special case"]
private theorem unramified_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) (hs : Surjective α) (het : Etale α)
    (hαk : Unramified (α ≫ k)) : Unramified k := by
  have : Surjective α := hs
  have : Etale α := het
  have h := (unramified_iff_locallyOfFiniteType_and_formallyUnramified (α ≫ k)).mp hαk
  have : LocallyOfFiniteType (α ≫ k) := h.1
  have : FormallyUnramified (α ≫ k) := h.2
  exact (unramified_iff_locallyOfFiniteType_and_formallyUnramified k).mpr
    ⟨locallyOfFiniteType_of_comp_of_fppf α k, formallyUnramified_of_comp_surjective_etale α k⟩

/-- Unramifiedness of a morphism of schemes is étale local on the source. The clause of
Tag 03YV is recorded on `AlgebraicGeometry.unramified_isLocalAtSource`. -/
instance isLocalAtSource_etalePrecoverage_unramified :
    MorphismProperty.IsLocalAtSource (@Unramified.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Unramified.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf =>
      MorphismProperty.comp_mem _ g f (have : Etale g := hg; inferInstance) hf)
    unramified_of_comp_surjective_etale

/-- Unramifiedness of a morphism of schemes is étale local on the target. -/
instance isLocalAtTarget_etalePrecoverage_unramified :
    MorphismProperty.IsLocalAtTarget (@Unramified.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Unramified.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg =>
      MorphismProperty.comp_mem _ f g hf (have : Etale g := hg; inferInstance))
    unramified_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves unramifiedness: an open immersion is
étale, hence unramified. -/
instance respectsRight_isOpenImmersion_unramified :
    MorphismProperty.RespectsRight (@Unramified.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf :=
    have : IsOpenImmersion g := hg
    MorphismProperty.comp_mem _ f g hf (inferInstance : Unramified g)

/-! ### G-unramifiedness -/

/-- G-unramifiedness descends along a surjective étale morphism of sources: G-unramifiedness
is local finite presentation together with formal unramifiedness (Tag 02HE), the first half
descends by Tag 02KL because an étale morphism is flat and locally of finite presentation, and
the second half descends stalkwise along a surjective smooth morphism, an étale morphism being
smooth. -/
@[ega "IV 17.3.2" "Remark 17.3.2(iii)",
  ega "IV 17.7.7" "special case",
  sga "4 IV 8.5.5" "special case"]
private theorem gUnramified_of_comp_surjective_etale
    {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z) (hs : Surjective α) (het : Etale α)
    (hαk : GUnramified (α ≫ k)) : GUnramified k := by
  have : Surjective α := hs
  have : Etale α := het
  have h := (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified (α ≫ k)).mp hαk
  have : LocallyOfFinitePresentation (α ≫ k) := h.1
  have : FormallyUnramified (α ≫ k) := h.2
  exact (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified k).mpr
    ⟨locallyOfFinitePresentation_of_comp_of_fppf α k,
      formallyUnramified_of_comp_surjective_etale α k⟩

/-- G-unramifiedness of a morphism of schemes is étale local on the source. The clause of
Tag 03YV is recorded on `AlgebraicGeometry.gUnramified_isLocalAtSource_etale`. -/
@[ega "IV 17.3.2" "Remark 17.3.2(iii)", sga "4 IV 8.5.5" "special case"]
instance isLocalAtSource_etalePrecoverage_gUnramified :
    MorphismProperty.IsLocalAtSource (@GUnramified.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@GUnramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @GUnramified.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf =>
      MorphismProperty.comp_mem _ g f (have : Etale g := hg; inferInstance) hf)
    gUnramified_of_comp_surjective_etale

/-- G-unramifiedness of a morphism of schemes is étale local on the target. -/
@[ega "IV 17.3.2" "Remark 17.3.2(iii)"]
instance isLocalAtTarget_etalePrecoverage_gUnramified :
    MorphismProperty.IsLocalAtTarget (@GUnramified.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@GUnramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @GUnramified.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg =>
      MorphismProperty.comp_mem _ f g hf (have : Etale g := hg; inferInstance))
    gUnramified_of_comp_surjective_etale

/-- Postcomposition with an open immersion preserves G-unramifiedness: an open immersion is
étale, hence G-unramified. -/
instance respectsRight_isOpenImmersion_gUnramified :
    MorphismProperty.RespectsRight (@GUnramified.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf :=
    have : IsOpenImmersion g := hg
    MorphismProperty.comp_mem _ f g hf (inferInstance : GUnramified g)

/-- **Stacks Project, Tag 04R3, item (10).** Being a G-unramified morphism of schemes is étale
local on the source and target.

This is the criterion of Tag 04R2 applied to G-unramifiedness: it is étale local on the source
and on the target by the two instances above, and postcomposition with an open immersion
preserves it. The source cites Tag 03YV for the first and Tag 02VM for the second; the two
localities used here are the ones proved in this file, which is enough, since Tag 04R2 asks for
étale locality only. -/
@[stacks 04R3 "g_unramified", ega "IV 17.3.2" "Remark 17.3.2(iii)"]
theorem isEtaleLocalOnSourceAndTarget_gUnramified :
    IsEtaleLocalOnSourceAndTarget (@GUnramified.{u} : MorphismProperty Scheme.{u}) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

end AlgebraicGeometry

end
