module

public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport

/-!
# Transporting the Rim–Schlessinger conditions along an essentially surjective comparison

Let `F : C ⥤ D` be fully faithful and `p : D ⥤ ArtinianLocalAlgCat Λ k`. If `F ⋙ p` is
cofibered in groupoids with nonempty special fibre, then being a predeformation category
transfers from `p` to `F ⋙ p`; if `F` is moreover essentially surjective, so do the
Rim–Schlessinger condition (RS) and being a deformation category.

## Main results

* `Deformation.Examples.full_compFiberFunctor`, `Deformation.Examples.faithful_compFiberFunctor`:
  the comparison functor on fibres is full and faithful as soon as the comparison is.
* `Deformation.Examples.isPredeformationCategory_comp_of_nonempty`: being a predeformation
  category transports, given the two hypotheses above.
* `Deformation.Examples.satisfiesRS_comp_of_essSurj`: condition (RS) transports along a fully
  faithful essentially surjective comparison whose composite is cofibered in groupoids.
* `Deformation.Examples.isDeformationCategory_comp_of_essSurj`: being a deformation category
  transports.

## References

* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06J9](https://stacks.math.columbia.edu/tag/06J9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Examples

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-! ### The comparison functor on fibres -/

section Fibre

variable {C : Type u₁} {D : Type u₂} {B : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]

/-- The comparison functor on fibres is faithful as soon as the comparison is. -/
public theorem faithful_compFiberFunctor (F : C ⥤ D) [F.Faithful] (p : D ⥤ B) (b : B) :
    (compFiberFunctor F p b).Faithful :=
  ⟨fun h => Subtype.ext (F.map_injective (congrArg Subtype.val h))⟩

/-- The comparison functor on fibres is full as soon as the comparison is. -/
public theorem full_compFiberFunctor (F : C ⥤ D) [F.Full] [F.Faithful] (p : D ⥤ B) (b : B) :
    (compFiberFunctor F p b).Full :=
  ⟨fun {X Y} g => ⟨⟨F.preimage g.1,
    (isHomLift_comp_iff F p _ _).2 (by
      have h : F.map (F.preimage g.1) = g.1 := F.map_preimage g.1
      rw [h]
      exact g.2)⟩,
    Subtype.ext (F.map_preimage _)⟩⟩

end Fibre

/-! ### Transport of the conditions -/

section Transport

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- If `F` is fully faithful, `F ⋙ p` is cofibered in groupoids with nonempty special fibre and
`p` is a predeformation category, then so is `F ⋙ p`. -/
public theorem isPredeformationCategory_comp_of_nonempty
    (F : C ⥤ D) [F.Full] [F.Faithful]
    (p : D ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hcof : IsCofiberedInGroupoids (F ⋙ p))
    (hne : Nonempty ((F ⋙ p).Fiber (residueFieldObject.{u, v, w} Λ k)))
    (hp : IsPredeformationCategory.{u, v, w} p) :
    IsPredeformationCategory.{u, v, w} (F ⋙ p) := by
  refine ⟨hcof, ?_⟩
  obtain ⟨-, hu⟩ := (CategoryTheory.equiv_punit_iff_unique _).mp hp.specialFiber
  have hfull := full_compFiberFunctor F p (residueFieldObject.{u, v, w} Λ k)
  have hfaithful := faithful_compFiberFunctor F p (residueFieldObject.{u, v, w} Λ k)
  refine (CategoryTheory.equiv_punit_iff_unique _).mpr ⟨hne, fun A B => ?_⟩
  have hUniq := (hu ((compFiberFunctor F p (residueFieldObject.{u, v, w} Λ k)).obj A)
    ((compFiberFunctor F p (residueFieldObject.{u, v, w} Λ k)).obj B)).some
  exact ⟨Equiv.unique
    ((Functor.FullyFaithful.ofFullyFaithful
      (compFiberFunctor F p (residueFieldObject.{u, v, w} Λ k))).homEquiv)⟩

/-- If `F` is fully faithful and essentially surjective, `F ⋙ p` is cofibered in groupoids and
`p` satisfies (RS), then so does `F ⋙ p`. -/
public theorem satisfiesRS_comp_of_essSurj
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj]
    (p : D ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hcof : IsCofiberedInGroupoids (F ⋙ p))
    (hp : SatisfiesRS p) : SatisfiesRS (F ⋙ p) := by
  refine ⟨hcof, ?_⟩
  intro x₁ x₂ x f₁ f₂ hs
  obtain ⟨d, hd, hpd⟩ := hp.2 (F.map f₁) (F.map f₂) hs
  let ε : F.obj (F.objPreimage d.pt) ≅ d.pt := F.objObjPreimageIso d.pt
  let a : F.objPreimage d.pt ⟶ x₁ := F.preimage (ε.hom ≫ d.fst)
  let b : F.objPreimage d.pt ⟶ x₂ := F.preimage (ε.hom ≫ d.snd)
  have ha : F.map a = ε.hom ≫ d.fst := F.map_preimage _
  have hb : F.map b = ε.hom ≫ d.snd := F.map_preimage _
  have he : a ≫ f₁ = b ≫ f₂ := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, ha, hb, Category.assoc, Category.assoc, d.condition]
  let c := PullbackCone.mk a b he
  have hi : c.map F ≅ d := PullbackCone.ext ε ha hb
  have hmap : IsLimit (c.map F) := IsLimit.ofIsoLimit hd.some hi.symm
  have hc : IsLimit c := (IsPullback.of_map F he ⟨⟨(c.map F).condition⟩,
    ⟨PullbackCone.mkSelfIsLimit hmap⟩⟩).isLimit
  refine ⟨c, ⟨hc⟩, ?_⟩
  have hi' : (c.map F).map p ≅ d.map p := PullbackCone.ext (p.mapIso ε)
    (by
      change p.map (F.map a) = (p.mapIso ε).hom ≫ p.map d.fst
      rw [ha, p.map_comp]
      rfl)
    (by
      change p.map (F.map b) = (p.mapIso ε).hom ≫ p.map d.snd
      rw [hb, p.map_comp]
      rfl)
  exact ⟨IsLimit.ofIsoLimit hpd.some hi'.symm⟩

/-- If `F` is fully faithful and essentially surjective, `F ⋙ p` is cofibered in groupoids with
nonempty special fibre and `p` is a deformation category, then so is `F ⋙ p`. -/
public theorem isDeformationCategory_comp_of_essSurj
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj]
    (p : D ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hcof : IsCofiberedInGroupoids (F ⋙ p))
    (hne : Nonempty ((F ⋙ p).Fiber (residueFieldObject.{u, v, w} Λ k)))
    (hp : IsDeformationCategory.{u, v, w} p) :
    IsDeformationCategory.{u, v, w} (F ⋙ p) :=
  ⟨isPredeformationCategory_comp_of_nonempty.{u, v, w} F p hcof hne hp.predeformation,
    satisfiesRS_comp_of_essSurj.{u, v, w} F p hcof hp.satisfiesRS⟩

end Transport

end Deformation.Examples

end
