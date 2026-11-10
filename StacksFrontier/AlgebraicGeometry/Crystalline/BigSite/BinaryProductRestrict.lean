module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality

/-!
# Restricting a binary product of the big crystalline site to opens

Let `A`, `B` be objects of the big crystalline category `CRIS(X/S)` and suppose the product
`A × B` exists, presented as a binary fan `c` over `(A, B)` together with a proof that `c` is a
limit.  Let `U` be an open of the ambient scheme of `A` and `V` an open of the ambient scheme of
`B`.  Then the restriction of `c.pt` to the open

`W = fst⁻¹(U) ∩ snd⁻¹(V)`

of its ambient scheme, with the two maps obtained by restricting the projections of `c`, is a
binary product of `A|U` and `B|V`.

The input is the universal property of a lift through the open immersion
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenHom`: a morphism `f : T ⟶ C`
whose map on ambient schemes has image inside an open `V` factors, uniquely, through
`C.restrictOpen V`.  Existence of the factorization is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift` and uniqueness is
`Crystalline.GlobalCrystallineSituation.Thickening.mono_restrictOpenHom`.  Both are built from
the corresponding statement for divided power schemes,
`Crystalline.DividedPowerScheme.restrictLift`, which is Mathlib's universal property of an open
immersion `AlgebraicGeometry.IsOpenImmersion.lift` upgraded with the compatibility with divided
powers: over an open `U` of the restriction `X|V` the divided power structure of `X|V` is that of
`X` over the image of `U`, so the compatibility of the lift is the compatibility of the original
morphism followed by a restriction map.

## Main definitions

* `Crystalline.DividedPowerScheme.restrictLift` — the factorization of a morphism of divided
  power schemes through the restriction to an open containing the image of its underlying map.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift` — the same factorization
  for a morphism of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenProductOpen` — the open
  `W = fst⁻¹(U) ∩ snd⁻¹(V)` of the ambient scheme of the vertex of a binary fan.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFst`,
  `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenSnd` — the two projections of
  the restricted fan.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.mono_restrictOpenHom` — the structure
  morphism of a restriction to an open is a monomorphism of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.Thickening.isLimit_restrictOpenBinaryFan` — **the
  restriction of a binary product is the binary product of the restrictions**: the fan with
  vertex `c.pt|W` and the restricted projections is a limit.
* `Crystalline.GlobalCrystallineSituation.Thickening.hasBinaryProduct_restrictOpen` — if `A` and
  `B` have a binary product in `CRIS(X/S)`, so do `A|U` and `B|V`.

## What is and is not proved

Only the statement above is proved: *given* a binary fan over `(A, B)` which is a limit, the
restricted fan is a limit.  Nothing here asserts that binary products exist in `CRIS(X/S)`; the
existence hypothesis is carried as an explicit `IsLimit` (or `HasBinaryProduct`) argument, and
`Crystalline.GlobalCrystallineSituation.Thickening.hasBinaryProduct_restrictOpen` only transports
an assumed product along restriction.  No affineness, no Cartesian condition on the projections
and no covering argument enters; in particular this file says nothing about how a product of two
objects of `CRIS(X/S)` is glued from local pieces.

## References

* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace DividedPowerScheme

variable {X Y : DividedPowerScheme.{u}} (f : Y ⟶ X) (V : X.scheme.Opens)

/-- **A morphism whose image lies in an open factors through it topologically.**  The image of the
underlying map of `f` is contained in the image of the open immersion of `V`. -/
theorem range_subset_range_ι (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    Set.range f.hom.base ⊆ Set.range V.ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨f.hom.base z, hf ⟨z, rfl⟩⟩, rfl⟩

/-- The factorization of the underlying morphism of schemes of `f` through the open immersion of
an open `V` containing its image. -/
noncomputable def restrictLiftBase (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    Y.scheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι f.hom (range_subset_range_ι f V hf)

/-- The factorization of the underlying morphism of schemes, followed by the open immersion of
`V`, is the underlying morphism of schemes of `f`. -/
@[reassoc]
theorem restrictLiftBase_ι (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    restrictLiftBase f V hf ≫ V.ι = f.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The preimage of an open `U` of `V` under the factorization is the preimage of its image in
`X`. -/
theorem restrictLiftBase_preimage (hf : Set.range f.hom.base ⊆ (V : Set X.scheme))
    (U : V.toScheme.Opens) :
    restrictLiftBase f V hf ⁻¹ᵁ U = f.hom ⁻¹ᵁ (V.ι ''ᵁ U) :=
  IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux _ V.ι _
    (restrictLiftBase_ι f V hf).symm U

/-- **The factorization on sections.**  Since the sections of `V` over `U` are the sections of `X`
over the image of `U`, the map on sections of the factorization is the map on sections of `f`
followed by a restriction map. -/
theorem restrictLiftBase_app (hf : Set.range f.hom.base ⊆ (V : Set X.scheme))
    (U : V.toScheme.Opens) :
    (restrictLiftBase f V hf).app U = f.hom.app (V.ι ''ᵁ U) ≫
      Y.scheme.presheaf.map (eqToHom (restrictLiftBase_preimage f V hf U)).op := by
  have h := IsOpenImmersion.lift_app V.ι f.hom (range_subset_range_ι f V hf) U
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
  exact h.trans (Category.id_comp _)

/-- `Crystalline.DividedPowerScheme.restrictLiftBase_app` evaluated at a section. -/
theorem restrictLiftBase_app_apply (hf : Set.range f.hom.base ⊆ (V : Set X.scheme))
    (U : V.toScheme.Opens) (z : Γ(X.scheme, V.ι ''ᵁ U)) :
    ((restrictLiftBase f V hf).app U).hom z =
      (Y.scheme.presheaf.map (eqToHom (restrictLiftBase_preimage f V hf U)).op).hom
        ((f.hom.app (V.ι ''ᵁ U)).hom z) :=
  congrArg (fun m : Γ(X.scheme, V.ι ''ᵁ U) ⟶
      Γ(Y.scheme, restrictLiftBase f V hf ⁻¹ᵁ U) ↦ m.hom z)
    (restrictLiftBase_app f V hf U)

/-- **The universal property of the restriction of a divided power scheme to an open.**  A
morphism `f : Y ⟶ X` of divided power schemes whose underlying map has image inside an open `V`
of `X` factors through `X.restrict V`.  On sections the factorization is the map on sections of
`f` followed by a restriction map, and both are morphisms of divided power rings. -/
noncomputable def restrictLift (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    Y ⟶ X.restrict V where
  hom := restrictLiftBase f V hf
  compatible U := by
    refine Eq.mpr (congrArg _ ?_) (DividedPowers.IsDPMorphism.comp _
      (Y.dividedPowers.naturality (eqToHom (restrictLiftBase_preimage f V hf U)).op)
      (f.compatible (V.ι ''ᵁ U)))
    exact RingHom.ext fun z ↦ restrictLiftBase_app_apply f V hf U z

/-- The underlying morphism of schemes of
`Crystalline.DividedPowerScheme.restrictLift` is
`Crystalline.DividedPowerScheme.restrictLiftBase`. -/
@[simp]
theorem restrictLift_hom (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    (restrictLift f V hf).hom = restrictLiftBase f V hf := rfl

/-- **The factorization through a restriction is a factorization.** -/
@[reassoc]
theorem restrictLift_restrictι (hf : Set.range f.hom.base ⊆ (V : Set X.scheme)) :
    restrictLift f V hf ≫ X.restrictι V = f :=
  Hom.ext (restrictLiftBase_ι f V hf)

end DividedPowerScheme

namespace GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}}

section Lift

variable {T C : Thickening S} (f : T ⟶ C) (V : C.thickening.target.scheme.Opens)

/-- **A morphism of `CRIS(X/S)` whose ambient map lands in an open lands in its preimage on
thickened schemes.**  The square of a morphism of thickenings commutes, so a point of the
thickened scheme of `T` is sent into the preimage of `V`. -/
theorem range_sourceHom_subset_range_ι
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    Set.range f.sourceHom.base ⊆ Set.range (C.thickening.immersion ⁻¹ᵁ V).ι.base := by
  rintro _ ⟨y, rfl⟩
  refine ⟨⟨f.sourceHom.base y, ?_⟩, rfl⟩
  change (f.sourceHom ≫ C.thickening.immersion).base y ∈ V
  rw [← f.immersion_naturality]
  exact hf ⟨_, rfl⟩

/-- The factorization of a morphism of `CRIS(X/S)` on thickened schemes, through the open
immersion of the preimage of `V`. -/
noncomputable def restrictOpenLiftSource
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    T.thickening.source ⟶ (C.thickening.immersion ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift (C.thickening.immersion ⁻¹ᵁ V).ι f.sourceHom
    (range_sourceHom_subset_range_ι f V hf)

/-- The factorization on thickened schemes, followed by the open immersion of the preimage of
`V`, is the map on thickened schemes of `f`. -/
@[reassoc]
theorem restrictOpenLiftSource_ι
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    restrictOpenLiftSource f V hf ≫ (C.thickening.immersion ⁻¹ᵁ V).ι = f.sourceHom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The two factorizations, on thickened and on ambient schemes, form a commuting square of
thickenings. -/
theorem restrictOpenLift_immersion_naturality
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    T.thickening.immersion ≫ DividedPowerScheme.restrictLiftBase f.targetHom V hf =
      restrictOpenLiftSource f V hf ≫ C.thickening.immersion ∣_ V := by
  refine (cancel_mono V.ι).mp ?_
  rw [Category.assoc, Category.assoc, morphismRestrict_ι,
    DividedPowerScheme.restrictLiftBase_ι, f.immersion_naturality, ← Category.assoc,
    restrictOpenLiftSource_ι]

/-- **The universal property of the restriction of an object of `CRIS(X/S)` to an open.**  A
morphism `f : T ⟶ C` whose map on ambient schemes has image inside an open `V` factors through
`C.restrictOpen V`; the factorization is the factorization of
`Crystalline.DividedPowerScheme.restrictLift` on ambient schemes and the factorization through
the preimage of `V` on thickened schemes. -/
noncomputable def restrictOpenLift
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    T ⟶ C.restrictOpen V where
  sourceHom := restrictOpenLiftSource f V hf
  targetHom := DividedPowerScheme.restrictLift f.targetHom V hf
  immersion_naturality := restrictOpenLift_immersion_naturality f V hf
  base_naturality := by
    change DividedPowerScheme.restrictLift f.targetHom V hf ≫
      (C.thickening.target.restrictι V ≫ C.toBase) = T.toBase
    rw [← Category.assoc, DividedPowerScheme.restrictLift_restrictι, f.base_naturality]
  toX_naturality := by
    change restrictOpenLiftSource f V hf ≫ ((C.thickening.immersion ⁻¹ᵁ V).ι ≫ C.toX) = T.toX
    rw [← Category.assoc, restrictOpenLiftSource_ι, f.toX_naturality]

/-- The map on thickened schemes of
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift`. -/
@[simp]
theorem restrictOpenLift_sourceHom
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    (restrictOpenLift f V hf).sourceHom = restrictOpenLiftSource f V hf := rfl

/-- The map on ambient schemes of
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift`. -/
@[simp]
theorem restrictOpenLift_targetHom
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    (restrictOpenLift f V hf).targetHom = DividedPowerScheme.restrictLift f.targetHom V hf := rfl

/-- **The factorization through a restriction is a factorization.** -/
@[reassoc]
theorem restrictOpenLift_restrictOpenHom
    (hf : Set.range f.targetHom.hom.base ⊆ (V : Set C.thickening.target.scheme)) :
    restrictOpenLift f V hf ≫ C.restrictOpenHom V = f :=
  Hom.ext (restrictOpenLiftSource_ι f V hf)
    (DividedPowerScheme.restrictLift_restrictι f.targetHom V hf)

end Lift

/-- **A morphism of `CRIS(X/S)` is determined by its map on ambient schemes.**  The immersion of
the target is a closed immersion, hence a monomorphism, and the square of a morphism of
thickenings commutes. -/
theorem hom_ext_of_targetHom {E F : Thickening S} {a b : E ⟶ F}
    (h : a.targetHom.hom = b.targetHom.hom) : a = b := by
  refine Hom.ext ((cancel_mono F.thickening.immersion).mp ?_) (DividedPowerScheme.Hom.ext h)
  rw [← a.immersion_naturality, ← b.immersion_naturality, h]

/-- **The structure morphism of a restriction to an open is a monomorphism.**  A morphism of
`CRIS(X/S)` is determined by its map on ambient schemes, and the open immersion of `V` is a
monomorphism of schemes. -/
instance mono_restrictOpenHom (C : Thickening S) (V : C.thickening.target.scheme.Opens) :
    Mono (C.restrictOpenHom V) := by
  refine ⟨fun {T} a b hab ↦ hom_ext_of_targetHom ((cancel_mono V.ι).mp ?_)⟩
  exact congrArg (fun k : T ⟶ C ↦ k.targetHom.hom) hab

/-- **Two morphisms into a restriction agreeing after the structure morphism are equal.** -/
theorem restrictOpen_hom_ext {T C : Thickening S} {V : C.thickening.target.scheme.Opens}
    {a b : T ⟶ C.restrictOpen V} (h : a ≫ C.restrictOpenHom V = b ≫ C.restrictOpenHom V) :
    a = b :=
  (cancel_mono (C.restrictOpenHom V)).mp h

section BinaryProduct

variable {A B : Thickening S} (c : BinaryFan A B) (U : A.thickening.target.scheme.Opens)
  (V : B.thickening.target.scheme.Opens)

/-- **The open of the ambient scheme of a product over which both projections are restricted.**
It is the intersection of the preimages of `U` under the first and of `V` under the second
projection. -/
def restrictOpenProductOpen : c.pt.thickening.target.scheme.Opens :=
  (c.fst.targetHom.hom ⁻¹ᵁ U) ⊓ (c.snd.targetHom.hom ⁻¹ᵁ V)

/-- Over `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenProductOpen` the first
projection lands in `U`. -/
theorem range_restrictOpenHom_comp_fst_subset :
    Set.range (c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.fst).targetHom.hom.base ⊆
      (U : Set A.thickening.target.scheme) := by
  rintro _ ⟨x, rfl⟩
  exact x.2.1

/-- Over `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenProductOpen` the second
projection lands in `V`. -/
theorem range_restrictOpenHom_comp_snd_subset :
    Set.range (c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.snd).targetHom.hom.base ⊆
      (V : Set B.thickening.target.scheme) := by
  rintro _ ⟨x, rfl⟩
  exact x.2.2

/-- **The first projection of the restricted fan**, the factorization of the first projection of
`c` through the restriction of `A` to `U`. -/
noncomputable def restrictOpenFst :
    c.pt.restrictOpen (restrictOpenProductOpen c U V) ⟶ A.restrictOpen U :=
  restrictOpenLift (c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.fst) U
    (range_restrictOpenHom_comp_fst_subset c U V)

/-- **The second projection of the restricted fan**, the factorization of the second projection of
`c` through the restriction of `B` to `V`. -/
noncomputable def restrictOpenSnd :
    c.pt.restrictOpen (restrictOpenProductOpen c U V) ⟶ B.restrictOpen V :=
  restrictOpenLift (c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.snd) V
    (range_restrictOpenHom_comp_snd_subset c U V)

/-- The first projection of the restricted fan is compatible with the structure morphisms of the
restrictions. -/
@[reassoc]
theorem restrictOpenFst_restrictOpenHom :
    restrictOpenFst c U V ≫ A.restrictOpenHom U =
      c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.fst :=
  restrictOpenLift_restrictOpenHom _ _ _

/-- The second projection of the restricted fan is compatible with the structure morphisms of the
restrictions. -/
@[reassoc]
theorem restrictOpenSnd_restrictOpenHom :
    restrictOpenSnd c U V ≫ B.restrictOpenHom V =
      c.pt.restrictOpenHom (restrictOpenProductOpen c U V) ≫ c.snd :=
  restrictOpenLift_restrictOpenHom _ _ _

/-- The morphism into the vertex of `c` induced by a fan over the two restrictions, obtained from
the universal property of `c` applied to the two projections of the fan followed by the structure
morphisms of the restrictions. -/
noncomputable def restrictOpenFanLift (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) : s.pt ⟶ c.pt :=
  hc.lift (BinaryFan.mk (s.fst ≫ A.restrictOpenHom U) (s.snd ≫ B.restrictOpenHom V))

/-- The induced morphism into the vertex of `c`, followed by the first projection of `c`, is the
first projection of the fan followed by the structure morphism of the restriction. -/
@[reassoc]
theorem restrictOpenFanLift_fst (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    restrictOpenFanLift c U V hc s ≫ c.fst = s.fst ≫ A.restrictOpenHom U :=
  hc.fac _ ⟨WalkingPair.left⟩

/-- The induced morphism into the vertex of `c`, followed by the second projection of `c`, is the
second projection of the fan followed by the structure morphism of the restriction. -/
@[reassoc]
theorem restrictOpenFanLift_snd (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    restrictOpenFanLift c U V hc s ≫ c.snd = s.snd ≫ B.restrictOpenHom V :=
  hc.fac _ ⟨WalkingPair.right⟩

/-- **The induced morphism into the vertex of `c` lands in the open `W`.**  Its composite with the
first projection factors through the restriction of `A` to `U`, hence lands in `U`, and likewise
on the other side. -/
theorem range_restrictOpenFanLift_subset (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    Set.range (restrictOpenFanLift c U V hc s).targetHom.hom.base ⊆
      (restrictOpenProductOpen c U V : Set c.pt.thickening.target.scheme) := by
  rintro _ ⟨x, rfl⟩
  constructor
  · change (restrictOpenFanLift c U V hc s ≫ c.fst).targetHom.hom.base x ∈ U
    rw [restrictOpenFanLift_fst]
    exact (s.fst.targetHom.hom.base x).2
  · change (restrictOpenFanLift c U V hc s ≫ c.snd).targetHom.hom.base x ∈ V
    rw [restrictOpenFanLift_snd]
    exact (s.snd.targetHom.hom.base x).2

/-- The morphism from a fan over the two restrictions into the restricted vertex, obtained by
factoring `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFanLift` through the
restriction to `W`. -/
noncomputable def restrictOpenProductLift (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    s.pt ⟶ c.pt.restrictOpen (restrictOpenProductOpen c U V) :=
  restrictOpenLift (restrictOpenFanLift c U V hc s) (restrictOpenProductOpen c U V)
    (range_restrictOpenFanLift_subset c U V hc s)

/-- The morphism into the restricted vertex, followed by the structure morphism of the
restriction, is the morphism into the vertex of `c`. -/
@[reassoc]
theorem restrictOpenProductLift_restrictOpenHom (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    restrictOpenProductLift c U V hc s ≫ c.pt.restrictOpenHom (restrictOpenProductOpen c U V) =
      restrictOpenFanLift c U V hc s :=
  restrictOpenLift_restrictOpenHom _ _ _

/-- The induced morphism is compatible with the first projection of the restricted fan. -/
theorem restrictOpenProductLift_fst (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    restrictOpenProductLift c U V hc s ≫ restrictOpenFst c U V = s.fst := by
  refine restrictOpen_hom_ext ?_
  rw [Category.assoc, restrictOpenFst_restrictOpenHom,
    restrictOpenProductLift_restrictOpenHom_assoc, restrictOpenFanLift_fst]

/-- The induced morphism is compatible with the second projection of the restricted fan. -/
theorem restrictOpenProductLift_snd (hc : IsLimit c)
    (s : BinaryFan (A.restrictOpen U) (B.restrictOpen V)) :
    restrictOpenProductLift c U V hc s ≫ restrictOpenSnd c U V = s.snd := by
  refine restrictOpen_hom_ext ?_
  rw [Category.assoc, restrictOpenSnd_restrictOpenHom,
    restrictOpenProductLift_restrictOpenHom_assoc, restrictOpenFanLift_snd]

/-- **The restriction of a binary product is the binary product of the restrictions.**  Let `c` be
a binary fan over `(A, B)` which is a limit, `U` an open of the ambient scheme of `A` and `V` one
of the ambient scheme of `B`.  The restriction of the vertex of `c` to
`W = fst⁻¹(U) ∩ snd⁻¹(V)`, with the two restricted projections, is a binary product of `A|U` and
`B|V`.

A fan over `(A|U, B|V)` is pushed into a fan over `(A, B)`, lifted through `c`, and the lift lands
in `W` because each of its composites with a projection of `c` factors through a restriction;
uniqueness is the uniqueness in `c` together with the fact that the structure morphism of a
restriction is a monomorphism. -/
noncomputable def isLimit_restrictOpenBinaryFan (hc : IsLimit c) :
    IsLimit (BinaryFan.mk (restrictOpenFst c U V) (restrictOpenSnd c U V)) :=
  BinaryFan.isLimitMk (restrictOpenProductLift c U V hc)
    (restrictOpenProductLift_fst c U V hc) (restrictOpenProductLift_snd c U V hc)
    fun s m e₁ e₂ ↦ by
      refine restrictOpen_hom_ext ?_
      rw [restrictOpenProductLift_restrictOpenHom]
      refine BinaryFan.IsLimit.hom_ext hc ?_ ?_
      · rw [Category.assoc, ← restrictOpenFst_restrictOpenHom, ← Category.assoc, e₁,
          restrictOpenFanLift_fst]
      · rw [Category.assoc, ← restrictOpenSnd_restrictOpenHom, ← Category.assoc, e₂,
          restrictOpenFanLift_snd]

end BinaryProduct

/-- **The restrictions of two objects with a binary product have a binary product.**  It is the
restriction of the product to `W = fst⁻¹(U) ∩ snd⁻¹(V)`, by
`Crystalline.GlobalCrystallineSituation.Thickening.isLimit_restrictOpenBinaryFan`. -/
theorem hasBinaryProduct_restrictOpen (A B : Thickening S) [HasBinaryProduct A B]
    (U : A.thickening.target.scheme.Opens) (V : B.thickening.target.scheme.Opens) :
    HasBinaryProduct (A.restrictOpen U) (B.restrictOpen V) :=
  ⟨⟨_, isLimit_restrictOpenBinaryFan (limit.cone (pair A B)) U V (limit.isLimit (pair A B))⟩⟩

end Thickening

end GlobalCrystallineSituation

end Crystalline

end
