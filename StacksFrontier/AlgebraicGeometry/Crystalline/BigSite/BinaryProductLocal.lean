module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.SituationRestrict

/-!
# Localizing binary products in the big crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W ⊆ S` and an open `V ⊆ X` whose
image in `S` lies in `W`.  An object of `CRIS(X/S)` whose ambient scheme maps into `W` and whose
thickened scheme maps into `V` *is* an object of `CRIS(V/S|_W)`, and change of base along the two
open immersions, [Stacks, Tag 07IC], takes the latter reading back to the original object.  Since
change of base is fully faithful, a binary product computed in `CRIS(V/S|_W)` is a binary product
in `CRIS(X/S)` as soon as every scheme carrying a cone over the two factors is itself in the image
of change of base — which the local reading of objects provides.  This is the localization step of
[Stacks, Tag 07I9]: products of objects supported over affine opens of `S` and `X` may be
constructed in the affine situation.

## Main definitions

* `Crystalline.DividedPowerScheme.liftRestrict` — the factorization of a morphism of divided power
  schemes whose image lies in an open `W` through `X.restrict W`.
* `Crystalline.GlobalCrystallineSituation.localObject` — an object of `CRIS(X/S)` whose two
  structure morphisms land in `W` and `V`, read as an object of `CRIS(V/S|_W)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.extendLocalObjectIso` — extending the local reading of an
  object gives back the object.
* `CategoryTheory.Limits.hasBinaryProduct_of_fullyFaithful_cones` — a fully faithful functor
  carries binary products to binary products, provided every object carrying a cone over the image
  pair is isomorphic to an object in the image.
* `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_extend` — change of base along the two
  open immersions preserves binary products.
* `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_localObject` — two objects supported
  over `W` and `V` have a product as soon as their local readings do.
* `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_affine_localization` — two objects of
  `CRIS(X/S)` supported over affine opens `W` and `V` have a product, granted the product in the
  affine situation.

## What is and is not proved

No tag attribute is placed in this file.  It is the localization half of the binary products of
[Stacks, Tag 07I9]: the existence of binary products in the *affine* situation is not proved here
but taken as the explicit hypothesis `haff` of
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_affine_localization`, which asks for
binary products in a situation whose base, thickened space and the ambient schemes of the two
objects are all affine and in which `p` is nilpotent on global sections.  Likewise the nilpotence
of `p` on `V` is a hypothesis: the data of a global crystalline situation only make `p` locally
nilpotent.  Nothing here asserts that the opens `W` and `V` can be chosen, nor that the products
so constructed glue.

## References

* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace CategoryTheory.Limits

/-- **A fully faithful functor carries a binary product to a binary product, provided every object
carrying a cone over the image pair is in its image up to isomorphism.**  The cone on the images of
the two projections is a limit: a cone with vertex `T` is transported along an isomorphism
`F.obj L ≅ T` to a cone in the source category, where the product of the two factors receives a
unique map, and full faithfulness turns the uniqueness there into uniqueness here. -/
theorem hasBinaryProduct_of_fullyFaithful_cones
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (hF : F.FullyFaithful)
    (A B : C) [HasBinaryProduct A B]
    (h : ∀ (T : D) (_f : T ⟶ F.obj A) (_g : T ⟶ F.obj B),
      ∃ L : C, Nonempty (F.obj L ≅ T)) : HasBinaryProduct (F.obj A) (F.obj B) := by
  classical
  choose L he using h
  let e (T : D) (f : T ⟶ F.obj A) (g : T ⟶ F.obj B) := (he T f g).some
  let q (T : D) (f : T ⟶ F.obj A) (g : T ⟶ F.obj B) : L T f g ⟶ A ⨯ B :=
    prod.lift (hF.preimage ((e T f g).hom ≫ f)) (hF.preimage ((e T f g).hom ≫ g))
  have hq₁ (T : D) (f : T ⟶ F.obj A) (g : T ⟶ F.obj B) :
      F.map (q T f g) ≫ F.map prod.fst = (e T f g).hom ≫ f := by
    simp [q, ← F.map_comp]
  have hq₂ (T : D) (f : T ⟶ F.obj A) (g : T ⟶ F.obj B) :
      F.map (q T f g) ≫ F.map prod.snd = (e T f g).hom ≫ g := by
    simp [q, ← F.map_comp]
  refine HasLimit.mk ⟨BinaryFan.mk (F.map (prod.fst : A ⨯ B ⟶ A))
    (F.map (prod.snd : A ⨯ B ⟶ B)), BinaryFan.IsLimit.mk _
      (fun {T} f g => (e T f g).inv ≫ F.map (q T f g)) ?_ ?_ ?_⟩
  · intro T f g
    simp [hq₁]
  · intro T f g
    simp [hq₂]
  · intro T f g m hm₁ hm₂
    change m ≫ F.map (prod.fst : A ⨯ B ⟶ A) = f at hm₁
    change m ≫ F.map (prod.snd : A ⨯ B ⟶ B) = g at hm₂
    apply (cancel_epi (e T f g).hom).mp
    rw [Iso.hom_inv_id_assoc, ← hF.map_preimage ((e T f g).hom ≫ m)]
    congr 1
    apply prod.hom_ext <;> apply hF.map_injective <;> simp [hm₁, hm₂, hq₁, hq₂]

end CategoryTheory.Limits

namespace Crystalline

namespace DividedPowerScheme

/-- A morphism of divided power schemes whose image lies in an open `W` of the target has image in
the range of the open immersion of `W`. -/
theorem range_le_range_ι {X Y : DividedPowerScheme.{u}} (f : Y ⟶ X) (W : X.scheme.Opens)
    (hf : Set.range f.hom.base ⊆ W) : Set.range f.hom.base ⊆ Set.range W.ι.base := by
  intro y hy
  exact ⟨⟨y, hf hy⟩, rfl⟩

variable {X Y : DividedPowerScheme.{u}} (f : Y ⟶ X) (W : X.scheme.Opens)
  (hf : Set.range f.hom.base ⊆ W)

/-- **The factorization of a morphism of schemes with image in `W` through the open subscheme
`W`.**  This is the underlying morphism of schemes of
`Crystalline.DividedPowerScheme.liftRestrict`. -/
def liftRestrictHom : Y.scheme ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι f.hom (range_le_range_ι f W hf)

/-- The factorization through the open subscheme `W`, composed with the open immersion of `W`, is
the given morphism of schemes. -/
@[reassoc]
theorem liftRestrictHom_ι : liftRestrictHom f W hf ≫ W.ι = f.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The preimage of an open of `W` under the factorization is the preimage of its image in the
ambient scheme. -/
theorem liftRestrictHom_preimage (V : W.toScheme.Opens) :
    liftRestrictHom f W hf ⁻¹ᵁ V = f.hom ⁻¹ᵁ (W.ι ''ᵁ V) := by
  rw [← liftRestrictHom_ι f W hf, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]

/-- **The factorization on sections**: the sections of `f` over the image of `V`, followed by the
restriction identifying the two presentations of the preimage.  The comparison isomorphism of the
open immersion `W.ι` is the identity, by `AlgebraicGeometry.Scheme.Opens.ι_appIso`. -/
theorem liftRestrictHom_app (V : W.toScheme.Opens) (z : Γ(X.scheme, W.ι ''ᵁ V)) :
    ((liftRestrictHom f W hf).app V).hom z =
      (Y.scheme.presheaf.map (eqToHom (liftRestrictHom_preimage f W hf V)).op).hom
        ((f.hom.app (W.ι ''ᵁ V)).hom z) := by
  have h := IsOpenImmersion.lift_app W.ι f.hom (range_le_range_ι f W hf) V
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
  exact congrArg (fun m : Γ(X.scheme, W.ι ''ᵁ V) ⟶
    Γ(Y.scheme, liftRestrictHom f W hf ⁻¹ᵁ V) ↦ m.hom z) h

/-- **The factorization of a morphism of divided power schemes with image in an open `W` through
the restriction `X|_W`.**  The divided power ideal of `X|_W` over an open `V` is that of `X` over
the image of `V`, so the compatibility with the divided powers is that of the given morphism over
the image, composed with a restriction map of the structure sheaf of the source. -/
def liftRestrict : Y ⟶ X.restrict W where
  hom := liftRestrictHom f W hf
  compatible V := by
    have h := DividedPowers.IsDPMorphism.comp
      (Y.dividedPowers.dividedPowers (op (liftRestrictHom f W hf ⁻¹ᵁ V)))
      (Y.dividedPowers.naturality (eqToHom (liftRestrictHom_preimage f W hf V)).op)
      (f.compatible (W.ι ''ᵁ V))
    refine Eq.mpr (congrArg _ ?_) h
    exact RingHom.ext fun z ↦ liftRestrictHom_app f W hf V z

/-- The underlying morphism of schemes of the factorization through `X|_W`, by definition. -/
@[simp]
theorem liftRestrict_hom : (liftRestrict f W hf).hom = liftRestrictHom f W hf := rfl

/-- The factorization through `X|_W` composed with the morphism `X|_W ⟶ X` is the given
morphism. -/
@[reassoc]
theorem liftRestrict_restrictι : liftRestrict f W hf ≫ X.restrictι W = f :=
  Hom.ext (liftRestrictHom_ι f W hf)

end DividedPowerScheme

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The structure morphism of the restricted situation, composed with the open immersion of `W`,
is the structure morphism of `S` restricted to `V`.**  Reassociating, the closed fibre inclusion of
`S|_W` followed by the open immersion of `W` is the map of closed fibres followed by the closed
fibre inclusion of `S` (`Crystalline.DividedPowerScheme.closedFiberMap_comp_closedFiberι`), and the
structure morphism of the restricted situation composed with the map of closed fibres is the
structure morphism of `S` restricted to `V`
(`Crystalline.GlobalCrystallineSituation.restrict_changeBase_condition`). -/
@[reassoc]
theorem restrict_sourceToBase :
    sourceToBase (restrict S W V hVW) ≫ W.ι = V.ι ≫ sourceToBase S :=
  (Category.assoc _ _ _).trans
    ((congrArg ((restrict S W V hVW).toClosedFiber ≫ ·)
        (DividedPowerScheme.closedFiberMap_comp_closedFiberι (S.S.restrictι W)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ DividedPowerScheme.closedFiberι S.S)
            (restrict_changeBase_condition S W V hVW)).trans (Category.assoc _ _ _))))

variable (T : Thickening S) (hW : Set.range T.toBase.hom.base ⊆ W)
  (hV : Set.range T.toX.base ⊆ V)

/-- The factorization of the map to `X` of an object whose thickened scheme maps into `V` through
the open subscheme `V`. -/
def localObjectToX : T.thickening.source ⟶ V.toScheme :=
  (IsOpenImmersion.lift V.ι T.toX (fun _ hy ↦ ⟨⟨_, hV hy⟩, rfl⟩) :
    T.thickening.source ⟶ V.toScheme)

/-- The factorization of the map to `X` through `V`, composed with the open immersion of `V`, is
the map to `X`. -/
@[reassoc]
theorem localObjectToX_ι : localObjectToX S V T hV ≫ V.ι = T.toX :=
  IsOpenImmersion.lift_fac _ _ _

/-- **An object of `CRIS(X/S)` whose ambient scheme maps into `W` and whose thickened scheme maps
into `V`, read as an object of `CRIS(V/S|_W)`.**  The underlying divided power thickening is
unchanged; the two structure morphisms are factored through the two open immersions, and the
compatibility of the factorizations is the compatibility of the original morphisms, the open
immersion of `W` being a monomorphism. -/
def localObject : Thickening (restrict S W V hVW) where
  thickening := T.thickening
  toBase := DividedPowerScheme.liftRestrict T.toBase W hW
  toX := localObjectToX S V T hV
  over_base := (cancel_mono W.ι).mp <|
    calc (T.thickening.immersion ≫ (DividedPowerScheme.liftRestrict T.toBase W hW).hom) ≫ W.ι
        = T.thickening.immersion ≫
            ((DividedPowerScheme.liftRestrict T.toBase W hW).hom ≫ W.ι) := Category.assoc _ _ _
      _ = T.thickening.immersion ≫ T.toBase.hom :=
          congrArg _ (DividedPowerScheme.liftRestrictHom_ι T.toBase W hW)
      _ = T.toX ≫ sourceToBase S := T.over_base
      _ = (localObjectToX S V T hV ≫ V.ι) ≫ sourceToBase S :=
          congrArg (· ≫ sourceToBase S) (localObjectToX_ι S V T hV).symm
      _ = localObjectToX S V T hV ≫ (V.ι ≫ sourceToBase S) := Category.assoc _ _ _
      _ = localObjectToX S V T hV ≫ (sourceToBase (restrict S W V hVW) ≫ W.ι) :=
          congrArg _ (restrict_sourceToBase S W V hVW).symm
      _ = (localObjectToX S V T hV ≫ sourceToBase (restrict S W V hVW)) ≫ W.ι :=
          (Category.assoc _ _ _).symm

/-- Reading an object in the restricted situation does not change its divided power thickening. -/
@[simp]
theorem localObject_thickening : (localObject S W V hVW T hW hV).thickening = T.thickening := rfl

/-- The divided power base morphism of an object of `CRIS(X/S)`, read in the restricted
situation. -/
@[simp]
theorem localObject_toBase :
    (localObject S W V hVW T hW hV).toBase = DividedPowerScheme.liftRestrict T.toBase W hW := rfl

/-- The map to `V` of an object of `CRIS(X/S)`, read in the restricted situation. -/
@[simp]
theorem localObject_toX :
    (localObject S W V hVW T hW hV).toX = localObjectToX S V T hV := rfl

/-- The underlying divided power thickening is unchanged by change of base. -/
@[simp]
theorem extend_obj_thickening (A : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj A).thickening = A.thickening := rfl

/-- The divided power base morphism of a rebased object is its base morphism followed by the
restriction morphism of the base. -/
@[simp]
theorem extend_obj_toBase (A : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj A).toBase = A.toBase ≫ S.S.restrictι W := rfl

/-- The map to `X` of a rebased object is its map to `V` followed by the open immersion. -/
@[simp]
theorem extend_obj_toX (A : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj A).toX = A.toX ≫ V.ι := rfl

/-- Change of base does not change the map on thickened schemes. -/
@[simp]
theorem extend_map_sourceHom {A B : Thickening (restrict S W V hVW)} (k : A ⟶ B) :
    ((extend S W V hVW).map k).sourceHom = k.sourceHom := rfl

/-- Change of base does not change the map on ambient divided power schemes. -/
@[simp]
theorem extend_map_targetHom {A B : Thickening (restrict S W V hVW)} (k : A ⟶ B) :
    ((extend S W V hVW).map k).targetHom = k.targetHom := rfl

/-- **Extending the local reading of an object gives back the object.**  Both objects have the same
underlying divided power thickening, and the two pairs of structure morphisms agree because
factoring through an open immersion and composing back is the identity. -/
def extendLocalObjectIso :
    (extend S W V hVW).obj (localObject S W V hVW T hW hV) ≅ T where
  hom :=
    { sourceHom := 𝟙 T.thickening.source
      targetHom := 𝟙 T.thickening.target
      immersion_naturality := by simp
      base_naturality := (Category.id_comp T.toBase).trans
        (DividedPowerScheme.liftRestrict_restrictι T.toBase W hW).symm
      toX_naturality := (Category.id_comp T.toX).trans (localObjectToX_ι S V T hV).symm }
  inv :=
    { sourceHom := 𝟙 T.thickening.source
      targetHom := 𝟙 T.thickening.target
      immersion_naturality := by simp
      base_naturality :=
        (Category.id_comp (DividedPowerScheme.liftRestrict T.toBase W hW ≫
          S.S.restrictι W)).trans (DividedPowerScheme.liftRestrict_restrictι T.toBase W hW)
      toX_naturality :=
        (Category.id_comp (localObjectToX S V T hV ≫ V.ι)).trans (localObjectToX_ι S V T hV) }
  hom_inv_id := by apply Thickening.Hom.ext <;> simp
  inv_hom_id := by apply Thickening.Hom.ext <;> simp

/-- **Change of base along the two open immersions preserves binary products.**  Any object of
`CRIS(X/S)` carrying a cone over the images of two objects of `CRIS(V/S|_W)` has both structure
morphisms factoring through `W` and `V`, hence is the extension of its own local reading;
`CategoryTheory.Limits.hasBinaryProduct_of_fullyFaithful_cones` then applies to the fully faithful
change of base. -/
theorem hasBinaryProduct_extend (A B : Thickening (restrict S W V hVW))
    [HasBinaryProduct A B] :
    HasBinaryProduct ((extend S W V hVW).obj A) ((extend S W V hVW).obj B) := by
  refine hasBinaryProduct_of_fullyFaithful_cones (extend S W V hVW)
    (extendFullyFaithful S W V hVW) A B ?_
  intro T f g
  have hW : Set.range T.toBase.hom.base ⊆ W := by
    rintro y ⟨x, rfl⟩
    have hf := congrArg (fun k : T.thickening.target ⟶ S.S ↦ k.hom.base x) f.base_naturality
    rw [← hf]
    exact (A.toBase.hom.base (f.targetHom.hom.base x)).property
  have hV : Set.range T.toX.base ⊆ V := by
    rintro y ⟨x, rfl⟩
    have hf := congrArg (fun k : T.thickening.source ⟶ S.X ↦ k.base x) f.toX_naturality
    rw [← hf]
    exact (A.toX.base (f.sourceHom.base x)).property
  exact ⟨localObject S W V hVW T hW hV, ⟨extendLocalObjectIso S W V hVW T hW hV⟩⟩

/-- **Two objects of `CRIS(X/S)` whose structure morphisms land in `W` and `V` have a binary
product as soon as their local readings do.**  The product of the local readings is carried into
`CRIS(X/S)` by `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_extend`, and the two
extended objects are the original ones by
`Crystalline.GlobalCrystallineSituation.extendLocalObjectIso`. -/
theorem hasBinaryProduct_of_localObject (A B : Thickening S)
    (hWA : Set.range A.toBase.hom.base ⊆ W) (hVA : Set.range A.toX.base ⊆ V)
    (hWB : Set.range B.toBase.hom.base ⊆ W) (hVB : Set.range B.toX.base ⊆ V)
    [HasBinaryProduct (localObject S W V hVW A hWA hVA) (localObject S W V hVW B hWB hVB)] :
    HasBinaryProduct A B := by
  have := hasBinaryProduct_extend S W V hVW (localObject S W V hVW A hWA hVA)
    (localObject S W V hVW B hWB hVB)
  exact hasLimit_of_iso (mapPairIso
    (F := pair ((extend S W V hVW).obj (localObject S W V hVW A hWA hVA))
      ((extend S W V hVW).obj (localObject S W V hVW B hWB hVB))) (G := pair A B)
    (extendLocalObjectIso S W V hVW A hWA hVA) (extendLocalObjectIso S W V hVW B hWB hVB))

include hVW in
/-- **Two objects of `CRIS(X/S)` supported over affine opens of `S` and `X` have a binary
product**, granted binary products in the affine situation.  The two objects are read in the
restricted situation `(p, S|_W, V)`, whose base and thickened space are affine; their product
there, supplied by `haff`, is carried back by
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_extend`, and the extensions of the local
readings are the original objects by
`Crystalline.GlobalCrystallineSituation.extendLocalObjectIso`. -/
theorem hasBinaryProduct_of_affine_localization
    (haff : ∀ (S' : GlobalCrystallineSituation.{u}), IsAffine S'.X → IsAffine S'.S.scheme →
      IsNilpotent (S'.p : Γ(S'.X, ⊤)) → ∀ (A' B' : Thickening S'),
        IsAffine A'.thickening.source → IsAffine A'.thickening.target.scheme →
        IsAffine B'.thickening.source → IsAffine B'.thickening.target.scheme →
        HasBinaryProduct A' B')
    (hWaff : IsAffineOpen W) (hVaff : IsAffineOpen V)
    (hVnil : IsNilpotent (S.p : Γ(V.toScheme, ⊤)))
    (A B : Thickening S) [IsAffine A.thickening.target.scheme]
    [IsAffine B.thickening.target.scheme]
    (hWA : Set.range A.toBase.hom.base ⊆ W) (hVA : Set.range A.toX.base ⊆ V)
    (hWB : Set.range B.toBase.hom.base ⊆ W) (hVB : Set.range B.toX.base ⊆ V) :
    HasBinaryProduct A B := by
  have : IsAffine (restrict S W V hVW).S.scheme := hWaff
  have : IsAffine (restrict S W V hVW).X := hVaff
  have hA : IsAffine A.thickening.source :=
    AlgebraicGeometry.isAffine_of_isAffineHom A.thickening.immersion
  have hB : IsAffine B.thickening.source :=
    AlgebraicGeometry.isAffine_of_isAffineHom B.thickening.immersion
  have := haff (restrict S W V hVW) inferInstance inferInstance hVnil
    (localObject S W V hVW A hWA hVA) (localObject S W V hVW B hWB hVB)
    hA (inferInstanceAs (IsAffine A.thickening.target.scheme))
    hB (inferInstanceAs (IsAffine B.thickening.target.scheme))
  exact hasBinaryProduct_of_localObject S W V hVW A B hWA hVA hWB hVB

end GlobalCrystallineSituation

end Crystalline

end
