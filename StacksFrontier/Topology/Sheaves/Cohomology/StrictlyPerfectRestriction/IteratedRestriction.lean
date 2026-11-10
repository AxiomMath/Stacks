module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs

/-!
# Iterated restriction of modules on a ringed space

Restricting a ringed space to an open `U` and then restricting the result to an open `V` of
`X.restrict U` lands in a *different* category of modules from restricting `X` directly to the
image of `V` in `X`, even though the two ringed spaces are canonically isomorphic. This file
provides the transport between the two.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictRestrictEquiv` is the equivalence
  `OXMod ((X.restrict U).restrict V) ≌ OXMod (X.restrict (U.ι ''ᵁ V))`.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.overFunctorIsoRestrictModules` identifies
  restriction to the slice sheaf of rings
  over `U`, followed by
    `AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`, with
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`.

## Implementation notes

Mathlib has the corresponding transport only for schemes (`AlgebraicGeometry.Scheme.Hom.isoImage`);
for presheafed, sheafed and ringed spaces only the `⊤` case (`restrictTopIso`) exists.

The equivalence is built with `SheafOfModules.pushforwardPushforwardEquivalence` from the
equivalence of sites `Opens ↥V ≌ Opens ↥(U.ι ''ᵁ V)` induced by the evident homeomorphism. The
structure sheaf of an open restriction is, by construction, the structure sheaf of `X` composed
with the open-image functor on opens, so both comparison maps of sheaves of rings are values of
`X.presheaf` on morphisms of `Opens X`. Since `Opens X` is a partial order its morphisms are
unique, so every coherence condition -- naturality of the two comparison maps and the two
compatibilities demanded by `pushforwardPushforwardEquivalence` -- reduces to the statement that
`X.presheaf` takes parallel morphisms to equal morphisms.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

section Carrier

variable {X : RingedSpace.{u, u}} {U : Opens X.carrier}
  {V : Opens (X.restrict U.isOpenEmbedding).carrier}

/-- The inclusion of the twice-restricted carrier into `X`. -/
def dblIncl (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier ⟶ X.carrier :=
  Opens.inclusion' V ≫ Opens.inclusion' U

/-- A point of the twice-restricted carrier lies in the image of `V` in `X`. -/
theorem dblIncl_mem (p : ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier) :
    dblIncl X U V p ∈ U.isOpenEmbedding.functor.obj V := by
  obtain ⟨⟨y, hy⟩, hp⟩ := p
  exact ⟨⟨y, hy⟩, hp, rfl⟩

/-- A point of the image of `V` in `X` lies in `U`. -/
theorem mem_of_mem_image (q : ↥(U.isOpenEmbedding.functor.obj V)) : (q.1 : X.carrier) ∈ U := by
  obtain ⟨a, -, ha⟩ := q.2
  exact ha ▸ a.2

/-- A point of the image of `V` in `X`, viewed in `U`, lies in `V`. -/
theorem mem_of_mem_image' (q : ↥(U.isOpenEmbedding.functor.obj V)) :
    (⟨q.1, mem_of_mem_image q⟩ : ↥U) ∈ V := by
  obtain ⟨a, haV, ha⟩ := q.2
  have h : (⟨q.1, mem_of_mem_image q⟩ : ↥U) = a := Subtype.ext ha.symm
  rwa [h]

/-- **The twice-restricted carrier is the carrier of the restriction to the image.** -/
def carrierIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier ≅
      (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier where
  hom := TopCat.ofHom ⟨fun p => ⟨dblIncl X U V p, dblIncl_mem p⟩,
    Continuous.subtype_mk (map_continuous _) _⟩
  inv := TopCat.ofHom ⟨fun q => ⟨⟨q.1, mem_of_mem_image q⟩, mem_of_mem_image' q⟩, by fun_prop⟩
  hom_inv_id := by ext p; rfl
  inv_hom_id := by ext q; rfl

/-- The comparison homeomorphism is an open embedding. -/
theorem carrierIso_hom_isOpenEmbedding (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Topology.IsOpenEmbedding (carrierIso X U V).hom :=
  (TopCat.homeoOfIso (carrierIso X U V)).isOpenEmbedding

/-- The inverse comparison homeomorphism is an open embedding. -/
theorem carrierIso_inv_isOpenEmbedding (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Topology.IsOpenEmbedding (carrierIso X U V).inv :=
  (TopCat.homeoOfIso (carrierIso X U V)).symm.isOpenEmbedding

/-- **The two sites agree.** The opens of the twice-restricted space are the opens of the
restriction to the image of `V`. -/
def opensEquiv (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Opens ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier ≌
      Opens (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier where
  functor := (carrierIso_hom_isOpenEmbedding X U V).functor
  inverse := (carrierIso_inv_isOpenEmbedding X U V).functor
  unitIso := NatIso.ofComponents (fun A => eqToIso (by
    apply Opens.ext
    change (A : Set _) = (carrierIso X U V).inv '' ((carrierIso X U V).hom '' (A : Set _))
    rw [Set.image_image]
    exact (Set.image_id' _).symm)) (by intros; subsingleton)
  counitIso := NatIso.ofComponents (fun B => eqToIso (by
    apply Opens.ext
    change (carrierIso X U V).hom '' ((carrierIso X U V).inv '' (B : Set _)) = (B : Set _)
    rw [Set.image_image]
    exact Set.image_id' _)) (by intros; subsingleton)
  functor_unitIso_comp := by intros; subsingleton

/-- The forward functor of `opensEquiv` is continuous for the Grothendieck topologies of open
covers. -/
instance opensEquiv_functor_isContinuous (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Functor.IsContinuous (opensEquiv X U V).functor
      (Opens.grothendieckTopology
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier) :=
  (carrierIso_hom_isOpenEmbedding X U V).functor_isContinuous

/-- The inverse functor of `opensEquiv` is continuous for the Grothendieck topologies of open
covers. -/
instance opensEquiv_inverse_isContinuous (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Functor.IsContinuous (opensEquiv X U V).inverse
      (Opens.grothendieckTopology
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
      (Opens.grothendieckTopology
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier) :=
  (carrierIso_inv_isOpenEmbedding X U V).functor_isContinuous

end Carrier

section Rings

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  (V : Opens (X.restrict U.isOpenEmbedding).carrier)

/-- **Morphisms of `Opens X` are unique**, so the structure sheaf takes parallel morphisms to
equal morphisms. -/
theorem structureSheafOfRings_map_eq {Z₁ Z₂ : (Opens X.carrier)ᵒᵖ} (f g : Z₁ ⟶ Z₂) :
    (structureSheafOfRings X).obj.map f = (structureSheafOfRings X).obj.map g :=
  congrArg _ (Subsingleton.elim f g)

/-- Parallel composites of structure-sheaf restriction maps agree. -/
theorem structureSheafOfRings_mapComp_eq {Z₁ Z₂ Z₃ Z₄ : (Opens X.carrier)ᵒᵖ} (a : Z₁ ⟶ Z₂)
    (b : Z₂ ⟶ Z₄) (c : Z₁ ⟶ Z₃) (d : Z₃ ⟶ Z₄) :
    (structureSheafOfRings X).obj.map a ≫ (structureSheafOfRings X).obj.map b =
      (structureSheafOfRings X).obj.map c ≫ (structureSheafOfRings X).obj.map d := by
  simp only [← Functor.map_comp]; rfl

/-- A structure-sheaf restriction map is any composite of two with the same endpoints. -/
theorem structureSheafOfRings_map_eq_comp {Z₁ Z₂ Z₃ : (Opens X.carrier)ᵒᵖ} (a : Z₁ ⟶ Z₃)
    (c : Z₁ ⟶ Z₂) (d : Z₂ ⟶ Z₃) :
    (structureSheafOfRings X).obj.map a =
      (structureSheafOfRings X).obj.map c ≫ (structureSheafOfRings X).obj.map d := by
  simp only [← Functor.map_comp]; rfl

/-- A round trip of three structure-sheaf restriction maps is the identity. -/
theorem structureSheafOfRings_mapComp3_eq_id {Z₁ Z₂ Z₃ : (Opens X.carrier)ᵒᵖ} (a : Z₁ ⟶ Z₂)
    (b : Z₂ ⟶ Z₃) (c : Z₃ ⟶ Z₁) :
    (structureSheafOfRings X).obj.map a ≫ (structureSheafOfRings X).obj.map b ≫
        (structureSheafOfRings X).obj.map c = 𝟙 ((structureSheafOfRings X).obj.obj Z₁) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← (structureSheafOfRings X).obj.map_id Z₁]; rfl

/-- **The image of an open of the twice-restricted space.** Pushing an open of
`(X.restrict U).restrict V` forward to `X` through the comparison homeomorphism and the image of
`V` is the same as pushing it forward through `V` and then `U`. -/
theorem image_opensEquiv_functor_obj
    (A : Opens ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier) :
    (U.isOpenEmbedding.functor.obj V).isOpenEmbedding.functor.obj
        ((opensEquiv X U V).functor.obj A) =
      U.isOpenEmbedding.functor.obj (V.isOpenEmbedding.functor.obj A) := by
  apply Opens.ext
  refine Set.Subset.antisymm ?_ ?_ <;>
    rintro y ⟨p, ⟨q, hq, rfl⟩, rfl⟩ <;> exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩

/-- **The image of an open of the restriction to the image of `V`.** The same statement as
`AlgebraicGeometry.RingedSpace.PseudoCoherence.image_opensEquiv_functor_obj` for the inverse
comparison. -/
theorem image_opensEquiv_inverse_obj
    (B : Opens (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier) :
    U.isOpenEmbedding.functor.obj
        (V.isOpenEmbedding.functor.obj ((opensEquiv X U V).inverse.obj B)) =
      (U.isOpenEmbedding.functor.obj V).isOpenEmbedding.functor.obj B := by
  apply Opens.ext
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨p, ⟨q, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    exact ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩

/-- **The comparison of structure sheaves, forwards.** -/
def restrictRestrictRingHom :
    structureSheafOfRings ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ⟶
      ((opensEquiv X U V).functor.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (structureSheafOfRings
          (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)) :=
  ⟨{ app := fun A => (structureSheafOfRings X).obj.map
       (homOfLE (le_of_eq (image_opensEquiv_functor_obj X U V A.unop))).op
     naturality := fun _ _ _ => structureSheafOfRings_mapComp_eq X _ _ _ _ }⟩

/-- **The comparison of structure sheaves, backwards.** -/
def restrictRestrictRingInv :
    structureSheafOfRings (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) ⟶
      ((opensEquiv X U V).inverse.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (structureSheafOfRings ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) :=
  ⟨{ app := fun B => (structureSheafOfRings X).obj.map
       (homOfLE (le_of_eq (image_opensEquiv_inverse_obj X U V B.unop))).op
     naturality := fun _ _ _ => structureSheafOfRings_mapComp_eq X _ _ _ _ }⟩

/-- **Modules on the restriction to the image are modules on the twice-restricted space.** This
is the ringed-space analogue of `AlgebraicGeometry.Scheme.Hom.isoImage`, which Mathlib has only
for schemes. -/
def restrictRestrictEquivAux :
    OXMod.{u} (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) ≌
      OXMod.{u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) :=
  SheafOfModules.pushforwardPushforwardEquivalence.{u} (opensEquiv X U V)
    (restrictRestrictRingHom X U V) (restrictRestrictRingInv X U V)
    (by ext B : 2; exact structureSheafOfRings_map_eq_comp X _ _ _)
    (by ext A : 2; exact structureSheafOfRings_mapComp3_eq_id X _ _ _)

/-- **The iterated-restriction transport.** Restricting `X` to `U` and then to `V` gives the
same category of modules as restricting `X` to the image of `V`. -/
def restrictRestrictEquiv (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    OXMod.{u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ≌
      OXMod.{u} (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) :=
  (restrictRestrictEquivAux X U V).symm

/-- The functor of `restrictRestrictEquiv` is additive. -/
instance : (restrictRestrictEquiv X U V).functor.Additive := ⟨by intros; ext B x; rfl⟩

/-- The inverse of `restrictRestrictEquiv` is additive. -/
instance : (restrictRestrictEquiv X U V).inverse.Additive := ⟨by intros; ext A x; rfl⟩

/-- The functor of `restrictRestrictEquiv` preserves homology. -/
instance : (restrictRestrictEquiv X U V).functor.PreservesHomology := inferInstance

/-- **Restriction to the slice is restriction to the open subspace.** The ringed-space analogue
of Mathlib's `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`: the slice sheaf of rings over
`U` and the structure sheaf of `X.restrict U` are two presentations of the same thing, and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict` turns one into the
other. -/
def overFunctorIsoRestrictModules (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.overFunctor.{u} (structureSheafOfRings X) U ⋙
        (sheafOfModulesEquivRestrict.{u} X U).functor ≅
      restrictModules.{u} X U :=
  Iso.refl _

end Rings

section StrictlyPerfect

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- Restriction of modules to an open subspace is additive. -/
instance : (restrictModules.{u} X U).Additive := ⟨by intros; ext W x; rfl⟩

/-- Restriction to an open subspace is a left adjoint, because restriction to the slice sheaf of
rings is (`SheafOfModules.overFunctor` is a pushforward along an identity) and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict` is an equivalence. -/
instance : (restrictModules.{u} X U).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (overFunctorIsoRestrictModules X U)

/-- **Restriction preserves finite free modules.** Restriction preserves the structure sheaf as a
module over itself on the nose, and preserves biproducts because it preserves coproducts. -/
def restrictModulesFiniteFreeIso (n : ℕ) :
    (restrictModules.{u} X U).obj (finiteFree X n) ≅
      finiteFree (X.restrict U.isOpenEmbedding) n :=
  letI : PreservesBiproduct (fun _ : Fin n => structureModule X) (restrictModules.{u} X U) :=
    preservesBiproduct_of_preservesCoproduct _
  (Functor.mapBiproduct (restrictModules.{u} X U) (fun _ : Fin n => structureModule X)).trans
    (biproduct.whiskerEquiv (Equiv.refl (Fin n)) (fun _ => Iso.refl _))

/-- **Restriction preserves direct summands of finite free modules.** -/
theorem isDirectSummandOfFiniteFree_restrictModules (E : OXMod.{u} X)
    (hE : IsDirectSummandOfFiniteFree E) :
    IsDirectSummandOfFiniteFree ((restrictModules.{u} X U).obj E) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map (restrictModules.{u} X U)).trans (restrictModulesFiniteFreeIso X U n).retract⟩⟩

/-- **The restriction of a strictly perfect complex is strictly perfect.** Restriction preserves
zero morphisms, so it cannot create a nonzero term, and it preserves direct summands of finite
free modules by
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.isDirectSummandOfFiniteFree_restrictModules`. -/
theorem isStrictlyPerfect_restrictComplex (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    {P : CochainComplex (OXMod.{u} X) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (restrictComplex P U) :=
  ⟨hP.bounded.subset fun _ hi h => hi ((restrictModules.{u} X U).map_isZero h),
    fun i => isDirectSummandOfFiniteFree_restrictModules X U _ (hP.directSummand i)⟩

end StrictlyPerfect

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
