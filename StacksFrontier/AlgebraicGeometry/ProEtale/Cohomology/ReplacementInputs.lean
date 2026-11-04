module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Connected.Clopen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of global sections of a Zariski sheaf

A continuous map `f : X ⟶ Y` of topological spaces induces, through the inverse-image/direct-image
adjunction on sheaves for the open-cover topologies, a map on global sections. This file records
that map, its compatibility with composition, and the two cases in which it is bijective for
formal reasons: when `f` is a homeomorphism, and — at the level of the underlying point-set
topology — the connectedness transfer that is used to recognise the geometric cases.

Coefficients live in `Type (max (u + 1) v)`, a universe large enough for the left Kan extensions
that compute the inverse image on a site whose objects already live one universe above its
morphisms.

## Main definitions

* `AlgebraicGeometry.ProEtale.globalSectionsPullback` is the map on global sections induced by a
  continuous map, namely the component at the whole space of the unit of the sheaf
  pullback/pushforward adjunction.
* `AlgebraicGeometry.ProEtale.zariskiSheafPullbackCompIso` identifies the inverse image along a
  composite with the composite of the inverse images.

## Main results

* `AlgebraicGeometry.ProEtale.globalSectionsPullback_comp` says that `globalSectionsPullback` is
  compatible with `zariskiSheafPullbackCompIso`.
* `AlgebraicGeometry.ProEtale.globalSectionsPullback_bijective_of_iso`: along an isomorphism of
  spaces the map on global sections is bijective.
* `AlgebraicGeometry.ProEtale.isConnected_preimage_of_surjective_isClosedMap`: for a surjective
  closed continuous map with connected fibres, the preimage of a connected closed set is
  connected.

## Implementation notes

The inverse image is Mathlib's `Functor.sheafPullback` for `Opens.map f`, which exists because
`Opens.map f` is continuous for the open-cover topologies. `zariskiSheafPullbackCompIso` is
obtained from uniqueness of left adjoints: the direct images compose on the nose, so the two
candidate inverse images are left adjoint to the same functor.

`globalSectionsPullback_bijective_of_iso` is proved by exhibiting the unit of the adjunction as
an isomorphism: for a homeomorphism the induced equivalence of lattices of opens is a dense
subsite in both directions, so the inverse image agrees with the equivalence of sheaf categories
it induces, whose unit is invertible.

## References

* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.ProEtale

section GlobalSections

variable {X Y Z : TopCat.{u}}

/-- The map on global sections induced by a continuous map: the component at the whole space of
the unit of the inverse-image/direct-image adjunction for the open-cover topologies. -/
def globalSectionsPullback (i : X ⟶ Y)
    (F : Sheaf (Opens.grothendieckTopology Y) (Type (max (u + 1) v))) :
    F.obj.obj (Opposite.op ⊤) →
      (((Opens.map i).sheafPullback (Type (max (u + 1) v))
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj F).obj.obj
        (Opposite.op ⊤) :=
  (((Opens.map i).sheafAdjunctionContinuous (Type (max (u + 1) v))
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app F).hom.app
      (Opposite.op ⊤)

/-- The inverse image along a composite of continuous maps is the composite of the inverse
images: the direct images compose on the nose, so both are left adjoint to the same functor. -/
@[ega "0 3.5.5" "special case"]
def zariskiSheafPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Opens.map (f ≫ g)).sheafPullback (Type (max (u + 1) v))
        (Opens.grothendieckTopology Z)
        (Opens.grothendieckTopology X) ≅
      (Opens.map g).sheafPullback (Type (max (u + 1) v))
        (Opens.grothendieckTopology Z)
        (Opens.grothendieckTopology Y) ⋙
        (Opens.map f).sheafPullback (Type (max (u + 1) v))
          (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X) :=
  ((Opens.map (f ≫ g)).sheafAdjunctionContinuous (Type (max (u + 1) v))
    (Opens.grothendieckTopology Z) (Opens.grothendieckTopology X)).leftAdjointUniq
      ((((Opens.map g).sheafAdjunctionContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y)).comp
      ((Opens.map f).sheafAdjunctionContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))).ofNatIsoRight (Iso.refl _))

/-- Pullback of global sections is compatible with composition, through
`zariskiSheafPullbackCompIso`. -/
lemma globalSectionsPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (Opens.grothendieckTopology Z) (Type (max (u + 1) v))) :
    (fun s => (((zariskiSheafPullbackCompIso f g).hom.app F).hom.app (Opposite.op ⊤))
          (globalSectionsPullback (f ≫ g) F s)) =
      fun s => globalSectionsPullback f
        (((Opens.map g).sheafPullback (Type (max (u + 1) v))
          (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y)).obj F)
        (globalSectionsPullback g F s) := by
  funext s
  let a := (Opens.map (f ≫ g)).sheafAdjunctionContinuous (Type (max (u + 1) v))
    (Opens.grothendieckTopology Z) (Opens.grothendieckTopology X)
  let b := (((Opens.map g).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y)).comp
    ((Opens.map f).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))).ofNatIsoRight (Iso.refl _)
  exact (congrArg (fun q => q.hom.app (Opposite.op ⊤) s) (a.unit_leftAdjointUniq_hom_app b F) :)

/-- For a homeomorphism `e`, the inverse of the induced equivalence of lattices of opens is a
dense subsite for the open-cover topologies. -/
lemma isDenseSubsite_mapMapIso_inverse (e : X ≅ Y) :
    (Opens.mapMapIso e).inverse.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
  refine { functorPushforward_mem_iff := ?_ }
  intro U S
  refine ⟨fun h x hx => ?_, fun h y hy => ?_⟩
  · rw [Opens.mem_grothendieckTopology] at h
    have hy : e.hom x ∈ (Opens.mapMapIso e).inverse.obj U := by
      show e.inv (e.hom x) ∈ U
      simpa using hx
    obtain ⟨V, g, hg, hV⟩ := h (e.hom x) hy
    refine ⟨(Opens.mapMapIso e).functor.obj V,
      (Opens.mapMapIso e).functor.map g ≫ (Opens.mapMapIso e).counit.app U, ?_, ?_⟩
    · simpa only [Sieve.mem_functorPushforward_inverse] using hg
    · show x ∈ e.hom ⁻¹' (V : Set Y)
      simpa using hV
  · rw [Opens.mem_grothendieckTopology] at h
    change e.inv y ∈ U at hy
    obtain ⟨V, g, hg, hxV⟩ := h (e.inv y) hy
    refine ⟨(Opens.mapMapIso e).inverse.obj V, (Opens.mapMapIso e).inverse.map g, ?_, ?_⟩
    · rw [Sieve.mem_functorPushforward_inverse]
      have hnat : (Opens.mapMapIso e).functor.map ((Opens.mapMapIso e).inverse.map g) ≫
          (Opens.mapMapIso e).counit.app U = (Opens.mapMapIso e).counit.app V ≫ g := by
        simpa using (Opens.mapMapIso e).counit.naturality g
      rw [hnat]
      exact S.downward_closed hg ((Opens.mapMapIso e).counit.app V)
    · exact hxV

/-- Along an isomorphism of spaces, pullback of global sections of a sheaf of types is
bijective. -/
lemma globalSectionsPullback_bijective_of_iso (e : X ≅ Y)
    (F : Sheaf (Opens.grothendieckTopology Y) (Type (max (u + 1) v))) :
    Function.Bijective (globalSectionsPullback e.hom F) := by
  have := isDenseSubsite_mapMapIso_inverse e
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let C := Equivalence.sheafCongr J K (Opens.mapMapIso e) (Type (max (u + 1) v))
  let adj := (Opens.map e.hom).sheafAdjunctionContinuous (Type (max (u + 1) v)) J K
  have : IsIso adj.unit := adj.isIso_unit_of_iso
    (Functor.isoWhiskerRight (adj.leftAdjointUniq C.toAdjunction)
      ((Opens.map e.hom).sheafPushforwardContinuous (Type (max (u + 1) v)) J K) ≪≫
        C.unitIso.symm)
  show Function.Bijective ((adj.unit.app F).hom.app (Opposite.op ⊤))
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end GlobalSections

/-- A surjective closed continuous map with connected fibres pulls connected closed sets back to
connected sets: such a map is coinducing, and a coinducing map with connected fibres has this
property. -/
lemma isConnected_preimage_of_surjective_isClosedMap
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hclosed : IsClosedMap f)
    (hfib : ∀ y, IsConnected (f ⁻¹' ({y} : Set β)))
    {T : Set β} (hT : IsClosed T) (hconn : IsConnected T) :
    IsConnected (f ⁻¹' T) := by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed hfib ?_ hT hconn
  refine Topology.isCoinducing_iff_isClosed.mpr fun s => ⟨fun hs => ?_, fun hs => hs.preimage hf⟩
  simpa only [Set.image_preimage_eq s hsurj] using hclosed _ hs

end AlgebraicGeometry.ProEtale

end
