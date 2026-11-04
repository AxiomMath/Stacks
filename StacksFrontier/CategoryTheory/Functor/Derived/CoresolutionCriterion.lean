module

public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute

/-!
# Recognising a right derived functor from coresolutions

Let `L : C ⥤ D` be a localization functor for a class of morphisms `W`, and let `P` be a property
of objects of `C` such that every object admits a morphism of `W` into an object with `P`, and
such that `L` is bijective on the morphisms into an object with `P`. In the triangulated situation
`P` is membership in a coresolving right orthogonal, and the bijectivity is
`CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated`.

Under those hypotheses a candidate `G : D ⥤ H` together with a map `β : F ⟶ L ⋙ G` *is* the right
derived functor of `F` as soon as `β` is invertible at every object with `P`. This is the converse
of `CategoryTheory.Functor.LeftExtension.isIso_hom_app_of_bijective`, and it is what lets one
*produce* right derived functors: a functor on `D` that happens to compute `F` on the coresolving
objects is the right derived functor of `F`, hence is determined up to a unique isomorphism
compatible with the comparison maps, and transformations out of it may be compared by
`CategoryTheory.Functor.rightDerived_ext`.

## Main results

* `CategoryTheory.Functor.isIso_of_isIso_app_of_coresolutions_of_prop`: a transformation of
  functors on `D` invertible at the coresolving objects is invertible.
* `CategoryTheory.Functor.isRightDerivedFunctor_of_coresolutions`: the criterion.
* `CategoryTheory.Functor.rightDerivedIso`: two right derived functors of the same functor are
  isomorphic, compatibly with their comparison maps.

## Implementation notes

*Why the coresolving objects are described by a property rather than by the bijectivity itself.*
`CategoryTheory.Functor.isIso_of_isIso_app_of_coresolutions` of
`StacksFrontier/CategoryTheory/Functor/Derived/Absolute.lean` takes the resolution hypothesis with
the bijectivity of `L` on morphisms *as* the property of the coresolving object, which is all its
own application needs. Here the invertibility of `β` at a coresolving object is an extra
hypothesis, and in the intended application — the cohomology of derived Hom, Tag 0CS5 — proving it
needs more about the coresolving object than bijectivity into it: it needs bijectivity into every
*shift* of it, which follows from the coresolving object lying in the right orthogonal of the
acyclic objects but not from the bijectivity alone. So the property is a parameter and the
bijectivity is a consequence of it, which makes
`CategoryTheory.Functor.isIso_of_isIso_app_of_coresolutions` the special case `P I = ∀ Y,
Function.Bijective (L.map : (Y ⟶ I) → _)` of the first result below.

*The proof is otherwise that of
`CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions`*: the total right derived
functor exists by `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_coresolutions`, the
criterion `CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` turns the goal
into invertibility of the induced map to the candidate, and that is checked at the coresolving
objects, where both comparison maps are invertible. The absoluteness statement of that file is
*not* a special case of this one: there the comparison at a coresolving object is invertible
because it is the image of an invertible map under a functor, which is a property of the
particular candidate `RF ⋙ G` rather than a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] {H' : Type u₄} [Category.{v₄} H']

variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W]

/-- A natural transformation between two functors on the localization `D` is invertible as soon as
it is invertible at `L.obj I` for every coresolving object `I`: every object of `D` is isomorphic
to such an `L.obj I`, because `L` is essentially surjective and inverts the coresolving morphism.

This is `CategoryTheory.Functor.isIso_of_isIso_app_of_coresolutions` with the property describing
the coresolving objects taken as a parameter. -/
theorem isIso_of_isIso_app_of_coresolutions_of_prop {E₁ E₂ : D ⥤ H'} (γ : E₁ ⟶ E₂)
    (P : C → Prop)
    (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧ P I)
    (h : ∀ I : C, P I → IsIso (γ.app (L.obj I))) :
    IsIso γ := by
  have := Localization.essSurj L W
  have happ : ∀ Y : D, IsIso (γ.app Y) := by
    intro Y
    obtain ⟨I, s, hs, hI⟩ := hres (L.objPreimage Y)
    have : IsIso (L.map s) := Localization.inverts L W s hs
    have := h I hI
    let e : Y ≅ L.obj I := (L.objObjPreimageIso Y).symm ≪≫ asIso (L.map s)
    have : IsIso (γ.app Y ≫ E₂.map e.hom) := by
      rw [← γ.naturality e.hom]; infer_instance
    exact IsIso.of_isIso_comp_right (γ.app Y) (E₂.map e.hom)
  exact NatIso.isIso_of_isIso_app γ

/-- **A candidate that computes `F` on the coresolving objects is the right derived functor.**
If every object of `C` admits a morphism of `W` into an object with the property `P`, if `L` is
bijective on the morphisms into an object with `P`, and if `β : F ⟶ L ⋙ G` is invertible at every
object with `P`, then `G` together with `β` is the right derived functor of `F` with respect
to `W`. -/
theorem isRightDerivedFunctor_of_coresolutions {F : C ⥤ H} {G : D ⥤ H} (β : F ⟶ L ⋙ G)
    (P : C → Prop)
    (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧ P I)
    (hbij : ∀ I : C, P I →
      ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I)))
    (hiso : ∀ I : C, P I → IsIso (β.app I)) :
    G.IsRightDerivedFunctor β W := by
  have hres' : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I)) := by
    intro X
    obtain ⟨I, s, hs, hI⟩ := hres X
    exact ⟨I, s, hs, hbij I hI⟩
  have := hasPointwiseRightDerivedFunctor_of_coresolutions W F hres'
  have := F.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor W
  rw [(F.totalRightDerived L W).isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (F.totalRightDerivedUnit L W) W G β]
  refine isIso_of_isIso_app_of_coresolutions_of_prop (L := L) W _ P hres fun I hI => ?_
  have hb := hbij I hI
  have h1 : IsIso (β.app I) := hiso I hI
  have h2 : IsIso ((F.totalRightDerivedUnit L W).app I) :=
    (LeftExtension.mk _ (F.totalRightDerivedUnit L W)).isIso_hom_app_of_bijective
      (isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor _ _ W (L.obj I)) hb
  have h3 : IsIso ((F.totalRightDerivedUnit L W).app I ≫
      ((F.totalRightDerived L W).rightDerivedDesc
        (F.totalRightDerivedUnit L W) W G β).app (L.obj I)) := by
    rw [(F.totalRightDerived L W).rightDerived_fac_app
      (F.totalRightDerivedUnit L W) W G β I]
    infer_instance
  exact IsIso.of_isIso_comp_left ((F.totalRightDerivedUnit L W).app I) _

/-- **Two right derived functors of one functor agree.** The canonical transformation descending
`β'` along `G` is invertible, so it is an isomorphism `G ≅ G'` compatible with the two comparison
maps; `CategoryTheory.Functor.rightDerivedIso_fac` records that compatibility and
`CategoryTheory.Functor.rightDerived_ext` its uniqueness. -/
def rightDerivedIso {F : C ⥤ H} {G G' : D ⥤ H} (β : F ⟶ L ⋙ G) (β' : F ⟶ L ⋙ G')
    [G.IsRightDerivedFunctor β W] [G'.IsRightDerivedFunctor β' W] : G ≅ G' :=
  haveI : IsIso (G.rightDerivedDesc β W G' β') :=
    (G.isRightDerivedFunctor_iff_isIso_rightDerivedDesc β W G' β').1 inferInstance
  asIso (G.rightDerivedDesc β W G' β')

/-- The isomorphism of two right derived functors of one functor is compatible with the two
comparison maps. -/
theorem rightDerivedIso_fac {F : C ⥤ H} {G G' : D ⥤ H} (β : F ⟶ L ⋙ G) (β' : F ⟶ L ⋙ G')
    [G.IsRightDerivedFunctor β W] [G'.IsRightDerivedFunctor β' W] :
    β ≫ Functor.whiskerLeft L (rightDerivedIso W β β').hom = β' :=
  G.rightDerived_fac β W G' β'

end CategoryTheory.Functor

end
