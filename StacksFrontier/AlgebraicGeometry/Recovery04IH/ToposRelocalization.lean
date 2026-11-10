module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizationMorphismsLocallyRinged
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
import StacksCore.Tactic.StacksAttribute

/-!
# Relocalization of a ringed topos, and its locality

Let `X` be a ringed topos and `s : G ⟶ F` a morphism of sheaves of sets on it. Postcomposing a
section with `s` carries the site of elements of `G` to the site of elements of `F`, and that
functor is continuous and cocontinuous for the two restricted topologies (Stacks 04J4). So it
induces a morphism of topoi between the two localizations, and the structure sheaf of the
localization at `G` is the restriction along it of the structure sheaf of the localization at
`F`, on the nose. That makes the pair a morphism of ringed topoi — the *relocalization*
morphism — and, as for the other three morphisms attached to a localization, its structure map
is the identity on underlying sheaves of sets, so it is locally ringed (Stacks 04IH (6)).

## Main definitions

* `AlgebraicGeometry.RingedTopos.toStacks04H9`: a ringed topos read in the single-universe
  presentation `Stacks.Sheaves.LocallyRingedTopos.RingedTopos`.
* `AlgebraicGeometry.RingedTopos.relocalizationMorphismOfTopoi`: relocalization as a morphism
  of topoi.
* `AlgebraicGeometry.RingedTopos.relocalizationInverseImageCommRingIso`: the identification of
  the inverse image of the structure sheaf of the localization at `F` with the structure sheaf
  of the localization at `G`.
* `AlgebraicGeometry.RingedTopos.relocalizationMorphism`: relocalization as a morphism of
  ringed topoi.

## Main results

* `AlgebraicGeometry.RingedTopos.relocalization_fSharp_inverseImage`: the structure map of the
  relocalization, in inverse-image form, is that identification.
* `AlgebraicGeometry.RingedTopos.relocalizationMorphism_isLocallyRinged`: **Stacks 04IH (6)**,
  the relocalization morphism of Stacks 04J4 is locally ringed.

## Implementation notes

Postcomposition of sections and its continuity and cocontinuity are **not** redeveloped here:
they are `Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp` and its two companions in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardRightExact.lean`. Those are stated for
`Stacks.Sheaves.LocallyRingedTopos.RingedTopos`, which carries the same three fields as
`AlgebraicGeometry.RingedTopos.{u, u, u}` — a site, a topology and a `CommRingCat`-valued
structure sheaf, all in one universe — so `toStacks04H9` is a reassociation of the fields and
the site of elements, its topology and the postcomposition functor are literally the same
objects on both sides. The functor itself does not mention the ringed topos at all: it is
`CategoryTheory.CostructuredArrow.map s.hom`.

That the structure sheaf of the localization at `G` is the restriction of the structure sheaf
of the localization at `F` is `rfl`: postcomposition followed by the projection to the site of
`X` is the projection to the site of `X`, on the nose, because both read off the underlying
object of an element. This is `relocalizationRingIso`, which is `Iso.refl`.

The structure map is given in direct-image form, as `AlgebraicGeometry.RingedToposHom` takes it,
and `relocalization_fSharp_inverseImage` recovers the comparison; this matches
`AlgebraicGeometry.RingedSite.relocalizationRingedToposHom` and
`AlgebraicGeometry.RingedTopos.localizationMorphism`. That the units square is then a square of
identities is the observation recorded in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizationMorphismsLocallyRinged.lean`.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.LocalizedRingedTopos

universe v u

namespace AlgebraicGeometry.RingedTopos

/-- A ringed topos with all three universes equal, read as a
  `Stacks.Sheaves.LocallyRingedTopos.RingedTopos`: the same
site, topology and structure sheaf. -/
abbrev toStacks04H9 (X : RingedTopos.{u, u, u}) : Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u}
  :=
  { C := X.C, J := X.J, O := X.O }

variable (X : RingedTopos.{v, u, v}) {G F : X.Topos}

/-- Postcomposition of sections is continuous for the two restricted topologies. This is
`Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp_isContinuous` for sites whose objects lie in
an arbitrary universe. -/
theorem isContinuous_elementPostcomp (s : G ⟶ F) :
    (CostructuredArrow.map s.hom).IsContinuous (elementTopology X G) (elementTopology X F) := by
  refine Functor.isContinuous_of_coverPreserving ?_ ?_
  · exact
      { compatible ℱ {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ e := by
          have el : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := congrArg CommaMorphism.left e
          let W' : elementSite X G := CostructuredArrow.mk (yoneda.map f₁.left ≫ Y₁.hom)
          have w₂ : yoneda.map f₂.left ≫ Y₂.hom = yoneda.map f₁.left ≫ Y₁.hom := by
            rw [← CostructuredArrow.w g₁, ← CostructuredArrow.w g₂, ← Category.assoc,
              ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, el]
          let h₁ : W' ⟶ Y₁ := CostructuredArrow.homMk f₁.left rfl
          let h₂ : W' ⟶ Y₂ := CostructuredArrow.homMk f₂.left w₂
          let ι : W ⟶ (CostructuredArrow.map s.hom).obj W' :=
            CostructuredArrow.homMk (𝟙 W.left) (by simpa [W'] using CostructuredArrow.w f₁)
          have ef₁ : f₁ = ι ≫ (CostructuredArrow.map s.hom).map h₁ :=
            CostructuredArrow.hom_ext _ _ (by simp [ι, h₁])
          have ef₂ : f₂ = ι ≫ (CostructuredArrow.map s.hom).map h₂ :=
            CostructuredArrow.hom_ext _ _ (by simp [ι, h₂])
          have hcomp : h₁ ≫ g₁ = h₂ ≫ g₂ :=
            CostructuredArrow.hom_ext _ _ (by simpa [h₁, h₂] using el)
          rw [ef₁, ef₂]
          simp only [op_comp, Functor.map_comp, types_comp_apply]
          exact congrArg _ (hx h₁ h₂ hg₁ hg₂ hcomp) }
  · refine ⟨fun {U T} hT ↦ ?_⟩
    change T ∈ (CostructuredArrow.proj yoneda G.obj).restrictedTopology X.J U at hT
    change _ ∈ (CostructuredArrow.proj yoneda F.obj).restrictedTopology X.J _
    rw [CategoryTheory.Stacks.Topos.Localized.restrictedTopology_eq_topology] at hT ⊢
    refine X.J.superset_covering ?_ hT
    rintro V g ⟨W, a, b, ha, rfl⟩
    exact ⟨(CostructuredArrow.map s.hom).obj W, (CostructuredArrow.map s.hom).map a, b,
      ⟨W, a, 𝟙 _, ha, by simp⟩, rfl⟩

/-- Postcomposition of sections is cocontinuous for the two restricted topologies. This is
`Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp_isCocontinuous` for sites whose objects lie
in an arbitrary universe. -/
theorem isCocontinuous_elementPostcomp (s : G ⟶ F) :
    (CostructuredArrow.map s.hom).IsCocontinuous (elementTopology X G) (elementTopology X F) where
  cover_lift {U S} hS := by
    change S ∈ (CostructuredArrow.proj yoneda F.obj).restrictedTopology X.J _ at hS
    change _ ∈ (CostructuredArrow.proj yoneda G.obj).restrictedTopology X.J U
    rw [CategoryTheory.Stacks.Topos.Localized.restrictedTopology_eq_topology] at hS ⊢
    refine X.J.superset_covering ?_ hS
    intro V g hg
    refine (CategoryTheory.Stacks.Topos.Localized.mem_functorPushforward_proj_lift_iff G.obj _
      g).2 ?_
    exact (CategoryTheory.Stacks.Topos.Localized.mem_functorPushforward_proj_iff F.obj S
      ((CostructuredArrow.map s.hom).map
        (CategoryTheory.Stacks.Topos.Localized.liftHom G.obj U g))).1 hg

attribute [local instance] isContinuous_elementPostcomp isCocontinuous_elementPostcomp
  hasPointwiseRightKanExtension_of_essentiallySmall

variable [EssentiallySmall.{v} X.C]

/-- Relocalization as a morphism of topoi: its inverse image is restriction along
postcomposition of sections with `s`, its direct image the right adjoint supplied by
cocontinuity of that functor. -/
noncomputable def relocalizationMorphismOfTopoi (s : G ⟶ F) :
    MorphismOfTopoi (localizedRingedTopos X G).Topos (localizedRingedTopos X F).Topos where
  inverseImage := (CostructuredArrow.map s.hom).sheafPushforwardContinuous
    (Type v) (elementTopology X G) (elementTopology X F)
  pushforward := (CostructuredArrow.map s.hom).sheafPushforwardCocontinuous
    (Type v) (elementTopology X G) (elementTopology X F)
  adj := (CostructuredArrow.map s.hom).sheafAdjunctionCocontinuous
    (Type v) (elementTopology X G) (elementTopology X F)
  preservesFiniteLimits :=
    CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous
      (elementTopology X G) (elementTopology X F) (CostructuredArrow.map s.hom) (Type v)

/-- The canonical inverse image of the structure sheaf of the localization at `F` along the
relocalization is the structure sheaf of the localization at `G`: restriction along
postcomposition identifies the inverse image with the restriction, and that restriction is the
localized structure sheaf on the nose. -/
noncomputable def relocalizationInverseImageCommRingIso (s : G ⟶ F) :
    (inverseImageCommRingFunctor.{v, v, v, max u v, v, max u v}
        (X.relocalizationMorphismOfTopoi s)).obj
        (localizedRingedTopos X F).O ≅ (localizedRingedTopos X G).O :=
  restrictionCommRingIso.{v, v, max u v, v, max u v} (elementTopology X G) (elementTopology X F)
    (CostructuredArrow.map s.hom) (localizedRingedTopos X F).O

/-- **Stacks 04J4.** The relocalization morphism of ringed topoi attached to a morphism
`s : G ⟶ F` of sheaves on a ringed topos: the morphism of topoi is restriction along
postcomposition of sections, and the structure map is the canonical identification of the
inverse image of the structure sheaf of the localization at `F` with that of the localization
at `G`. -/
@[stacks 04J4 "the upper edge `(j, j♯)` of the relocalization triangle"]
noncomputable def relocalizationMorphism (s : G ⟶ F) :
    RingedToposHom (localizedRingedTopos X G) (localizedRingedTopos X F) where
  toToposHom := X.relocalizationMorphismOfTopoi s
  fSharp := (commRingImageAdjunction (X.relocalizationMorphismOfTopoi s)).homEquiv _ _
    (X.relocalizationInverseImageCommRingIso s).hom

/-- **Stacks 04J4.** The structure map of the relocalization, in inverse-image form, is the
canonical identification of the two localized structure sheaves. -/
theorem relocalization_fSharp_inverseImage (s : G ⟶ F) :
    (X.relocalizationMorphism s).fSharpInverseImage =
      (X.relocalizationInverseImageCommRingIso s).hom :=
  Equiv.symm_apply_apply _ _

/-- The structure map of the relocalization of a ringed topos is the identity on underlying
sheaves of sets. -/
theorem fSharpSet_relocalizationMorphism (s : G ⟶ F) :
    RingedToposHom.fSharpSet (X.relocalizationMorphism s) =
      𝟙 ((X.relocalizationMorphism s).toToposHom.inverseImage.obj
        ((localizedRingedTopos X F).forgetRing.obj (localizedRingedTopos X F).O)) :=
  (RingedToposHom.fSharpInverseImage_forget_homEquiv (X.relocalizationMorphism s)).symm.trans
    ((congrArg (localizedRingedTopos X G).forgetRing.map
      (X.relocalization_fSharp_inverseImage s)).trans rfl)

/-- **Stacks 04IH (6).** The morphism
`(j, j♯) : (Sh(C)/G, O_G) → (Sh(C)/F, O_F)` of Stacks 04J4, the relocalization of a ringed topos
along a morphism `s : G ⟶ F` of sheaves, is a morphism of locally ringed topoi: its structure
map is the identity on underlying sheaves of sets and the inverse image of the units subsheaf is
the units subsheaf, so the units square is a square of identities. -/
@[stacks 04IH "(6): the morphism `(j, j♯)` of 04J4 is a morphism of locally ringed topoi"]
theorem relocalizationMorphism_isLocallyRinged (s : G ⟶ F) :
    (X.relocalizationMorphism s).IsLocallyRinged := by
  refine ⟨𝟙 _, ?_⟩
  rw [X.fSharpSet_relocalizationMorphism s]
  exact IsPullback.of_id_fst

end AlgebraicGeometry.RingedTopos

end
