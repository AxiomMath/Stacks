module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact
public import StacksFrontier.Topology.Simplicial.Augmentation
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Higher direct images along an augmentation of a simplicial space

Let `X` be a simplicial topological space, let `a : X ⟶ Y` be an augmentation towards a
topological space `Y`, and let `F` be an abelian sheaf on the site `X_Zar` of simplicial opens.
The direct image of abelian sheaves along the morphism of topoi of Stacks 09W4 is left exact,
and Stacks 0D84 computes its right derived functors: `Rⁿa_*F` is the sheaf associated to the
presheaf

`V ↦ Hⁿ((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`.

This module builds the direct image on abelian sheaves and the presheaf of its right derived
functors, and identifies `Rⁿa_*F` with the sheaf associated to that presheaf.  The source
builds the displayed presheaf out of the simplicial space `X ×_Y V`; here it is built out of
the direct image itself, which by part (2) of the source proof is the rule
`V ↦ H⁰((X ×_Y V)_Zar, F|)`.  The link to the fibres is recorded in degree zero only, in the
form in which the source proof uses it: the sections of `a_*F` over `V` are the equalizer of
the two maps between the sections of `F` over the simplicial opens `X_0 ×_Y V = a_0⁻¹(V)` and
`X_1 ×_Y V = a_1⁻¹(V)`.

## Main definitions

* `Stacks.Topology.Simplicial.augmentationPushforwardAb`: the direct image `a_*` of abelian
  sheaves along the augmentation.
* `Stacks.Topology.Simplicial.augmentationPushforwardAbPresheaf`: the presheaf of abelian
  groups `V ↦ (a_*F)(V)` underlying it.
* `Stacks.Topology.Simplicial.augmentationFibreSections`: the sections of the direct image over
  a fixed open of the target, as a functor of the abelian sheaf.
* `Stacks.Topology.Simplicial.augmentationCohomologyPresheaf`: the presheaf whose value over
  `V` is the `n`-th right derived functor of those sections.

## Main results

* `Stacks.Topology.Simplicial.higherDirectImage_iso_sheafify_augmentationCohomologyPresheaf`:
  the `n`-th higher direct image is the sheaf associated to that presheaf.
* `Stacks.Topology.Simplicial.augmentationCohomologyPresheaf_evaluation_iso`: its value over
  `V` is the `n`-th right derived functor of the sections over `V`.
* `Stacks.Topology.Simplicial.augmentationPushforwardAb_forget_isoEqualizer`: in degree zero,
  the underlying sheaf of sets of `a_*F` is the equalizer of the two maps induced by the
  vertices of the one-simplex between the direct images of the degree-zero and degree-one
  components of `F`.

## Implementation notes

The direct image on abelian sheaves is the one attached to an arbitrary morphism of topoi by
Stacks 04DA, applied to the morphism of topoi of Stacks 09W4; it is therefore right adjoint to
the inverse image of abelian sheaves, which is what pins it down.  Being a right adjoint it
preserves limits, hence is additive, so its right derived functors exist.

Deriving before sheafifying is what retains all restriction maps canonically, exactly as in
the analogous Stacks 01E4 and Stacks 072W: the cohomology presheaf is the right derived functor
of the *presheaf*-valued direct image, so the presheaf and all of its restriction maps are
assembled before any sheafification happens.  The identification of the higher direct image
with the associated sheaf is then exactness of sheafification, and the identification of the
values of the presheaf is exactness of evaluation at an open.

What is **not** proved here is the identification of the sections of `a_*F` over `V`, and of
their right derived functors, with the cohomology of the restriction of `F` to the site of the
simplicial space `X ×_Y V`.  That is parts (1), (2b), (2c) and (2d) of the source proof: it
needs the simplicial space `X ×_Y V`, its site, the restriction functor to it, and the fact
that this restriction is exact and carries injective abelian sheaves to injective abelian
sheaves.  The degree-zero fibrewise content that the source proof does use, its part (2a), is
recorded on underlying sheaves of sets in
`Stacks.Topology.Simplicial.augmentationPushforwardAb_forget_isoEqualizer`.

The displayed isomorphisms are stated as `Nonempty` of an isomorphism wherever the comparison
is produced from a chosen injective resolution, which is the form the analogous Stacks 072W
statement takes in this library.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y)

/-- The morphism of topoi of an augmentation of a simplicial space, read as a morphism between
topoi of sheaves on sites rather than on a simplicial space and a space. -/
def augmentationMorphismOfTopoi : MorphismOfTopoi
    (Sheaf (SimplicialOpen.grothendieckTopology X) (Type u))
    (Sheaf (Opens.grothendieckTopology Y) (Type u)) :=
  (augmentationMorphism X Y a).toMorphismOfTopoi

/-- The direct image `a_*` of abelian sheaves along an augmentation of a simplicial space: the
direct image of abelian sheaves of Stacks 04DA along the morphism of topoi of Stacks 09W4.  It
is right adjoint to the inverse image of abelian sheaves. -/
def augmentationPushforwardAb :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) Ab.{u} :=
  Stacks.Topos.AbelianPushforward.abelianPushforward _ (augmentationMorphismOfTopoi X Y a)

/-- The inverse image of abelian sheaves along the augmentation is left adjoint to `a_*`. -/
def augmentationInverseImageAbAdjPushforward :
    CategoryTheory.Sites.abelianInverseImage (augmentationMorphismOfTopoi X Y a) ⊣
      augmentationPushforwardAb X Y a :=
  Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward _ _

/-- The direct image of abelian sheaves along an augmentation preserves limits, being a right
adjoint; in particular it is left exact. -/
theorem preservesLimitsOfSize_augmentationPushforwardAb :
    PreservesLimitsOfSize.{0, 0} (augmentationPushforwardAb X Y a) :=
  Stacks.Topos.AbelianPushforward.preservesLimitsOfSize_abelianPushforward _ _

/-- The direct image `a_*` of abelian sheaves along an augmentation is an additive functor. -/
instance augmentationPushforwardAb_additive :
    (augmentationPushforwardAb X Y a).Additive := by
  have := preservesLimitsOfSize_augmentationPushforwardAb X Y a
  exact Functor.additive_of_preserves_binary_products _

/-- The presheaf of abelian groups `V ↦ (a_*F)(V)` underlying the direct image of an abelian
sheaf along an augmentation.  By part (2) of the proof of Stacks 0D84 this is the rule
`V ↦ H⁰((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`. -/
def augmentationPushforwardAbPresheaf :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤ (Opens Y)ᵒᵖ ⥤ Ab.{u} :=
  augmentationPushforwardAb X Y a ⋙ sheafToPresheaf (Opens.grothendieckTopology Y) Ab.{u}

/-- The presheaf-valued direct image of abelian sheaves along an augmentation is an additive
functor. -/
instance augmentationPushforwardAbPresheaf_additive :
    (augmentationPushforwardAbPresheaf X Y a).Additive := by
  have := augmentationPushforwardAb_additive X Y a
  dsimp only [augmentationPushforwardAbPresheaf]
  infer_instance

/-- The sections over a fixed open `V` of the target of the direct image of an abelian sheaf
along an augmentation, as a functor of the abelian sheaf.  By part (2) of the proof of
Stacks 0D84 this is the functor `F ↦ H⁰((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`. -/
def augmentationFibreSections (V : Opens Y) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤ Ab.{u} :=
  augmentationPushforwardAbPresheaf X Y a ⋙
    (evaluation (Opens Y)ᵒᵖ Ab.{u}).obj (op V)

/-- The sections over an open `V` of the direct image along an augmentation form an additive
functor of the abelian sheaf. -/
instance augmentationFibreSections_additive (V : Opens Y) :
    (augmentationFibreSections X Y a V).Additive := by
  have := augmentationPushforwardAbPresheaf_additive X Y a
  dsimp only [augmentationFibreSections]
  infer_instance

section Derived

variable [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{u}]
  [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u})]

/-- The cohomology presheaf of an augmentation: the `n`-th right derived functor of the
presheaf-valued direct image.  Its value over an open `V` of the target is the `n`-th right
derived functor of the sections of the direct image over `V`, which by part (2) of the proof of
Stacks 0D84 is `Hⁿ((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`.  All opens and all restriction maps are
assembled before deriving, so the presheaf carries its restriction maps canonically. -/
def augmentationCohomologyPresheaf (n : ℕ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤ (Opens Y)ᵒᵖ ⥤ Ab.{u} :=
  (augmentationPushforwardAbPresheaf X Y a).rightDerived n

section Sheafify

variable [HasSheafify (Opens.grothendieckTopology Y) Ab.{u}]

/-- The direct image of abelian sheaves along an augmentation is the sheaf associated to its
own underlying presheaf. -/
def augmentationPushforwardAbIsoSheafify :
    augmentationPushforwardAb X Y a ≅
      augmentationPushforwardAbPresheaf X Y a ⋙
        presheafToSheaf (Opens.grothendieckTopology Y) Ab.{u} :=
  Functor.isoWhiskerLeft (augmentationPushforwardAb X Y a)
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology Y) Ab.{u}).counit).symm

/-- **Stacks 0D84.** Let `X` be a simplicial space, let `a : X ⟶ Y` be an augmentation and let
`F` be an abelian sheaf on `X_Zar`.  Then the `n`-th higher direct image `Rⁿa_*F` is the sheaf
associated to the cohomology presheaf of the augmentation, whose value over an open `V` of `Y`
is `Hⁿ((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`.

Sheafification is exact, so it commutes with the right derived functors of the presheaf-valued
direct image; the higher direct image is the right derived functor of the sheaf-valued one,
which is the sheafification of the presheaf-valued one. -/
@[stacks 0D84 "the sheafification of the cohomology presheaf; not its fibrewise values"]
theorem higherDirectImage_iso_sheafify_augmentationCohomologyPresheaf (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    Nonempty (((augmentationPushforwardAb X Y a).rightDerived n).obj F ≅
      (presheafToSheaf (Opens.grothendieckTopology Y) Ab.{u}).obj
        ((augmentationCohomologyPresheaf X Y a n).obj F)) := by
  have e₀ := (ModuleSheafCohomology.rightDerivedIso
    (augmentationPushforwardAbIsoSheafify X Y a) n).app F
  obtain ⟨e₁⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (augmentationPushforwardAbPresheaf X Y a)
    (presheafToSheaf (Opens.grothendieckTopology Y) Ab.{u}) n F
  exact ⟨e₀ ≪≫ e₁.symm⟩

end Sheafify

/-- **Stacks 0D84.** The value over an open `V` of the target of the cohomology presheaf of an
augmentation is the `n`-th right derived functor of the sections of the direct image over `V`.
By part (2) of the source proof the latter functor is `F ↦ H⁰((X ×_Y V)_Zar, F|)`, so this is
the displayed rule `V ↦ Hⁿ((X ×_Y V)_Zar, F|)` of the statement.

Evaluation of a presheaf of abelian groups at an open is exact, so it commutes with right
derived functors. -/
@[stacks 0D84 "those values as derived sections of the direct image, not as fibre cohomology"]
theorem augmentationCohomologyPresheaf_evaluation_iso (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) (V : Opens Y) :
    Nonempty (((augmentationCohomologyPresheaf X Y a n).obj F).obj (op V) ≅
      ((augmentationFibreSections X Y a V).rightDerived n).obj F) := by
  exact Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (augmentationPushforwardAbPresheaf X Y a)
    ((evaluation (Opens Y)ᵒᵖ Ab.{u}).obj (op V)) n F

end Derived

/-- **Stacks 0D84, part (2a) of the proof.** The underlying sheaf of sets of the direct image
`a_*F` of an abelian sheaf along an augmentation is the equalizer of the two maps induced by
the vertices of the one-simplex between the direct images of the degree-zero and the
degree-one components of `F`.

Over an open `V` of the target the two sheaves of that equalizer have sections the sections of
`F` over the simplicial opens `a_0⁻¹(V)` and `a_1⁻¹(V)`, which are the degree-zero and
degree-one components of the simplicial space `X ×_Y V`.  This is the fibrewise description of
the sections of `a_*F` used in the source proof. -/
@[stacks 0D84 "degree zero: the direct image as an equalizer of fibrewise direct images"]
def augmentationPushforwardAb_forget_isoEqualizer
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    (sheafCompose (Opens.grothendieckTopology Y) (forget Ab.{u})).obj
        ((augmentationPushforwardAb X Y a).obj F) ≅
      equalizer
        (augmentationFaceMap X Y a
          ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).obj F) 0)
        (augmentationFaceMap X Y a
          ((sheafCompose (SimplicialOpen.grothendieckTopology X) (forget Ab.{u})).obj F) 1) :=
  (Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso
      (SimplicialOpen.grothendieckTopology X) (augmentationMorphismOfTopoi X Y a)).app F ≪≫
    augmentationMorphism_pushforwardEqualizer X Y a _

end Stacks.Topology.Simplicial

end
