module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Opposites
public import StacksCore.Tactic.StacksAttribute

/-!
# `Spec 𝒪_{X, x}` is the inverse limit of the affine open neighbourhoods of `x`

Let `X` be a scheme and `x` a point of it.  The affine open neighbourhoods of `x`, ordered by
inclusion, form a cofiltered category, and the open immersions between them form a diagram of
schemes whose transition maps are affine and whose objects are quasi-compact and quasi-separated.
This file proves that `Spec 𝒪_{X, x}`, with the canonical maps
`Mathlib.AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem` as its legs, is the inverse limit of
that diagram, and that the preimage in it of an open of `X` is the limit of the corresponding
preimages.

The route is `Spec`-of-a-colimit.  The stalk is by definition the colimit of the sections over
*all* open neighbourhoods of `x`, and the affine ones are cofinal among those because the affine
opens form a basis, so the sections over the affine open neighbourhoods also have the stalk as
their colimit.  The functor `Spec` is a right adjoint, hence turns that colimit of rings into a
limit of schemes, and `IsAffineOpen.isoSpec` identifies the resulting diagram
`W ↦ Spec Γ(X, W)` with the diagram `W ↦ W` of open subschemes.  The two lemmas that make this
identification natural and compatible with the legs are `Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`
for the naturality square and `Scheme.Opens.fromSpecStalkOfMem_toSpecΓ` for the legs.

## Main definitions

* `AlgebraicGeometry.affineOpenNhds`: being affine, as a property of an open neighbourhood of `x`.
* `AlgebraicGeometry.affineOpenNhdsDiagram`: the diagram of affine open neighbourhoods of `x` and
  the open immersions between them.
* `AlgebraicGeometry.affineOpenNhdsRingDiagram`: the diagram of their rings of sections.
* `AlgebraicGeometry.specStalkCone`: the cone with apex `Spec 𝒪_{X, x}` over the first diagram.

## Main results

* `AlgebraicGeometry.isColimitGermCocone`: the sections over the affine open neighbourhoods of `x`
  have the stalk at `x` as their colimit.
* `AlgebraicGeometry.isLimitSpecStalkCone`: `Spec 𝒪_{X, x}` is the inverse limit of the affine open
  neighbourhoods of `x`.
* `AlgebraicGeometry.isLimitOpensSpecStalkCone`: the preimage in `Spec 𝒪_{X, x}` of an open of `X`
  is the inverse limit of its preimages in the affine open neighbourhoods of `x`.

## Implementation notes

The index category is the full subcategory of `TopologicalSpace.OpenNhds x` on the affine opens,
rather than a hand-rolled poset, so that cofinality is an instance of
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful` and the colimit
comparison is `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`.  Because
`AlgebraicGeometry.Scheme.Opens` is a reducible abbreviation for `TopologicalSpace.Opens`, dot
notation on `W.obj.1` resolves into the wrong namespace, and the coercion out of `OpenNhds x`
is not type-correct at `rw`'s transparency; both are handled by naming the scheme-side
declarations explicitly and by stating the pointwise lemmas over an explicit `U : X.Opens`.

## References

* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (x : X)

/-- The property, of an open neighbourhood of `x`, of being affine. -/
def affineOpenNhds : ObjectProperty (OpenNhds x) := fun U ↦ IsAffineOpen U.1

/-- The affine open neighbourhoods of `x`, as a full subcategory of all of them. -/
abbrev AffineOpenNhds := (affineOpenNhds X x).FullSubcategory

/-- Every open neighbourhood of `x` contains an affine one. -/
theorem exists_affineOpenNhds_le (U : OpenNhds x) :
    ∃ W : AffineOpenNhds X x, W.obj ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset U.2
  exact ⟨⟨⟨W, hxW⟩, hW⟩, hWU⟩

/-- The affine open neighbourhoods of `x` are initial among all open neighbourhoods of `x`. -/
instance : (affineOpenNhds X x).ι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun U ↦ by
    obtain ⟨W, hW⟩ := exists_affineOpenNhds_le X x U
    exact ⟨W, ⟨homOfLE hW⟩⟩

/-- The opposite of the inclusion of the affine open neighbourhoods of `x` is final. -/
instance : (affineOpenNhds X x).ι.op.Final :=
  Functor.final_op_of_initial _

/-- The diagram of affine open neighbourhoods of `x`, as schemes. -/
noncomputable def affineOpenNhdsDiagram : AffineOpenNhds X x ⥤ Scheme.{u} :=
  (affineOpenNhds X x).ι ⋙ OpenNhds.inclusion x ⋙ X.restrictFunctor ⋙ Over.forget X

/-- The diagram of affine open neighbourhoods sends `W` to the open subscheme `W`. -/
@[simp]
theorem affineOpenNhdsDiagram_obj (W : AffineOpenNhds X x) :
    (affineOpenNhdsDiagram X x).obj W = Scheme.Opens.toScheme (X := X) W.obj.1 :=
  rfl

/-- The diagram of affine open neighbourhoods sends an inclusion `W ≤ W'` to the open immersion
`X.homOfLE`. -/
@[simp]
theorem affineOpenNhdsDiagram_map {W W' : AffineOpenNhds X x} (f : W ⟶ W') :
    (affineOpenNhdsDiagram X x).map f =
      X.homOfLE (show W.obj.1 ≤ W'.obj.1 from leOfHom ((affineOpenNhds X x).ι.map f)) :=
  rfl

/-- The diagram of rings of sections on the affine open neighbourhoods of `x`. -/
def affineOpenNhdsRingDiagram : (AffineOpenNhds X x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineOpenNhds X x).ι.op ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf

/-- The cocone of germ maps from the sections over the affine open neighbourhoods of `x` to the
stalk at `x`. -/
noncomputable def germCocone : Cocone (affineOpenNhdsRingDiagram X x) :=
  (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker (affineOpenNhds X x).ι.op

/-- The sections over the affine open neighbourhoods of `x` have the stalk at `x` as their
colimit. -/
noncomputable def isColimitGermCocone : IsColimit (germCocone X x) :=
  (Functor.Final.isColimitWhiskerEquiv (affineOpenNhds X x).ι.op _).symm (colimit.isColimit _)

/-- The cone exhibiting `Spec 𝒪_{X, x}` over the affine open neighbourhoods of `x`, with legs the
canonical maps `Spec 𝒪_{X, x} ⟶ W`. -/
noncomputable def specStalkCone : Cone (affineOpenNhdsDiagram X x) where
  pt := Spec (X.presheaf.stalk x)
  π :=
  { app := fun W ↦ Scheme.Opens.fromSpecStalkOfMem (X := X) W.obj.1 x W.obj.2
    naturality := fun W W' f ↦ by
      dsimp
      rw [Category.id_comp, ← cancel_mono (Scheme.Opens.ι (X := X) W'.obj.1), Category.assoc,
        Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι] }

/-- The leg of `AlgebraicGeometry.specStalkCone` at `W` is the canonical map
`Spec 𝒪_{X, x} ⟶ W`. -/
@[simp]
theorem specStalkCone_π_app (W : AffineOpenNhds X x) :
    (specStalkCone X x).π.app W =
      Scheme.Opens.fromSpecStalkOfMem (X := X) W.obj.1 x W.obj.2 :=
  rfl

/-- An object of the diagram of affine open neighbourhoods is an affine open. -/
theorem isAffineOpen_affineOpenNhds (W : AffineOpenNhds X x) :
    IsAffineOpen (X := X) W.obj.1 :=
  W.property

/-- Every point has an affine open neighbourhood. -/
instance : Nonempty (AffineOpenNhds X x) :=
  let ⟨W, _⟩ := exists_affineOpenNhds_le X x ⊤
  ⟨W⟩

/-- The category of affine open neighbourhoods of `x` is cofiltered. -/
instance : IsCofiltered (AffineOpenNhds X x) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (affineOpenNhds X x).ι fun U ↦ by
    obtain ⟨W, hW⟩ := exists_affineOpenNhds_le X x U
    exact ⟨W, ⟨homOfLE hW⟩⟩

/-- Each object of the diagram of affine open neighbourhoods is an affine scheme. -/
instance isAffine_affineOpenNhdsDiagram_obj (W : AffineOpenNhds X x) :
    IsAffine ((affineOpenNhdsDiagram X x).obj W) :=
  W.property

/-- The transition maps of the diagram of affine open neighbourhoods are affine. -/
instance isAffineHom_affineOpenNhdsDiagram_map {W W' : AffineOpenNhds X x} (f : W ⟶ W') :
    IsAffineHom ((affineOpenNhdsDiagram X x).map f) :=
  inferInstance

/-- Each object of the diagram of affine open neighbourhoods is quasi-compact. -/
instance compactSpace_affineOpenNhdsDiagram_obj (W : AffineOpenNhds X x) :
    CompactSpace ((affineOpenNhdsDiagram X x).obj W) :=
  inferInstance

/-- Each object of the diagram of affine open neighbourhoods is quasi-separated. -/
instance quasiSeparatedSpace_affineOpenNhdsDiagram_obj (W : AffineOpenNhds X x) :
    QuasiSeparatedSpace ((affineOpenNhdsDiagram X x).obj W) :=
  inferInstance

/-- The diagram of affine open neighbourhoods of `x` is isomorphic to `Spec` of the diagram of
their rings of sections, with component `W ≅ Spec Γ(X, W)` at `W`. -/
noncomputable def affineOpenNhdsDiagramIso :
    affineOpenNhdsDiagram X x ≅ (affineOpenNhdsRingDiagram X x).rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun W ↦ (isAffineOpen_affineOpenNhds X x W).isoSpec)
    (fun {W W'} f ↦ (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map (X := X) W.obj.1 W'.obj.1
      (leOfHom ((affineOpenNhds X x).ι.map f))).symm)

/-- The canonical map `Spec 𝒪_{X, x} ⟶ U` for an affine open neighbourhood `U` of `x` is, under
the identification `U ≅ Spec Γ(X, U)`, the map induced by the germ map. -/
theorem specMap_germ_isoSpec_inv {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) :
    Spec.map (X.presheaf.germ U x hxU) ≫ hU.isoSpec.inv = U.fromSpecStalkOfMem x hxU := by
  rw [Iso.comp_inv_eq]
  exact (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U x hxU).symm

/-- **`Spec 𝒪_{X, x}` is the inverse limit of the affine open neighbourhoods of `x`**, the limit
being taken in the category of schemes over the diagram of open immersions between them. -/
noncomputable def isLimitSpecStalkCone : IsLimit (specStalkCone X x) := by
  haveI : PreservesLimitsOfSize.{0, u} Scheme.Spec.{u} :=
    ΓSpec.adjunction.rightAdjoint_preservesLimits
  have h := isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone (affineOpenNhdsRingDiagram X x) (isColimitGermCocone X x))
  refine IsLimit.ofIsoLimit
    ((IsLimit.postcomposeInvEquiv (affineOpenNhdsDiagramIso X x) _).symm h)
    (Cone.ext (Iso.refl _) fun W ↦ ?_)
  obtain ⟨⟨U, hxU⟩, hU⟩ := W
  exact (specMap_germ_isoSpec_inv X x hU hxU).trans (Category.id_comp _).symm

/-! ### Preimages of opens as limits

The preimage in `Spec 𝒪_{X, x}` of an open `V ⊆ X` is the inverse limit of its preimages in the
affine open neighbourhoods of `x`; for `V = X \ {x}` with `x` closed this is the *punctured*
local scheme. -/

/-- The preimage in `Spec 𝒪_{X, x}` of `V ∩ U`, taken along the canonical map to an open
neighbourhood `U` of `x`, is the preimage of `V` along `X.fromSpecStalk x`. -/
theorem fromSpecStalkOfMem_preimage {U : X.Opens} (hxU : x ∈ U) (V : X.Opens) :
    U.fromSpecStalkOfMem x hxU ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = X.fromSpecStalk x ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- The preimage in `Spec 𝒪_{X, x}` of an open `V` of `X` is the apex of the cone obtained from
`AlgebraicGeometry.specStalkCone` by restricting to `V` at an affine open neighbourhood `W₀`. -/
theorem specStalkCone_π_preimage (W₀ : AffineOpenNhds X x) (V : X.Opens) :
    (specStalkCone X x).π.app W₀ ⁻¹ᵁ (Scheme.Opens.ι (X := X) W₀.obj.1 ⁻¹ᵁ V) =
      X.fromSpecStalk x ⁻¹ᵁ V :=
  fromSpecStalkOfMem_preimage X x W₀.obj.2 V

/-- **The preimage of an open `V ⊆ X` in `Spec 𝒪_{X, x}` is the limit of its preimages in the
affine open neighbourhoods of `x` contained in a fixed one.** -/
noncomputable def isLimitOpensSpecStalkCone (W₀ : AffineOpenNhds X x) (V : X.Opens) :
    IsLimit (opensCone (affineOpenNhdsDiagram X x) (specStalkCone X x) W₀
      (Scheme.Opens.ι (X := X) W₀.obj.1 ⁻¹ᵁ V)) :=
  isLimitOpensCone (affineOpenNhdsDiagram X x) (specStalkCone X x) (isLimitSpecStalkCone X x) W₀ _

end AlgebraicGeometry

end
