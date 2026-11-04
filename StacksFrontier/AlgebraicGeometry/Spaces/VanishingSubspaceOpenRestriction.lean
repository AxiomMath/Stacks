module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Restricting the zero locus of global functions to an étale or open subspace

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site, let
`f₁, …, f_r ∈ Γ(X, 𝒪_X)` and let `V(f₁, …, f_r) ⊆ X` be the closed subspace they cut out,
`AlgebraicGeometry.Space.vanishingSubfunctor`.  This file compares that construction with
restriction along a morphism `φ : U ⟶ X`: the functions restrict to functions on `U`, cutting out
`V(f₁|_U, …, f_r|_U) ⊆ U`, and the question is whether that is the inverse image
`φ⁻¹ V(f₁, …, f_r)`.

The file exists to supply the geometric input to a *slicing* argument: an étale chart or an open
subspace `W ⊆ X` is chosen, finitely many functions are produced on it or on `X`, and what the
argument then needs is that cutting the functions out commutes with passing to `W`, so that
`V(f₁, …, f_r) ⊓ W` is the zero locus of the restricted functions computed inside `W`.  That
identification is `AlgebraicGeometry.Space.vanishingSubfunctor_inf_eq_preimage_of_isOpenSubspace`.

## Main definitions

* `AlgebraicGeometry.Space.unitSectionsRestrict`: the restriction of a global regular function
  along an étale morphism of algebraic spaces, as a map of `sections` of the unit module.  This
  is the map the statements below are about and it is not available otherwise: pullback of
  modules along an étale morphism, `AlgebraicGeometry.Space.etaleModulePullback`, is restriction
  of sections along `AlgebraicGeometry.Space.smallEtalePostcomp` with no change of scalars, so a
  global function on `X` restricts to a global function on `U` by reindexing the charts, and no
  comparison map of structure sheaves is involved.

## Main results

* `AlgebraicGeometry.Space.unitSectionValue_restrict` and
  `AlgebraicGeometry.Space.vanishingIdealAt_restrict`: the value of a restricted function on a
  chart `V` of `U` is the value of the original function on the postcomposed chart of `X`, and
  therefore the chart ideal of the restricted family at `V` is the chart ideal of the original
  family at the postcomposed chart.  Both hold by definition.
* `AlgebraicGeometry.Space.vanishingSubfunctor_restrict_le_preimage`: **unconditionally**, the
  zero locus of the restricted functions is contained in the inverse image of the zero locus of
  the functions.
* `AlgebraicGeometry.Space.vanishingSubfunctor_restrict_eq_preimage`: the two are *equal* as soon
  as the defining ideal of `V(f₁, …, f_r)` on the affine étale charts of `X` is the ideal of the
  family; see the implementation notes for why that hypothesis is needed and
  `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq` for how it is met.  It *is*
  met, with no hypothesis, by
  `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq_vanishingIdealAt`, which is
  stated where the quasi-coherence input of Stacks 03MB is in the import closure; and
  `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq_of_isEmpty` gives a family on
  which it holds with no input at all.
* `AlgebraicGeometry.Space.range_vanishingSubfunctor_restrict_le_inf` and
  `AlgebraicGeometry.Space.vanishingSubfunctor_inf_eq_preimage_of_isOpenSubspace`: the same two
  statements for an open subspace `W ⊆ X`, phrased as a comparison of `V(f₁, …, f_r) ⊓ W` with
  the image in `X` of the zero locus of the restricted functions computed inside `W`.
* `CategoryTheory.Subfunctor.image_preimage_ι` and
  `CategoryTheory.Subfunctor.range_preimage_ι_comp_ι`: the subfunctor identity the open-subspace
  form rests on, that the image of an inverse image along the inclusion of a subfunctor is the
  intersection.

## Implementation notes

The containment `V(f₁|_U, …, f_r|_U) ≤ φ⁻¹ V(f₁, …, f_r)` is proved from the *defining family* of
`AlgebraicGeometry.Space.vanishingSubfunctor` rather than from its defining ideal: the inverse
image along `φ` of a closed subspace `Z` of `X` whose chart ideals are bounded by the ideal of the
family is a closed subspace of `U` whose chart ideals are bounded by the ideal of the restricted
family, by `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp` together
with `AlgebraicGeometry.Space.vanishingIdealAt_restrict`, so each member of the family defining
`V(f₁, …, f_r)` pulls back to a member of the family defining `V(f₁|_U, …, f_r|_U)`.  Taking the
infimum over the first family then bounds the second, by
`CategoryTheory.Subfunctor.image_le_iff`.  Nothing about the defining ideal of the infimum itself
is used, and the morphism need only be étale.

The reverse containment is not available *from the infimum construction alone*, and the reason is
the one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/VanishingSubspace.lean`.  Both
`AlgebraicGeometry.Space.le_vanishingSubfunctor` and
`AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le` reduce
`φ⁻¹ V(f₁, …, f_r) ≤ V(f₁|_U, …, f_r|_U)` to the single chartwise containment

`vanishingIdealAt B S hS X f W ≤ definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W)`

over the affine étale charts `W` of `X`, and that containment is exactly the half of Stacks 03MB
which the infimum construction does not give: the infimum is bounded *above* by the ideal of the
family on every chart only after a closed subspace realizing that ideal is known to exist, which
is `AlgebraicGeometry.Space.exists_vanishingSubfunctor_eq_of_isQuasicoherentOnSite`.  That
closed subspace does exist, with no hypothesis, because the sheaf of ideals of the family is
quasi-coherent on the small étale site
(`AlgebraicGeometry.Space.exists_vanishingSubfunctor_eq`), so the hypothesis carried below is
dischargeable; it is carried rather than discharged only because the quasi-coherence is proved
above this file in the import order, and
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq_vanishingIdealAt` discharges it
where both are available.  Nor can the
containment be obtained from the defining family the way the other one is: it would need, for a
closed subspace `Z ⊆ U` whose chart ideals are bounded by the ideal of the restricted family, a
closed subspace `Z' ⊆ X` whose chart ideals are bounded by the ideal of the family and with
`φ⁻¹ Z' ≤ Z`, and no such `Z'` is constructible from `Z` alone — on a chart of `X` missing the
image of `φ` the condition on `Z'` constrains it where `Z` says nothing, and the minimal choice
there is `V(f₁, …, f_r)` itself.  So the hypothesis is carried, exactly as every assertion of
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeProperties.lean` carries the same hypothesis for
the zero scheme of Stacks 0845.

The hypothesis is stated as a property of `AlgebraicGeometry.Space.vanishingSubspace` itself
rather than of an auxiliary closed subspace; the two are interchangeable by
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq`, which turns any closed subspace
with the prescribed chart ideals into the hypothesis, through
`AlgebraicGeometry.Space.vanishingSubfunctor_eq`.

Restriction of global functions is defined for an arbitrary *étale* morphism, which is the
generality in which `AlgebraicGeometry.Space.smallEtalePostcomp` and hence
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp` are available; an
open immersion is étale by `AlgebraicGeometry.Space.isEtale_of_isOpenImmersion`, which is how the
open-subspace form is obtained.  Because postcomposition leaves the underlying scheme of a chart
unchanged, affineness of a chart of `U` and of the postcomposed chart of `X` are the *same*
proposition, `AlgebraicGeometry.Space.isAffine_smallEtalePostcomp_obj_iff`; without that the
chartwise hypotheses of the two infimum bounds could not be matched up, since both quantify over
affine charts only.

## References

* [Stacks Project, Section 06LV](https://stacks.math.columbia.edu/tag/06LV)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category C] {F : C ⥤ Type u}

/-- The image along the inclusion of a subfunctor `G` of the inverse image of a subfunctor `Z`
along that same inclusion is the intersection `Z ⊓ G`: a section of `F` is in the image exactly
when it lies in `G` and lands in `Z`. -/
theorem image_preimage_ι (Z G : Subfunctor F) : (Z.preimage G.ι).image G.ι = Z ⊓ G := by
  ext i x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hxZ, hxG⟩
    exact ⟨⟨x, hxG⟩, hxZ, rfl⟩

/-- The range of the composite of the inclusion of the inverse image `G⁻¹ Z` into `G` with the
inclusion of `G` into `F` is the intersection `Z ⊓ G`. -/
theorem range_preimage_ι_comp_ι (Z G : Subfunctor F) :
    range ((Z.preimage G.ι).ι ≫ G.ι) = Z ⊓ G := by
  rw [range_comp, range_ι, image_preimage_ι]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-! ### Restriction of global regular functions along an étale morphism -/

/-- The restriction along an étale morphism `φ : U ⟶ X` of algebraic spaces of a global regular
function on `X`, as a global regular function on `U`.

Postcomposition with `φ` carries an étale chart of `U` to an étale chart of `X` with the same
underlying scheme, so the value of the restricted function on a chart `V` of `U` is the value of
the original function on the chart `V ⟶ U ⟶ X` of `X`, with no change of scalars; compatibility
with the restriction maps of the structure sheaf is compatibility of the original function at the
postcomposed charts. -/
noncomputable def unitSectionsRestrict (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (a : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    (SheafOfModules.unit (structureRingSheaf B S hS U)).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ a.eval ((smallEtalePostcomp B S hS φ hφ).op.obj V))
    fun {_ _} g ↦ a.property ((smallEtalePostcomp B S hS φ hφ).op.map g)

/-- The value of a restricted global function on an étale chart `V` of `U` is the value of the
original function on the postcomposed chart `V ⟶ U ⟶ X` of `X`. -/
theorem unitSectionValue_restrict (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (a : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (V : (SmallEtale B S hS U.1)ᵒᵖ) :
    unitSectionValue B S hS U (unitSectionsRestrict B S hS φ hφ a) V =
      unitSectionValue B S hS X a (op ((smallEtalePostcomp B S hS φ hφ).obj V.unop)) :=
  rfl

/-- The ideal generated on an étale chart `V` of `U` by a restricted family of global functions is
the ideal generated by the original family on the postcomposed chart `V ⟶ U ⟶ X` of `X`: the two
are ideals of the *same* ring of regular functions, generated by the same elements. -/
theorem vanishingIdealAt_restrict (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (V : SmallEtale B S hS U.1) :
    vanishingIdealAt B S hS U (fun i ↦ unitSectionsRestrict B S hS φ hφ (f i)) V =
      vanishingIdealAt B S hS X f ((smallEtalePostcomp B S hS φ hφ).obj V) :=
  rfl

/-- An étale chart of `U` is affine exactly when the chart of `X` obtained from it by
postcomposition is: the two have the same underlying scheme. -/
theorem isAffine_smallEtalePostcomp_obj_iff (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (V : SmallEtale B S hS U.1) :
    IsAffine ((SmallEtale.toSchemes B S hS X.1).obj
        ((smallEtalePostcomp B S hS φ hφ).obj V)).1 ↔
      IsAffine ((SmallEtale.toSchemes B S hS U.1).obj V).1 :=
  Iff.rfl

/-! ### The zero locus of the restricted functions -/

/-- **The zero locus of the restricted functions is contained in the inverse image of the zero
locus.**  For an étale `φ : U ⟶ X` and global regular functions `f₁, …, f_r` on `X`,

`V(f₁|_U, …, f_r|_U) ≤ φ⁻¹ V(f₁, …, f_r)`.

No hypothesis is needed: the inverse image along `φ` of any closed subspace of `X` whose chart
ideals are bounded by the ideal of `f₁, …, f_r` is a closed subspace of `U` whose chart ideals are
bounded by the ideal of the restricted functions, so `V(f₁|_U, …, f_r|_U)` is contained in the
inverse image of every member of the family whose infimum is `V(f₁, …, f_r)`. -/
theorem vanishingSubfunctor_restrict_le_preimage (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    vanishingSubfunctor B S hS U (fun i ↦ unitSectionsRestrict B S hS φ hφ (f i)) ≤
      (vanishingSubfunctor B S hS X f).preimage φ.hom := by
  rw [← Subfunctor.image_le_iff, vanishingSubfunctor]
  refine le_sInf ?_
  rintro W ⟨hW, hWle⟩
  rw [Subfunctor.image_le_iff]
  refine vanishingSubfunctor_le B S hS U _
    ⟨(⟨W, hW⟩ : ClosedSubspaces B S hS X.1).1.preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom W X.2 U.2 hW⟩ fun V hV ↦
    (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ ⟨W, hW⟩ V).trans_le
      (hWle _ hV)

/-- A closed subspace of `X` whose defining ideal on every affine étale chart is the ideal of
`f₁, …, f_r` makes that identification true of `V(f₁, …, f_r)` itself, since it *is*
`V(f₁, …, f_r)` by `AlgebraicGeometry.Space.vanishingSubfunctor_eq`.

This is how the hypothesis of
`AlgebraicGeometry.Space.vanishingSubfunctor_restrict_eq_preimage` is met; by
`AlgebraicGeometry.Space.exists_vanishingSubfunctor_eq_of_isQuasicoherentOnSite` such a closed
subspace exists as soon as the ideal of the family is the ideal sheaf of a quasi-coherent sheaf of
ideals. -/
theorem definingIdealAt_vanishingSubspace_eq (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (Z : ClosedSubspaces B S hS X.1)
    (hZ : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toSchemes B S hS X.1).obj W).1 →
      definingIdealAt B S hS X Z (op W) = vanishingIdealAt B S hS X f W)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj W).1) :
    definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W) =
      vanishingIdealAt B S hS X f W := by
  rw [show vanishingSubspace B S hS X f = Z from
    Subtype.ext (vanishingSubfunctor_eq B S hS X f Z hZ)]
  exact hZ W hW

/-- **The hypothesis carried below is satisfiable with no appeal to Stacks 03MB.**  For the empty
family it holds on every étale chart, affine or not: the empty family cuts out the whole of `X` by
`AlgebraicGeometry.Space.vanishingSubfunctor_isEmpty`, and the defining ideal of `X` inside itself
is zero, as is the ideal generated by no functions. -/
theorem definingIdealAt_vanishingSubspace_eq_of_isEmpty (X : AlgebraicSpaces B S hS) {r : ℕ}
    [IsEmpty (Fin r)]
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (W : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W) =
      vanishingIdealAt B S hS X f W := by
  have htop : vanishingSubspace B S hS X f = ⟨⊤, isClosedSubspace_top B S hS X⟩ :=
    Subtype.ext (vanishingSubfunctor_isEmpty B S hS X f)
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor X.1).ι) :
      X ⟶ (⟨(⊤ : Subfunctor X.1).toFunctor, (isClosedSubspace_top B S hS X).1⟩ :
        AlgebraicSpaces B S hS)) ≫ ObjectProperty.homMk (⊤ : Subfunctor X.1).ι = 𝟙 X := by
    apply ObjectProperty.hom_ext
    exact IsIso.inv_hom_id _
  rw [htop, vanishingIdealAt_isEmpty B S hS X f W,
    definingIdealAt_eq_bot_of_retraction B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ _ hret (op W)]

/-- **The inverse image of the zero locus is contained in the zero locus of the restricted
functions**, granted the identification of the defining ideal of `V(f₁, …, f_r)` with the ideal of
the family on the affine étale charts of `X`.

That hypothesis is the half of Stacks 03MB which the infimum construction of
`AlgebraicGeometry.Space.vanishingSubfunctor` does not supply, and it is what this containment
needs; see the implementation notes. -/
theorem preimage_vanishingSubfunctor_le_restrict (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (h : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toSchemes B S hS X.1).obj W).1 →
      definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W) =
        vanishingIdealAt B S hS X f W) :
    (vanishingSubfunctor B S hS X f).preimage φ.hom ≤
      vanishingSubfunctor B S hS U (fun i ↦ unitSectionsRestrict B S hS φ hφ (f i)) := by
  refine le_vanishingSubfunctor B S hS U _
    ⟨(vanishingSubspace B S hS X f).1.preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom (vanishingSubspace B S hS X f).1 X.2 U.2
        (vanishingSubspace B S hS X f).2⟩ fun V hV ↦
    (h ((smallEtalePostcomp B S hS φ hφ).obj V) hV).ge.trans_eq
      (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ
        (vanishingSubspace B S hS X f) V).symm

/-- **Cutting out finitely many global functions commutes with restriction along an étale
morphism**, granted the identification of the defining ideal of `V(f₁, …, f_r)` with the ideal of
the family on the affine étale charts of `X`:

`V(f₁|_U, …, f_r|_U) = φ⁻¹ V(f₁, …, f_r)`.

One containment, `AlgebraicGeometry.Space.vanishingSubfunctor_restrict_le_preimage`, holds with no
hypothesis at all; the hypothesis is used only for the other one, by
`AlgebraicGeometry.Space.preimage_vanishingSubfunctor_le_restrict`. -/
theorem vanishingSubfunctor_restrict_eq_preimage (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (h : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toSchemes B S hS X.1).obj W).1 →
      definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W) =
        vanishingIdealAt B S hS X f W) :
    vanishingSubfunctor B S hS U (fun i ↦ unitSectionsRestrict B S hS φ hφ (f i)) =
      (vanishingSubfunctor B S hS X f).preimage φ.hom :=
  le_antisymm (vanishingSubfunctor_restrict_le_preimage B S hS φ hφ f)
    (preimage_vanishingSubfunctor_le_restrict B S hS φ hφ f h)

/-! ### The zero locus inside an open subspace -/

/-- **The zero locus of the restricted functions inside an open subspace is contained in the
intersection with it.**  For an open subspace `W ⊆ X` and global regular functions `f₁, …, f_r` on
`X`, the image in `X` of `V(f₁|_W, …, f_r|_W) ⊆ W` is contained in `V(f₁, …, f_r) ⊓ W`.  No
hypothesis is needed. -/
theorem range_vanishingSubfunctor_restrict_le_inf (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W) :
    Subfunctor.range ((vanishingSubfunctor B S hS (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS)
          (fun i ↦ unitSectionsRestrict B S hS (ObjectProperty.homMk W.ι)
            (isEtale_of_isOpenImmersion B S hS hW.2) (f i))).ι ≫ W.ι) ≤
      vanishingSubfunctor B S hS X f ⊓ W := by
  have hle := vanishingSubfunctor_restrict_le_preimage B S hS
    (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (isEtale_of_isOpenImmersion B S hS hW.2) f
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]
  exact fun i x hx ↦ ⟨hle i hx, x.2⟩

/-- **Cutting out finitely many global functions commutes with restriction to an open subspace**,
granted the identification of the defining ideal of `V(f₁, …, f_r)` with the ideal of the family on
the affine étale charts of `X`: for an open subspace `W ⊆ X`,

`V(f₁, …, f_r) ⊓ W` is the image in `X` of `V(f₁|_W, …, f_r|_W) ⊆ W`.

This is the form a slicing argument consumes: the functions are produced on `X` or on `W`, the
zero locus is computed inside `W`, and this says that doing so loses nothing. -/
theorem vanishingSubfunctor_inf_eq_preimage_of_isOpenSubspace (X : AlgebraicSpaces B S hS)
    {r : ℕ} (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (h : ∀ V : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toSchemes B S hS X.1).obj V).1 →
      definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op V) =
        vanishingIdealAt B S hS X f V) :
    vanishingSubfunctor B S hS X f ⊓ W =
      Subfunctor.range ((vanishingSubfunctor B S hS
          (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS)
          (fun i ↦ unitSectionsRestrict B S hS (ObjectProperty.homMk W.ι)
            (isEtale_of_isOpenImmersion B S hS hW.2) (f i))).ι ≫ W.ι) := by
  rw [vanishingSubfunctor_restrict_eq_preimage B S hS
      (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (isEtale_of_isOpenImmersion B S hS hW.2) f h,
    ObjectProperty.homMk_hom, Subfunctor.range_preimage_ι_comp_ι]

end AlgebraicGeometry.Space

end
