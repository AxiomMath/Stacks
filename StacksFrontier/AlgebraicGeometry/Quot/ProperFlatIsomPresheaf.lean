module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertGraphIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFibreSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceFibreAlgebraicSpace

/-!
# The isomorphism presheaf of a fibre of the stack of proper flat families

For a scheme `U` of the big fppf site of `S` and two objects `x`, `y` of the fibre of
`Spaces'_{fp, flat, proper}` over `U`, this file identifies the isomorphism presheaf `Isom(x, y)`
of **Stacks 02ZB** on `(Sch/U)` with the fibre over the tautological section of the subfunctor
`Isom_U(Z, X) ⊆ Mor_U(Z, X)` of **Stacks 0DPP**, where `Z` and `Y` are the algebraic spaces
carrying `x` and `y`. Both presheaves have the same sections over `b : V ⟶ U`: a relative
morphism of **Stacks 05Y1** from `Z` to `X` over `h_U` whose first component is `h_b` and whose
morphism of base changes is invertible, by
`AlgebraicGeometry.ProperFlatFibre.relativeSection_injective` and
`AlgebraicGeometry.ProperFlatFibre.relativeSection_surjective`.

That identification is criterion (2) of **Stacks 045G** in the shape
`AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf` asks for it, so together with the openness
of `Isom_U(Z, X)` inside `Mor_U(Z, X)` — Stacks 0DPP — and with the slice-fibre construction of
**Stacks 04SG** it gives **Stacks 0D1F**, the representability of the diagonal of
`Spaces'_{fp, flat, proper}`, on the single remaining input of Stacks 0D1C, which is Stacks 0D01.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.isomSub`: `Isom_U(Z, X) ⊆ Mor_U(Z, X)` of Stacks 0DPP at two
  objects of the fibre.
* `AlgebraicGeometry.ProperFlatFibre.isomFibre`: its fibre over the tautological section of `h_U`,
  a presheaf on `(Sch/U)`.
* `AlgebraicGeometry.ProperFlatFibre.isomSection`: the section of `isomFibre` attached to a
  section of `Isom(x, y)`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isomPresheafIso`: the comparison isomorphism
  `Isom(x, y) ≅ isomFibre x y`, after the universe lifts the statement of criterion (2) of
  Stacks 045G is taken up to.
* `AlgebraicGeometry.Space.isAlgebraicSpaceIsomPresheaf_properFlatSpacesStack`: criterion (2) of
  Stacks 045G for `Spaces'_{fp, flat, proper}`, from Stacks 0D01.
* `AlgebraicGeometry.Space.hasRepresentableDiagonal_properFlatSpacesStack_of_hilb`:
  **Stacks 0D1F** on the single input Stacks 0D01.

## Implementation notes

The route taken is the second one recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Quot/StackOfSpacesDiagonal.lean`: the algebraicity of
`Isom_U(Z, X)` comes from Stacks 0DPP, the isomorphism locus being an *open subspace* of
`Mor_U(Z, X)`, rather than from the fibre product square of the source's own proof. It needs
Stacks 05XD only through `AlgebraicGeometry.Space.hasIsomorphismLocus`, which is proved, so the
only input left is Stacks 0D01, which enters as the algebraicity of `Mor_U(Z, X)`, Stacks 0D1C.

Reading the presheaf `Isom_U(Z, X)` on the big fppf site of `S` as a presheaf on the big fppf
site of `U` is `AlgebraicGeometry.isAlgebraicSpace_iteratedSliceFiber`, the value on an object of
the quasi-inverse of the equivalence of Stacks 04SG.

## References

* [Stacks Project, Tag 0D1F](https://stacks.math.columbia.edu/tag/0D1F)
* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] isFibered

/-- The algebraic space carrying an object of the fibre of the proper flat families is an
algebraic space over `S`. -/
theorem isAlgebraicSpace_space {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    IsAlgebraicSpace B S hS (space x) :=
  x.val.obj.obj.left.property

/-- Postcomposing with the representable image of an identification of base schemes preserves
finite presentation, flatness and properness. -/
private theorem properties_postcomp {V U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ yoneda.obj V) (h : V = U)
    (hf : Space.IsFinitePresentation B S hS f ∧ Space.IsFlat B S hS f ∧
      Space.IsProper B S hS f) :
    Space.IsFinitePresentation B S hS (f ≫ yoneda.map (eqToHom h)) ∧
      Space.IsFlat B S hS (f ≫ yoneda.map (eqToHom h)) ∧
      Space.IsProper B S hS (f ≫ yoneda.map (eqToHom h)) := by
  cases h
  simpa only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id] using hf

/-- **The structure morphism of an object of the fibre over `U` is of finite presentation, flat
and proper.** These are the three conditions defining the objects of Stacks 0D1E, read through
the identification of the base of the object with `U`. -/
theorem str_properties {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    Space.IsFinitePresentation B S hS (str x) ∧ Space.IsFlat B S hS (str x) ∧
      Space.IsProper B S hS (str x) :=
  properties_postcomp _ x.property x.val.obj.property

section Fibre

variable {U : BigFppfOver B S hS} (x y : (cartesianProperFlatProjection B S hS).Fiber U)

/-- `Mor_U(Z, X)` of Stacks 05Y2 for the two algebraic spaces carrying two objects of the fibre of
the proper flat families over `U`. -/
abbrev relHom : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  Space.relativeHom B S hS (space x) (space y) (yoneda.obj U) (str x) (str y)
    (isAlgebraicSpace_space x) (isAlgebraicSpace_space y) (isAlgebraicSpace_yoneda B S hS U)

/-- The identification of the sections of `Mor_U(Z, X)` over a scheme of the site with the pairs
of Stacks 05Y1. -/
abbrev relHomSections (T : BigFppfOver B S hS) :
    (relHom x y).obj (op T) ≃
      Space.RelativeMorphism B S hS (space x) (space y) (yoneda.obj U) (str x) (str y)
        (yoneda.obj T) :=
  Space.relativeHomSections B S hS (space x) (space y) (yoneda.obj U) (str x) (str y)
    (isAlgebraicSpace_space x) (isAlgebraicSpace_space y) (isAlgebraicSpace_yoneda B S hS U) T

/-- **`Isom_U(Z, X) ⊆ Mor_U(Z, X)` of Stacks 0DPP** at two objects of the fibre of the proper flat
families over `U`. -/
abbrev isomSub : Subfunctor (relHom x y) :=
  Space.isomSubfunctor B S hS (space x) (space y) (yoneda.obj U) (str x) (str y)
    (isAlgebraicSpace_space x) (isAlgebraicSpace_space y) (isAlgebraicSpace_yoneda B S hS U)

/-- The projection `Isom_U(Z, X) ⟶ h_U`. -/
abbrev isomProj : (isomSub x y).toFunctor ⟶ yoneda.obj U :=
  (isomSub x y).ι ≫ Space.relativeHomProjection B S hS (space x) (space y) (yoneda.obj U)
    (str x) (str y) (isAlgebraicSpace_space x) (isAlgebraicSpace_space y)
    (isAlgebraicSpace_yoneda B S hS U)

/-- **The fibre of `Isom_U(Z, X)` over the tautological section of `h_U`**, a presheaf on
`(Sch/U)`: its sections over `b : V ⟶ U` are the relative isomorphisms whose first component is
`h_b`. -/
abbrev isomFibre : (Over U)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj U)) (isomProj x y)

/-- **The section of the fibre of `Isom_U(Z, X)` attached to a section of `Isom(x, y)`.** An
isomorphism `b^* x ≅ b^* y` of the fibre over `b.left` gives the relative morphism
`AlgebraicGeometry.ProperFlatFibre.relativeSection`, which is a relative isomorphism with first
component `h_b`. -/
def isomSection (b : Over U)
    (m : ((cartesianProperFlatProjection B S hS).isomPresheaf x y).obj (op b)) :
    (isomFibre x y).obj (op b) := by
  refine ⟨⟨(relHomSections x y b.left).symm (relativeSection x y b m.val), ?_⟩, ?_⟩
  · have : IsIso m.val := m.property
    change (relHomSections x y b.left
      ((relHomSections x y b.left).symm (relativeSection x y b m.val))).IsRelativeIso
    rw [Equiv.apply_symm_apply]
    exact relativeSection_isRelativeIso x y b m.val
  · change (Space.relativeHomProjection B S hS (space x) (space y) (yoneda.obj U) (str x) (str y)
        (isAlgebraicSpace_space x) (isAlgebraicSpace_space y)
        (isAlgebraicSpace_yoneda B S hS U)).app (op b.left)
      ((relHomSections x y b.left).symm (relativeSection x y b m.val)) = b.hom
    rw [Space.relativeHomProjection_app_symm_apply, relativeSection_base]
    exact yonedaEquiv_yoneda_map b.hom

/-- The relative morphism underlying the section of the fibre of `Isom_U(Z, X)` attached to a
section of `Isom(x, y)` is the one the latter was attached to. -/
theorem relHomSections_isomSection (b : Over U)
    (m : ((cartesianProperFlatProjection B S hS).isomPresheaf x y).obj (op b)) :
    relHomSections x y b.left (isomSection x y b m).val.val =
      relativeSection x y b m.val :=
  Equiv.apply_symm_apply _ _

/-- **A section of the fibre of `Isom_U(Z, X)` determines the section of `Isom(x, y)` it comes
from, and every one of them comes from a section of `Isom(x, y)`.** This is
`AlgebraicGeometry.ProperFlatFibre.relativeSection_injective` and
`AlgebraicGeometry.ProperFlatFibre.relativeSection_surjective`, read through the identification of
the sections of `Mor_U(Z, X)` with the pairs of Stacks 05Y1. -/
theorem isomSection_bijective (b : Over U) :
    Function.Bijective (isomSection x y b) := by
  refine ⟨fun m n h => ?_, fun s => ?_⟩
  · refine Subtype.ext (relativeSection_injective x y b ?_)
    rw [← relHomSections_isomSection x y b m, ← relHomSections_isomSection x y b n]
    exact congrArg (fun s => relHomSections x y b.left s.val.val) h
  · have hq : (relHomSections x y b.left s.val.val).IsRelativeIso := s.val.property
    have hb : (relHomSections x y b.left s.val.val).base = yoneda.map b.hom := by
      refine yonedaEquiv.injective ?_
      rw [← Space.relativeHomProjection_app, yonedaEquiv_yoneda_map]
      exact s.property
    obtain ⟨m, hm, he⟩ := relativeSection_surjective x y b
      (relHomSections x y b.left s.val.val) hb hq
    exact ⟨⟨m, hm⟩, Subtype.ext (Subtype.ext ((relHomSections x y b.left).injective
      ((relHomSections_isomSection x y b ⟨m, hm⟩).trans he)))⟩

/-- Attaching a section of the fibre of `Isom_U(Z, X)` to a section of `Isom(x, y)` commutes with
restriction along a morphism of `(Sch/U)`. -/
theorem isomSection_naturality {b c : Over U} (h : b ⟶ c)
    (m : ((cartesianProperFlatProjection B S hS).isomPresheaf x y).obj (op c)) :
    isomSection x y b (((cartesianProperFlatProjection B S hS).isomPresheaf x y).map h.op m) =
      (isomFibre x y).map h.op (isomSection x y c m) := by
  refine Subtype.ext (Subtype.ext ((relHomSections x y b.left).injective ?_))
  rw [relHomSections_isomSection]
  change relativeSection x y b
      (Functor.morRestrict (cartesianProperFlatProjection B S hS) x y h m.val) = _
  rw [relativeSection_restrict]
  change _ = relHomSections x y b.left ((relHom x y).map h.left.op (isomSection x y c m).val.val)
  rw [Space.relativeHomSections_map, relHomSections_isomSection]

/-- **The comparison isomorphism of Stacks 045G (2) for the proper flat families.** The
isomorphism presheaf `Isom(x, y)` of two objects of the fibre over `U` is the fibre of
`Isom_U(Z, X)` over the tautological section of `h_U`, up to the universe lifts the statement of
criterion (2) of Stacks 045G is taken up to. -/
def isomPresheafIso :
    isomFibre x y ⋙ uliftFunctor.{u + 1, u} ≅
      (cartesianProperFlatProjection B S hS).isomPresheaf x y ⋙ uliftFunctor.{u, u + 1} :=
  (NatIso.ofComponents
    (fun W => ((Equiv.ulift.trans (Equiv.ofBijective (isomSection x y W.unop)
      (isomSection_bijective x y W.unop))).trans Equiv.ulift.symm).toIso)
    (by
      intro W W' f
      ext s
      exact ULift.ext (isomSection_naturality x y f.unop s.down))).symm

end Fibre

end AlgebraicGeometry.ProperFlatFibre

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Criterion (2) of Stacks 045G for `Spaces'_{fp, flat, proper}`, from Stacks 0D01.** For a
scheme `U` of the site and two objects `x`, `y` of the fibre over `U`, the isomorphism presheaf
`Isom(x, y)` of Stacks 02ZB is an algebraic space over `U`.

The two objects of the fibre are finitely presented, flat and proper families over `U`, so the
relative morphism functor `Mor_U(Z, X)` is an algebraic space by Stacks 0D1C, with no
hypothesis left — this is where Stacks 05XD enters, discharged by
`AlgebraicGeometry.Space.hasIsomorphismLocus` — and the subfunctor `Isom_U(Z, X)` of relative
isomorphisms is an open subspace of it by Stacks 0DPP, hence an algebraic space over `S`. Reading
it over `U` is `AlgebraicGeometry.isAlgebraicSpace_iteratedSliceFiber`, the value on an object of
the quasi-inverse of the equivalence of Stacks 04SG, and the comparison with `Isom(x, y)` is
`AlgebraicGeometry.ProperFlatFibre.isomPresheafIso`. -/
theorem isAlgebraicSpaceIsomPresheaf_properFlatSpacesStack :
    Stack.IsAlgebraicSpaceIsomPresheaf B S hS (properFlatSpacesStack B S hS) := by
  intro U x y
  have hx := ProperFlatFibre.str_properties x
  have hy := ProperFlatFibre.str_properties y
  have hQ := isAlgebraicSpace_yoneda B S hS U
  have hM : IsAlgebraicSpace B S hS (ProperFlatFibre.relHom x y) :=
    isAlgebraicSpace_relativeHom (ProperFlatFibre.str x) (ProperFlatFibre.str y)
      (ProperFlatFibre.isAlgebraicSpace_space x) (ProperFlatFibre.isAlgebraicSpace_space y) hQ
      hy.1 hy.2.2.1 hx.1 hx.2.1 hx.2.2
  have hI := isOpenSubspace_isomSubfunctor B S hS (ProperFlatFibre.space x)
    (ProperFlatFibre.space y) (yoneda.obj U) (ProperFlatFibre.str x) (ProperFlatFibre.str y)
    (ProperFlatFibre.isAlgebraicSpace_space x) (ProperFlatFibre.isAlgebraicSpace_space y) hQ
    hx.1 hx.2.1 hx.2.2 hy.2.2 hM
  refine ⟨(Over.iteratedSliceBackward U).op ⋙ ProperFlatFibre.isomFibre x y,
    isAlgebraicSpace_iteratedSliceFiber B S hS U (ProperFlatFibre.isomProj x y) hI.1, ⟨?_⟩⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
      (ProperFlatFibre.isomPresheafIso x y) ≪≫ (Functor.associator _ _ _).symm

/-- **Stacks 0D1F.** The diagonal

```text
  Spaces'_{fp, flat, proper} ⟶ Spaces'_{fp, flat, proper} × Spaces'_{fp, flat, proper}
```

is representable by algebraic spaces.

This is criterion (2) of Stacks 045G, `AlgebraicGeometry.Stack
.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`, applied to
`AlgebraicGeometry.Space.isAlgebraicSpaceIsomPresheaf_properFlatSpacesStack`. Against
`AlgebraicGeometry.Space.hasRepresentableDiagonal_properFlatSpacesStack` it drops both the
Stacks 05XD hypothesis and the `Isom`-comparison hypothesis `hcmp`: the first is proved, and the
second is what the comparison of this file supplies.

It takes no hypothesis: the algebraicity of the Hilbert functors of Stacks 0D01 is no longer
needed by `AlgebraicGeometry.Space.isAlgebraicSpaceIsomPresheaf_properFlatSpacesStack`. -/
theorem hasRepresentableDiagonal_properFlatSpacesStack_of_hilb :
    Stack.HasRepresentableDiagonal B S hS (properFlatSpacesStack B S hS) :=
  (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
    (properFlatSpacesStack B S hS)).2
    (isAlgebraicSpaceIsomPresheaf_properFlatSpacesStack B S hS)

end AlgebraicGeometry.Space

end
