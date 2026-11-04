module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupExceptionalTwistDirectImage

/-!
# The comparison map of a twist is natural in the twist, and a local criterion with one bad point

Let `b : L ⟶ X` be a morphism of schemes. For an `𝒪_L`-module `T` with a global section
`s : 𝒪_L ⟶ T`, `Stacks.DeRham.BlowupTwist.twistUnitComparison b T s : 𝒪_X ⟶ b_*T` is the adjoint
transpose of `s`. This file records two facts used to decide whether such a comparison is an
isomorphism.

The first is that the comparison is **natural in the pair `(T, s)`**: a morphism `φ : T ⟶ T'`
carrying `s` to `s'` carries the comparison at `(T, s)` to the comparison at `(T', s')` by
composing with `b_*φ`. Taking `(T, s) = (𝒪_L, 𝟙)` this exhibits every comparison as the
adjunction unit followed by the direct image of its own section,

`𝒪_X ⟶ b_*𝒪_L ⟶ b_*T`,

which is the factorization the invertibility of a comparison away from the centre of a blowup is
read off from: the naturality makes it unnecessary to restrict the comparison itself, exactly as
in `StacksFrontier/AlgebraicGeometry/ProjectionFormula/Locality.lean`.

The second is a local criterion: a morphism of sheaves of modules on a scheme is invertible as
soon as its restriction to an open is invertible and its stalk at every point outside that open
is. This is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` with the covering
replaced by one open and a set of leftover points, and it is proved the same way, from
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`.

## Main results

* `Stacks.DeRham.BlowupTwist.twistUnitComparison_comp`: **the comparison is natural in the
  section**, `twistUnitComparison b T' (s ≫ φ) = twistUnitComparison b T s ≫ b_*φ`.
* `Stacks.DeRham.BlowupTwist.twistUnitComparison_eq_unit_comp`: **every comparison is the
  comparison at `(𝒪_L, 𝟙)` followed by the direct image of the section.**
* `Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_isIso_stalk_compl`: invertibility from
  invertibility over one open together with the stalks outside it.

## References

* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.DeRham.BlowupTwist

open _root_.RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {L X : Scheme.{u}} (b : L ⟶ X)

/-- **The comparison map is natural in the section.** A morphism `φ : T ⟶ T'` of `𝒪_L`-modules
carries the global section `s` of `T` to the global section `s ≫ φ` of `T'`, and the comparison
map at the latter is the comparison map at the former followed by `b_*φ`.

This is the naturality of the adjoint transpose in its codomain. -/
theorem twistUnitComparison_comp
    {T T' : SheafOfModules.{u} (structureRingSheaf L.toRingedSpace)}
    (s : SheafOfModules.unit (structureRingSheaf L.toRingedSpace) ⟶ T) (φ : T ⟶ T') :
    twistUnitComparison b T' (s ≫ φ) =
      twistUnitComparison b T s ≫ (pushforwardFunctor b.toLRSHom.toShHom).map φ := by
  dsimp only [twistUnitComparison]
  rw [← Category.assoc, (pullbackAdjunction b.toLRSHom.toShHom).homEquiv_naturality_right]

/-- **Every comparison map factors through the comparison map at the structure sheaf.** The
comparison map attached to a global section `s : 𝒪_L ⟶ T` is the comparison map attached to the
identity of `𝒪_L` — that is, the canonical map `𝒪_X ⟶ b_*𝒪_L` — followed by `b_*s`.

Neither factor need be invertible, so this is not a factorization argument for invertibility; it
is the shape in which naturality is applied. -/
theorem twistUnitComparison_eq_unit_comp
    (T : SheafOfModules.{u} (structureRingSheaf L.toRingedSpace))
    (s : SheafOfModules.unit (structureRingSheaf L.toRingedSpace) ⟶ T) :
    twistUnitComparison b T s =
      twistUnitComparison b (SheafOfModules.unit (structureRingSheaf L.toRingedSpace))
          (𝟙 (SheafOfModules.unit (structureRingSheaf L.toRingedSpace))) ≫
        (pushforwardFunctor b.toLRSHom.toShHom).map s := by
  refine Eq.trans (congrArg (twistUnitComparison b T) (Category.id_comp s).symm) ?_
  exact twistUnitComparison_comp b _ s

end Stacks.DeRham.BlowupTwist

namespace Stacks.BlowupTwistUnit

/-- **Invertibility from one open together with the stalks outside it.** A morphism of sheaves of
modules on a scheme whose restriction to an open `V` is invertible and whose stalk at every point
outside `V` is invertible is invertible.

The stalks inside `V` are the stalks of the restriction, by
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`; the rest is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`. -/
theorem isIso_of_isIso_restrict_of_isIso_stalk_compl {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (V : X.Opens)
    (hV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ))
    (h : ∀ x : X, x ∉ V → IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) :
    IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun x ↦ ?_
  by_cases hx : x ∈ V
  · have key : ∀ y : V.toScheme, IsIso ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι y)).map φ) := by
      intro y
      have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := hV
      have h3 : IsIso ((Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
        Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y) _
      have h2 : IsIso ((Scheme.Modules.restrictStalkNatIso V.ι y).hom.app M ≫
          (Scheme.Modules.toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι y)).map φ) := by
        rw [← (Scheme.Modules.restrictStalkNatIso V.ι y).hom.naturality φ]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((Scheme.Modules.restrictStalkNatIso V.ι y).hom.app M) _
    exact key ⟨x, hx⟩
  · exact h x hx

end Stacks.BlowupTwistUnit

end
