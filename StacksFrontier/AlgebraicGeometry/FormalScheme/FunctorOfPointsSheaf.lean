module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcSheaf

/-!
# The functor of points as a faithful embedding, and its sheaf condition

Let `𝔛` be a formal scheme à la EGA. Every formal scheme satisfies the size condition
`AlgebraicGeometry.IsSizeBoundedFormalScheme` for some cutoff cardinal, and the functor of points
on the category of all schemes is faithful. The functor of points of a formal scheme isomorphic to
a scheme satisfies the sheaf condition for fpqc coverings, gluing included; for an arbitrary
formal scheme the fpqc sheaf condition reduces to the existence of amalgamations.

## Main definitions

* `AlgebraicGeometry.formalSchemePointsSchemeEquiv`: the points over `T` of a scheme `Z` seen as a
  formal scheme are the morphisms `T ⟶ Z`.

## Main results

* `AlgebraicGeometry.exists_isSizeBoundedFormalScheme`: every formal scheme satisfies the size
  condition for some cutoff cardinal.
* `AlgebraicGeometry.injective_formalSchemePointsFunctor_map`: a morphism of formal schemes is
  determined by the transformation it induces on functors of points on all schemes.
* `AlgebraicGeometry.faithful_formalSchemePointsFunctor`: the functor of points on the category of
  all schemes is faithful.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_schemeToFormalScheme`: the functor of
  points of a scheme seen as a formal scheme is an fpqc sheaf.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_iso`: the functor of points of a
  formal scheme isomorphic to a scheme is an fpqc sheaf.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_exists_isAmalgamation`: for a
  general formal scheme the fpqc sheaf condition reduces to the existence of amalgamations.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI0](https://stacks.math.columbia.edu/tag/0AI0)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-! ### The size condition is always satisfiable -/

/-- Every formal scheme satisfies the size condition `IsSizeBoundedFormalScheme κ` for some cutoff
cardinal `κ`. -/
theorem exists_isSizeBoundedFormalScheme {X : LTRS.{u}} (hX : IsFormalScheme X) :
    ∃ κ : Cardinal.{u}, IsSizeBoundedFormalScheme κ X := by
  classical
  choose U hU A hlin hadm he using hX
  obtain ⟨κ, -, -, -, hκ⟩ := exists_size_cutoff
    (Set.range fun i : Σ x : ↥X, IdealsOfDefinition (A x).α =>
      Spec (spfQuotient (A i.1).α i.2))
  exact ⟨κ, fun x =>
    ⟨U x, hU x, A x, hlin x, hadm x, fun I => hκ _ ⟨⟨x, I⟩, rfl⟩, he x⟩⟩

/-! ### Faithfulness of the functor of points -/

/-- A morphism of formal schemes is determined by the natural transformation it induces on
functors of points on the category of all schemes. -/
@[stacks 0AI1 "injectivity of the functor of points on morphisms, with no size hypothesis"]
theorem injective_formalSchemePointsFunctor_map {X Y : FormalScheme.{u}} :
    Function.Injective fun f : X ⟶ Y => formalSchemePointsFunctor.map f := by
  obtain ⟨κ, hκ⟩ := exists_isSizeBoundedFormalScheme X.property
  exact fun f g hfg ↦ injective_formalSchemeFunctorOfPoints_map (κ := κ) hκ
    (congrArg ((Functor.whiskeringLeft _ _ _).obj (schemeCutoff κ).ι.op).map hfg)

/-- The functor of points of formal schemes on the category of all schemes is faithful. -/
@[stacks 0AIR "faithfulness of the embedding by the functor of points, on all schemes"]
instance faithful_formalSchemePointsFunctor : formalSchemePointsFunctor.{u}.Faithful where
  map_injective h := injective_formalSchemePointsFunctor_map h

/-! ### The sheaf condition -/

/-- The fpqc sheaf condition for the functor of points of a formal scheme on the category of all
schemes reduces to the existence of an amalgamation for every compatible family of points over
an fpqc covering sieve. -/
theorem isSheaf_fpqcTopology_formalSchemePoints_of_exists_isAmalgamation (X : FormalScheme.{u})
    (hglue : ∀ (T : Scheme.{u}) (R : Sieve T), R ∈ Scheme.fpqcTopology.{u} T →
      ∀ x : Presieve.FamilyOfElements (formalSchemePoints X) R.arrows,
        x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) :=
  fun _ R hR =>
    (isSeparated_fpqcTopology_formalSchemePoints X R hR).isSheafFor (hglue _ R hR)

/-- The points of a scheme `Z` seen as a formal scheme, over a test scheme `T`, are the
morphisms of schemes `T ⟶ Z`. -/
noncomputable def formalSchemePointsSchemeEquiv (Z T : Scheme.{u}) :
    (yoneda.obj Z).obj (op T) ≃ (formalSchemePoints (schemeToFormalScheme.obj Z)).obj (op T) where
  toFun ψ := schemeToFormalScheme.map ψ
  invFun φ := schemeToFormalScheme.preimage φ
  left_inv ψ := schemeToFormalScheme.preimage_map ψ
  right_inv φ := schemeToFormalScheme.map_preimage φ

/-- The functor of points of a scheme seen as a formal scheme satisfies the sheaf condition,
gluing included, for fpqc coverings of schemes. -/
@[stacks 0AI2 "sheaf condition with gluing, for a scheme seen as a formal scheme"]
theorem isSheaf_fpqcTopology_formalSchemePoints_schemeToFormalScheme (Z : Scheme.{u}) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u}
      (formalSchemePoints (schemeToFormalScheme.obj Z)) :=
  Presieve.isSheaf_of_nat_equiv (fun {T} => formalSchemePointsSchemeEquiv Z T)
    (fun _ _ f x => schemeToFormalScheme.map_comp f x)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj Z))

/-- The functor of points of a formal scheme isomorphic to a scheme satisfies the sheaf
condition, gluing included, for fpqc coverings of schemes. -/
@[stacks 0AI2 "sheaf condition with gluing, for a formal scheme isomorphic to a scheme"]
theorem isSheaf_fpqcTopology_formalSchemePoints_of_iso {X : FormalScheme.{u}} {Z : Scheme.{u}}
    (e : X ≅ schemeToFormalScheme.obj Z) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) :=
  Presieve.isSheaf_iso _ (formalSchemePointsFunctor.mapIso e).symm
    (isSheaf_fpqcTopology_formalSchemePoints_schemeToFormalScheme Z)

end AlgebraicGeometry

end
