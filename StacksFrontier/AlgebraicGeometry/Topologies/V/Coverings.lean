module

public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# V coverings

A family of morphisms of schemes is a V covering when, over every affine open of the
target, the pullback of the family is refined by a finite family of affine schemes which is
a standard V covering.  A set-valued presheaf on schemes is a V sheaf when it satisfies the
sheaf condition for every V covering family.

## Main definitions

* `AlgebraicGeometry.IsVCovering`: the predicate that a family of morphisms of schemes is a
  V covering.
* `AlgebraicGeometry.IsVSheaf`: the predicate that a presheaf is a sheaf for the V
  topology.

## Implementation notes

The definition is affine-local on the target: over each affine open `U` the family is
pulled back along `U.ι` and compared, by a morphism of pre-zero-hypercovers, with a finite
affine family which is a standard V covering of `U`.  The finiteness and affineness data
are carried explicitly, because `AlgebraicGeometry.IsStandardVCovering` takes them as
instance arguments.  The V topology is not presented as a precoverage here; the sheaf
condition is stated directly for the presieve of each V covering family.

## References

* [Stacks Project, Tag 0ETH](https://stacks.math.columbia.edu/tag/0ETH)
* [Stacks Project, Tag 0ETL](https://stacks.math.columbia.edu/tag/0ETL)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- **Stacks 0ETH.** A family of morphisms of schemes is a **V covering** if, over every
affine open of the target, a finite standard V covering by affine schemes refines the
pullback of the family. -/
@[stacks 0ETH]
public noncomputable def IsVCovering {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) : Prop :=
  ∀ (U : T.Opens) (hU : IsAffineOpen U),
    ∃ (𝒰 : PreZeroHypercover.{u} U.toScheme) (hfinite : Finite 𝒰.I₀)
      (haffine : ∀ j, IsAffine (𝒰.X j)),
      @IsStandardVCovering U.toScheme hU 𝒰.I₀ hfinite 𝒰.X haffine 𝒰.f ∧
        Nonempty (𝒰.Hom
          (({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).pullback₂ U.ι))

/-- The affine-local characterization of a V covering. -/
public theorem isVCovering_iff {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    IsVCovering X f ↔
      ∀ (U : T.Opens) (hU : IsAffineOpen U),
        ∃ (𝒰 : PreZeroHypercover.{u} U.toScheme) (hfinite : Finite 𝒰.I₀)
          (haffine : ∀ j, IsAffine (𝒰.X j)),
          @IsStandardVCovering U.toScheme hU 𝒰.I₀ hfinite 𝒰.X haffine 𝒰.f ∧
            Nonempty (𝒰.Hom
              (({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).pullback₂ U.ι)) :=
  Iff.rfl

/-- **Stacks 0ETL.** A set-valued presheaf on schemes is a sheaf for the V topology if it
satisfies the sheaf condition for every V covering family. -/
@[stacks 0ETL]
public abbrev IsVSheaf (F : Scheme.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (T : Scheme.{u}) (I : Type v) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T),
    IsVCovering X f → (Presieve.ofArrows X f).IsSheafFor F

end AlgebraicGeometry
