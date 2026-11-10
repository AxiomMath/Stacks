module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfMorphism

/-!
# Restriction along a covering morphism detects isomorphisms of big fppf sheaves

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `j : V ⟶ Y` a morphism
of `T`. Restriction of big fppf sheaves on `Y` along `j` is restriction along
`Over.map j : Over V ⥤ Over Y`. If every object `U` of the slice over `Y` is covered by the
arrows into it whose source lifts through `j`, a morphism of big fppf sheaves on `Y` is an
isomorphism as soon as its restriction along `j` is.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.liftingSieve`: the sieve on an object `U` of the slice
  over `Y` of the arrows `U' ⟶ U` whose source `U'` lifts through `j`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_of_isIso_overMap_pushforward_map`: a morphism of
  big fppf sheaves on `Y` whose restriction along `j` is an isomorphism is an isomorphism, when
  the lifting sieves are covering.

-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The sieve on an object `U` of the slice over `Y` of the arrows `U' ⟶ U` whose source lifts
through `j`, that is, whose structure morphism to `Y` factors through `j`. -/
def liftingSieve {V Y : T.Spaces} (j : V ⟶ Y) (U : Over Y) : Sieve U where
  arrows U' _ := ∃ a : U'.left ⟶ V, a ≫ j = U'.hom
  downward_closed := by
    rintro U' U'' g ⟨a, ha⟩ k
    exact ⟨k.left ≫ a, by rw [Category.assoc, ha, Over.w k]⟩

/-- **Restriction along `j` detects isomorphisms of big fppf sheaves**, when every object of
the slice over `Y` is covered by the arrows into it whose source lifts through `j`. -/
theorem isIso_of_isIso_overMap_pushforward_map {V Y : T.Spaces} (j : V ⟶ Y)
    (hcov : ∀ U : Over Y, liftingSieve T j U ∈ BigFppfSpaceOver.topology T Y U)
    {K K' : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))} (φ : K ⟶ K')
    (hφ : IsIso (((Over.map j).sheafPushforwardContinuous (Type (u + 1))
      (BigFppfSpaceOver.topology T V) (BigFppfSpaceOver.topology T Y)).map φ)) :
    IsIso φ := by
  have hbij : ∀ (U U' : Over Y) (g : U' ⟶ U), (liftingSieve T j U).arrows g →
      Function.Bijective (φ.hom.app (op U')) := by
    rintro U U' g ⟨a, ha⟩
    let e : (Over.map j).obj (Over.mk a) ≅ U' := Over.isoMk (Iso.refl _) (by simpa using ha.symm)
    have : IsIso (φ.hom.app (op ((Over.map j).obj (Over.mk a)))) :=
      inferInstanceAs (IsIso ((((Over.map j).sheafPushforwardContinuous (Type (u + 1))
        (BigFppfSpaceOver.topology T V) (BigFppfSpaceOver.topology T Y)).map φ).hom.app
          (op (Over.mk a))))
    have : IsIso (φ.hom.app (op U') ≫ K'.obj.map e.hom.op) := by
      rw [← φ.hom.naturality]
      infer_instance
    exact (isIso_iff_bijective _).1 (IsIso.of_isIso_comp_right _ (K'.obj.map e.hom.op))
  refine (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine (BigFppfSpaceOver.topology T Y).superset_covering (fun U' g hg => ?_) (hcov X.unop)
    apply (hbij _ _ g hg).1
    change (K.obj.map g.op ≫ φ.hom.app (op U')) x = (K.obj.map g.op ≫ φ.hom.app (op U')) y
    rw [φ.hom.naturality]
    exact congrArg (K'.obj.map g.op) hxy
  · exact (BigFppfSpaceOver.topology T Y).superset_covering
      (fun U' g hg => (hbij _ _ g hg).2 _) (hcov U)

end AlgebraicGeometry.BigFppfSpaceSite

end
