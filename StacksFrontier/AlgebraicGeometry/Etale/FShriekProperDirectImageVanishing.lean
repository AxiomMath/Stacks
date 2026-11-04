module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteDerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.QuasiFiniteSupportVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of a direct image with compact support along a proper morphism

Let `B` be a big étale site, `f : X ⟶ Y` and `h : Y ⟶ Z` morphisms of it with `f` and `f ≫ h`
locally quasi-finite and `h` proper, and `F` a torsion abelian sheaf on `X_étale`. Then

`R^q h_* (f_! F) = 0` for `q > 0`,

where `f_!` is the direct image with compact support of [Stacks, Tag 0F6R]. This is the vanishing
in the proofs of [Stacks, Tag 0F7G] and [Stacks, Tag 0F7B].

The stalks of `f_! F` vanish away from `f(X)` ([Stacks, Tag 0F5F]), so this is the statement
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_support_range` (proper base
change and [Stacks, Tag 0F1F]), which is proved on Mathlib's small étale sites, carried to the
size-bounded small étale sites of `B` along `AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_of_support_range`: the
  vanishing for a torsion sheaf whose stalks vanish away from the image of `f`, on the bounded
  small étale sites.
* `AlgebraicGeometry.SmallEtale.isZero_etaleStalk_fShriekFunctor_of_not_mem_range`: the stalks of
  `f_! F` vanish away from `f(X)`.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor`:
  `R^q h_* (f_! F) = 0` for `q > 0`.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}

/-- **`R^q h_* G = 0` for `q > 0`, for a torsion sheaf `G` supported on a quasi-finite image**, on
the size-bounded small étale sites of a big étale site: `h` proper, `f ≫ h` locally
quasi-finite, and the stalks of `G` vanishing at every geometric point not lying over `f(X)`.
This is `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_support_range`
carried along `AlgebraicGeometry.SmallEtale.sheafEquiv`, which identifies the stalks
(`AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso`) and the higher direct images
(`AlgebraicGeometry.SmallEtale.rightDerivedSheafEquivPushforwardBaseChangeIso`). -/
@[sga "4½ Arcata 4.6.1" "special case"]
public theorem isZero_rightDerived_etalePushforward_of_support_range (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsProper (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map (f ≫ h))]
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) G)
    (hsupp : ∀ p : GeometricPoint Y.obj, p.hom default ∉ Set.range (B.inclusion.map f) →
      IsZero (etaleStalk B Y.obj Y.property p G.obj))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforward.{u, u + 1} B h).rightDerived q).obj G) := by
  let EY := SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}
  let EZ := SmallEtale.sheafEquiv B Z.obj Z.property AddCommGrpCat.{u + 1}
  have : LocallyQuasiFinite (B.inclusion.map f ≫ B.inclusion.map h) := by
    rw [← Functor.map_comp]; infer_instance
  have hmain := Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_support_range
    (B.inclusion.map f) (B.inclusion.map h) (EY.functor.obj G)
    (torsionSheafProperty_sheafEquiv_functor_obj B Y G hG)
    (fun p hp ↦ IsZero.of_iso (hsupp p hp)
      (((GrothendieckTopology.Point.uliftPresheafFiberIso.{u + 1}
        (Scheme.pointSmallEtale p.hom)).app (EY.functor.obj G).obj) ≪≫
        smallEtaleStalkAb_sheafEquiv_obj_iso B Y p G)) q hq
  have h₁ : IsZero (EZ.functor.obj (((etalePushforward.{u, u + 1} B h).rightDerived q).obj
      (EY.inverse.obj (EY.functor.obj G)))) :=
    hmain.of_iso ((rightDerivedSheafEquivPushforwardBaseChangeIso.{0, u} B h q).app
      (EY.functor.obj G)).symm
  have h₂ : IsZero (((etalePushforward.{u, u + 1} B h).rightDerived q).obj
      (EY.inverse.obj (EY.functor.obj G))) :=
    (EZ.inverse.map_isZero h₁).of_iso (EZ.unitIso.app _)
  exact h₂.of_iso (((etalePushforward.{u, u + 1} B h).rightDerived q).mapIso (EY.unitIso.app G))

/-- **The stalks of `f_! F` vanish away from the image of `f`**: by [Stacks, Tag 0F5F] the stalk at
a geometric point `ȳ` is the direct sum of the stalks of `F` over the geometric fibre of `f` at
`ȳ`, which is empty when `ȳ` does not lie over `f(X)`. -/
public theorem isZero_etaleStalk_fShriekFunctor_of_not_mem_range (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (s : GeometricPoint Y.obj) (hs : s.hom default ∉ Set.range (B.inclusion.map f)) :
    IsZero (etaleStalk B Y.obj Y.property s ((fShriekFunctor.{u, u} B f).obj F).obj) := by
  have : IsEmpty (GeometricFiberPoint B f s) :=
    ⟨fun x ↦ hs ⟨x.1 default, by rw [← Scheme.Hom.comp_apply, x.2]⟩⟩
  have : Subsingleton (fiberStalks.{u, u + 1} B f s F) :=
    ⟨fun a b ↦ DFinsupp.ext fun x ↦ isEmptyElim x⟩
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso (fShriekStalkIso.{u, u} B f s F)

/-- **`R^q h_* (f_! F) = 0` for `q > 0`.** Let `f : X ⟶ Y` and `h : Y ⟶ Z` be morphisms of a big
étale site with `f` and `f ≫ h` locally quasi-finite and `h` proper, and let `F` be a torsion
abelian sheaf on `X_étale`. Then the higher direct images along `h` of the direct image with
compact support `f_! F` vanish. The sheaf `f_! F` is torsion ([Stacks, Tag 0GJX]) and its stalks
vanish away from `f(X)`, so this is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_of_support_range`. This is the
vanishing used in the proofs of [Stacks, Tag 0F7G] and [Stacks, Tag 0F7B]. -/
@[sga "4½ Arcata 4.6.1" "special case"]
public theorem isZero_rightDerived_etalePushforward_fShriekFunctor (f : X ⟶ Y) (h : Y ⟶ Z)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsProper (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map (f ≫ h))]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F)
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforward.{u, u + 1} B h).rightDerived q).obj
      ((fShriekFunctor.{u, u} B f).obj F)) :=
  isZero_rightDerived_etalePushforward_of_support_range B f h _
    (torsionSheafProperty_fShriekFunctor_obj.{u, u} B f F hF)
    (fun s hs ↦ isZero_etaleStalk_fShriekFunctor_of_not_mem_range B f F s hs) q hq

end AlgebraicGeometry.SmallEtale

end
