module

public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The structure map of a localized morphism of ringed sites

Let `(f, f^#) : (C, O) ⟶ (D, O')` be a morphism of ringed sites with underlying continuous
functor `u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Stacks 04J0 localizes it to
`(f', (f')^#) : (C/U, O_U) ⟶ (D/V, O'_V)`, which is
`AlgebraicGeometry.RingedSite.Hom.localized`. This file computes the structure map of the
localized morphism on underlying sheaves of sets: it is the restriction of the structure map of
`f` along `j_U`, precomposed with the Beck-Chevalley comparison for the localization square.

## Main definitions

* `CategoryTheory.SliceTopos.localizedPushforwardSquare`: clause (d) of Stacks 03CF read as a
  two-cell between the right adjoints.
* `CategoryTheory.SliceTopos.localizedInverseImageMate`: its Beck-Chevalley mate, the
  comparison `(f')⁻¹ j_V⁻¹ ⟶ j_U⁻¹ f⁻¹`.

## Main results

* `CategoryTheory.SliceTopos.localizedPushforwardSquare_app`: clause (d) is a strict equality of
  functors, so its two-cell is the identity on every component.
* `CategoryTheory.SliceTopos.homEquiv_localizedInverseImageMate`: the transpose of the comparison
  is the restriction of the unit of `f⁻¹ ⊣ f_*`.
* `CategoryTheory.SliceTopos.localizedInverseImageMate_comp`: composing the comparison with the
  restriction of a map is transposition.
* `AlgebraicGeometry.RingedSite.Hom.fSharpSet_localized`: the structure map of the localized
  morphism, on underlying sheaves of sets, is the comparison followed by the restriction of the
  structure map of `f`.

## Implementation notes

Clause (d) of Stacks 03CF, `CategoryTheory.sheafPushforwardContinuous_overPost_eq`, is a *strict*
equality `f'_* j_U⁻¹ = j_V⁻¹ f_*` of functors, proved by `rfl`; so the two-cell it defines is
`eqToHom` of that equality and is the identity on each component, and the structure map
`(f')^# = j_V⁻¹(f^#)` of `AlgebraicGeometry.RingedSite.Hom.localized` needs no comparison map
inserted. What the set-level computation below needs is the *inverse-image* comparison
`(f')⁻¹ j_V⁻¹ ⟶ j_U⁻¹ f⁻¹`, and that is taken here to be the Beck-Chevalley mate of clause (d);
`homEquiv_localizedInverseImageMate` is then `CategoryTheory.unit_mateEquiv_symm` together with
the component computation, and everything else is adjunction naturality.

**What this file does not settle.** The mate *is* invertible, which is an input that
`AlgebraicGeometry.RingedSite.Hom.localized` being a *locally ringed* morphism needs. The
identification of Stacks 03CF clause (b) with the mate is proved and registered on Stacks 03CF —
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom` of
`StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean`, whose own mate is this one on the
nose — and so is the conclusion:
`CategoryTheory.SliceTopos.isIso_localizedInverseImageMate` of
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMateInvertible.lean`, together with the
component form `isIso_localizedInverseImageMate_app`.

What remains for `AlgebraicGeometry.RingedSite.Hom.localized` to be a *locally ringed* morphism is
therefore only the transport of the units square: the units square of `f'` is the image under
`j_U⁻¹` of the units square of `f`, transported along this comparison — the units subsheaf of a
restricted structure sheaf is the restriction of the units subsheaf on the nose, and `j_U⁻¹` is a
right adjoint, hence preserves the cartesian square. The transport needs the comparison to be an
isomorphism at the two sheaves `O'` and `O'^*`, and that is what is available.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SliceTopos

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  (V : C) [u.IsContinuous J K]
  [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]

/-- **Stacks 03CF clause (d)** read as a two-cell between the right adjoints of the localization
square: `f_* j_V⁻¹ ⟶ j_U⁻¹ f'_*`. -/
noncomputable def localizedPushforwardSquare :
    TwoSquare (u.sheafPushforwardContinuous (Type u) J K)
      (K.overPullback (Type u) (u.obj V)) (J.overPullback (Type u) V)
      ((Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V)
        (K.over (u.obj V))) :=
  eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm

/-- The Beck-Chevalley comparison for the localization square: the mate of clause (d) of
Stacks 03CF, a natural transformation `(f')⁻¹ j_V⁻¹ ⟶ j_U⁻¹ f⁻¹`. -/
noncomputable def localizedInverseImageMate :
    TwoSquare (J.overPullback (Type u) V) (u.sheafPullback (Type u) J K)
      ((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)))
      (K.overPullback (Type u) (u.obj V)) :=
  (mateEquiv (u.sheafAdjunctionContinuous (Type u) J K)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
      (K.over (u.obj V)))).symm (localizedPushforwardSquare J K u V)

/-- Clause (d) is a strict equality of functors, so its two-cell is the identity on every
component. -/
theorem localizedPushforwardSquare_app (G : Sheaf K (Type u)) :
    (localizedPushforwardSquare J K u V).app G = 𝟙 _ := rfl

/-- The transpose of the Beck-Chevalley comparison across `(f')⁻¹ ⊣ f'_*` is the restriction of
the unit of `f⁻¹ ⊣ f_*`. -/
theorem homEquiv_localizedInverseImageMate (G : Sheaf J (Type u)) :
    (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
        (K.over (u.obj V))).homEquiv ((J.overPullback (Type u) V).obj G)
        ((K.overPullback (Type u) (u.obj V)).obj ((u.sheafPullback (Type u) J K).obj G)))
      ((localizedInverseImageMate J K u V).app G) =
      (J.overPullback (Type u) V).map
        ((u.sheafAdjunctionContinuous (Type u) J K).unit.app G) := by
  have h := unit_mateEquiv_symm (u.sheafAdjunctionContinuous (Type u) J K)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
      (K.over (u.obj V))) (localizedPushforwardSquare J K u V) G
  rw [Adjunction.homEquiv_unit]
  refine h.symm.trans ?_
  have h0 : (localizedPushforwardSquare J K u V).app
      ((u.sheafPullback (Type u) J K).obj G) = 𝟙 _ :=
    localizedPushforwardSquare_app J K u V _
  exact h0 ▸ Category.comp_id _

/-- Composing the Beck-Chevalley comparison with the restriction of a map is transposition: for
`psi : f⁻¹G ⟶ H`, the composite is the transpose across `(f')⁻¹ ⊣ f'_*` of the restriction of the
transpose of `psi` across `f⁻¹ ⊣ f_*`. -/
theorem localizedInverseImageMate_comp (G : Sheaf J (Type u)) {H : Sheaf K (Type u)}
    (psi : (u.sheafPullback (Type u) J K).obj G ⟶ H) :
    (localizedInverseImageMate J K u V).app G ≫
        (K.overPullback (Type u) (u.obj V)).map psi =
      (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
          (K.over (u.obj V))).homEquiv _ _).symm
        ((J.overPullback (Type u) V).map
          ((u.sheafAdjunctionContinuous (Type u) J K).homEquiv G H psi)) := by
  simp only [Functor.comp_obj]
  refine (Equiv.eq_symm_apply _).mpr ?_
  rw [Adjunction.homEquiv_naturality_right,
    homEquiv_localizedInverseImageMate, Adjunction.homEquiv_unit]
  rw [Functor.map_comp]
  rfl

end CategoryTheory.SliceTopos

namespace AlgebraicGeometry.RingedSite.Hom

variable {X Y : RingedSite.{u, u, u}}

/-- The functor `Over.post u` underlying the localization of a morphism of ringed sites is
continuous, by Stacks 03CF clause (a). -/
theorem isContinuous_overPost (f : RingedSite.Hom X Y) (V : Y.C) :
    (Over.post (X := V) f.u).IsContinuous (Y.J.over V) (X.J.over (f.u.obj V)) :=
  (Functor.isMorphismOfSites_overPost_of_isMorphismOfSites Y.J X.J f.u V
    f.isMorphismOfSites).isContinuous

attribute [local instance] isContinuous_overPost

variable (f : RingedSite.Hom X Y) (V : Y.C)

/-- **Stacks 04J0.** The structure map of the localized morphism of ringed sites, on underlying
sheaves of sets, is the Beck-Chevalley comparison for the localization square followed by the
restriction of the structure map of `f`. -/
theorem fSharpSet_localized :
    fSharpSet (f.localized V) =
      (CategoryTheory.SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app
          ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map (fSharpSet f) := by
  have hfs : (f.u.sheafAdjunctionContinuous (Type u) Y.J X.J).homEquiv
      ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)
      ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O) (fSharpSet f) =
      (sheafCompose Y.J (forget CommRingCat.{u})).map f.fsharp :=
    Equiv.apply_symm_apply _ _
  refine Eq.trans ?_ (CategoryTheory.SliceTopos.localizedInverseImageMate_comp Y.J X.J f.u V
    ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) (fSharpSet f)).symm
  rw [hfs]
  rfl

end AlgebraicGeometry.RingedSite.Hom

end
