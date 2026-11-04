module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.RestrictionThroughUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwoSquare

/-!
# Effacing a class on a closed subscheme through a finite direct image

This is the step of the proof of [Stacks, Tag 09ZE] that treats the sheaf `f_* N` for a finite
morphism `f : Y ⟶ X`. Let `i : Z ⟶ X` be a morphism (a closed immersion in the source) and
`Y_Z = Y ×_X Z`. By base change for the finite morphism `f` (Stacks 0959, 0A4E) and exactness
of finite direct images, a class `ξ ∈ H^q(Z, i^{-1} f_* N)` is the same as a class
`η ∈ H^q(Y_Z, N|_{Y_Z})`. If `π : Y' ⟶ Y` is finite and `η` restricts to zero on
`Y'_Z = Y' ×_Y Y_Z`, then `ξ` dies in `H^q(Z, i^{-1} f_* π_* π^{-1} N)` along the map induced by
the unit `N ⟶ π_* π^{-1} N`; when `π` is surjective that unit is a monomorphism, and so is its
image under `f_*`.

## Main results

* `Stacks.ExtAdjunction.extMap_comp_baseChangeMap_naturality` and
  `Stacks.ExtAdjunction.extMap_comp_baseChangeMap_unit` — the two formal identities, for a square
  of adjunctions, which the geometric statement is assembled from.
* `Stacks.ExtAdjunction.comp_map_unit_eq_zero_of_mapExactFunctor_eq_zero` — the effacement for
  two squares of adjunctions, with the functors as variables.
* `Stacks.EtaleCohomology.finiteDirectImageTransport` — the class on `Y_Z` attached to a class on
  `Z` with values in `i^{-1} f_* N`.
* `Stacks.EtaleCohomology.comp_directImage_unit_eq_zero_of_restriction_eq_zero` — the effacement
  through a finite direct image.

## Implementation notes

The formal argument is proved once with the six categories and the four adjunctions as variables
and then instantiated: stated directly for étale sheaves, the kernel has to compare the unfolded
inverse images, which does not finish in its budget.

## References

* [Stacks Project, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w₁ w₂ w₃ w₄ w₅ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ u

namespace Stacks.ExtAdjunction

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁} {Lf' : C₃ ⥤ C₄} {Rf' : C₄ ⥤ C₃}
  {Lg : C₁ ⥤ C₃} {Lg' : C₂ ⥤ C₄} {Lc : C₁ ⥤ C₄}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  [Lf'.Additive] [PreservesFiniteLimits Lf'] [PreservesFiniteColimits Lf']
  [HasExt.{w₃} C₃] [HasExt.{w₄} C₄]

omit [Abelian C₁] [Abelian C₂] in
/-- **Naturality of the base change transport on `Ext`.** For `φ : K ⟶ K'` and a class `y` with
values in `Lg (Rf K)`, transporting `y` through the base change map and the adjunction map of
`Lf' ⊣ Rf'` and then applying `Lg' φ` is the same as first applying `Lg (Rf φ)`. -/
theorem extMap_comp_baseChangeMap_naturality (a : C₃) {K K' : C₂} (φ : K ⟶ K') (n : ℕ)
    (y : Ext.{w₃} a (Lg.obj (Rf.obj K)) n) :
    extMap adjf' a (Lg'.obj K') n
        ((y.comp (Ext.mk₀ (Lg.map (Rf.map φ))) (add_zero n)).comp
          (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K')) (add_zero n)) =
      (extMap adjf' a (Lg'.obj K) n
        (y.comp (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K))
          (add_zero n))).comp (Ext.mk₀ (Lg'.map φ)) (add_zero n) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Stacks.CategoryTheory.BaseChange.map_naturality, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, extMap_naturality_mk₀]

omit [Abelian C₁] [Abelian C₂] in
/-- **The base change transport of the unit.** For a class `η` with values in `Lg K`,
postcomposing with `Lg` of the unit of `Lf ⊣ Rf` and transporting through the base change map and
the adjunction map of `Lf' ⊣ Rf'` gives the image of `η` under `Lf'`, followed by the comparison
of the two composites around the square. -/
theorem extMap_comp_baseChangeMap_unit (b : C₃) (K : C₁) (n : ℕ)
    (η : Ext.{w₃} b (Lg.obj K) n) :
    extMap adjf' b (Lg'.obj (Lf.obj K)) n
        ((η.comp (Ext.mk₀ (Lg.map (adjf.unit.app K))) (add_zero n)).comp
          (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (Lf.obj K)))
          (add_zero n)) =
      (η.mapExactFunctor Lf').comp (Ext.mk₀ ((eg.hom ≫ ef.inv).app K)) (add_zero n) := by
  have hu : Lg.map (adjf.unit.app K) ≫
      Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (Lf.obj K) =
        adjf'.unit.app (Lg.obj K) ≫ Rf'.map ((eg.hom ≫ ef.inv).app K) :=
    unit_mateEquiv adjf adjf' (Stacks.CategoryTheory.BaseChange.pullbackComparison eg ef) K
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hu, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, extMap_naturality_mk₀,
    ← mapExactFunctor_eq_extMap_comp_unit]

/-- **Precomposition with isomorphisms does not affect vanishing of an image.** If the image under
an exact functor `G` of `e ∘ x`, precomposed with an isomorphism, vanishes, then so does the image
of `x`. -/
theorem mapExactFunctor_eq_zero_of_comp {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₁} D₁]
    [Category.{v₂} D₂] [Abelian D₁] [Abelian D₂] [HasExt.{w₁} D₁] [HasExt.{w₂} D₂]
    (G : D₁ ⥤ D₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {a a' b : D₁} {c : D₂} (e : a' ⟶ a) (e' : c ⟶ G.obj a') [IsIso e] [IsIso e'] {n : ℕ}
    (x : Ext.{w₁} a b n)
    (h : (Ext.mk₀ e').comp (((Ext.mk₀ e).comp x (zero_add n)).mapExactFunctor G) (zero_add n) =
      0) :
    x.mapExactFunctor G = 0 := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀] at h
  exact (precomp_mk₀_bijective_of_isIso (e' ≫ G.map e) n).1 (h.trans (map_zero _).symm)

section TwoSquares

variable {C₅ : Type u₅} {C₆ : Type u₆} [Category.{v₅} C₅] [Category.{v₆} C₆]
  [Abelian C₅] [Abelian C₆]
  {Lp : C₂ ⥤ C₅} {Rp : C₅ ⥤ C₂} {Lp' : C₄ ⥤ C₆} {Rp' : C₆ ⥤ C₄}
  {Lg'' : C₅ ⥤ C₆} {Lc' : C₂ ⥤ C₆}
  (adjp : Lp ⊣ Rp) (adjp' : Lp' ⊣ Rp') (eg' : Lg' ⋙ Lp' ≅ Lc') (ef' : Lp ⋙ Lg'' ≅ Lc')
  [Lp'.Additive] [PreservesFiniteLimits Lp'] [PreservesFiniteColimits Lp']
  [Rf'.Additive] [PreservesFiniteLimits Rf'] [PreservesFiniteColimits Rf']
  [Rp'.Additive] [PreservesFiniteLimits Rp'] [PreservesFiniteColimits Rp']
  [HasExt.{w₅} C₆] [EnoughInjectives C₄] [EnoughInjectives C₆]
  [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef).natTrans]
  [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjp adjp' eg' ef').natTrans]

include adjp' eg' ef'

omit [Abelian C₁] [Abelian C₂] [Abelian C₅] in
/-- **Effacement through a direct image, formally.** Given two squares of adjunctions
`Lf ⊣ Rf`, `Lf' ⊣ Rf'` over `Lg, Lg'` and `Lp ⊣ Rp`, `Lp' ⊣ Rp'` over `Lg', Lg''`, with
invertible base change maps and exact `Rf'`, `Rp'`: if the class transported from
`ξ ∈ Ext^n(a, Lg (Rf N))` to `Ext^n(Lf' a, Lg' N)` is killed by `Lp'`, then `ξ` dies along
`Lg (Rf (unit))` for the unit `N ⟶ Rp (Lp N)`. -/
theorem comp_map_unit_eq_zero_of_mapExactFunctor_eq_zero (a : C₃) (N : C₂) (n : ℕ)
    (ξ : Ext.{w₃} a (Lg.obj (Rf.obj N)) n)
    (h : (extMap adjf' a (Lg'.obj N) n
      (ξ.comp (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef N))
        (add_zero n))).mapExactFunctor Lp' = 0) :
    ξ.comp (Ext.mk₀ (Lg.map (Rf.map (adjp.unit.app N)))) (add_zero n) = 0 := by
  have key := extMap_comp_baseChangeMap_unit adjp adjp' eg' ef' (Lf'.obj a) N n
    (extMap adjf' a (Lg'.obj N) n
      (ξ.comp (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef N)) (add_zero n)))
  rw [h, Ext.zero_comp] at key
  have hBp : IsIso (Stacks.CategoryTheory.BaseChange.map adjp adjp' eg' ef' (Lp.obj N)) :=
    inferInstanceAs (IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adjp adjp' eg'
      ef').natTrans.app _))
  have hBf : IsIso (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (Rp.obj (Lp.obj N))) :=
    inferInstanceAs (IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg
      ef).natTrans.app _))
  have h0 := (extMap_bijective adjp' (Lf'.obj a) (Lg''.obj (Lp.obj N)) n).1
    (key.trans (map_zero _).symm)
  have hunit := (postcomp_mk₀_bijective_of_isIso
    (Stacks.CategoryTheory.BaseChange.map adjp adjp' eg' ef' (Lp.obj N)) n).1
      (h0.trans (map_zero _).symm)
  have hnat := extMap_comp_baseChangeMap_naturality adjf adjf' eg ef a (K := N)
    (K' := Rp.obj (Lp.obj N)) (adjp.unit.app N) n ξ
  rw [hunit] at hnat
  exact (postcomp_mk₀_bijective_of_isIso _ n).1
    (((extMap_bijective adjf' a (Lg'.obj (Rp.obj (Lp.obj N))) n).1
      (hnat.trans (map_zero _).symm)).trans (map_zero _).symm)

end TwoSquares

end Stacks.ExtAdjunction

namespace Stacks.EtaleCohomology

section Geometric

variable {X Y Z YZ Y' Y'Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X) (g : YZ ⟶ Y) (fZ : YZ ⟶ Z)
  (sq : IsPullback g fZ f i)

/-- The class on `Y_Z = Y ×_X Z` corresponding to a class `ξ ∈ H^q(Z, i^{-1} f_* N)`: transport
`ξ` along the base change map `i^{-1} f_* N ⟶ f_{Z,*} g^{-1} N` and the adjunction
`f_Z^{-1} ⊣ f_{Z,*}`, and identify `f_Z^{-1} ℤ` with `ℤ`. -/
def finiteDirectImageTransport (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((etaleAbelianDirectImage.{u, 0} f).obj N)) q) :
    Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} g).obj N) q :=
  (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} fZ).app
      (AddCommGrpCat.of (ULift ℤ))).inv).comp
    (Stacks.ExtAdjunction.extMap (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ) _ _ q
      (ξ.comp (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ)
        (etaleAbelianInverseImageCompIso.{u, 0} fZ i).symm
        ((etaleAbelianInverseImageCompIso.{u, 0} g f).symm ≪≫
          eqToIso (congrArg (fun k : YZ ⟶ X ↦ etaleAbelianInverseImage.{u, 0} k) sq.w)) N))
        (add_zero q)))
    (zero_add q)

variable [IsFinite f] (π : Y' ⟶ Y) (g' : Y'Z ⟶ Y') (πZ : Y'Z ⟶ YZ)
  (sq' : IsPullback g' πZ π g) [IsFinite π]

include sq' in
/-- **Effacement through a finite direct image** (the `f_* M` step of Stacks 09ZE). Let
`f : Y ⟶ X` be finite, `i : Z ⟶ X` any morphism, `Y_Z = Y ×_X Z`, and `π : Y' ⟶ Y` finite with
base change `π_Z : Y'_Z ⟶ Y_Z`. If the class on `Y_Z` corresponding to
`ξ ∈ H^q(Z, i^{-1} f_* N)` restricts to zero on `Y'_Z`, then `ξ` dies in
`H^q(Z, i^{-1} f_* π_* π^{-1} N)` along the map induced by the unit `N ⟶ π_* π^{-1} N`. -/
theorem comp_directImage_unit_eq_zero_of_restriction_eq_zero
    (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((etaleAbelianDirectImage.{u, 0} f).obj N)) q)
    (h : etaleCohomologyRestrictionMap.{u, 0, u + 1} πZ _ q
      (finiteDirectImageTransport f i g fZ sq N q ξ) = 0) :
    ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map
      ((etaleAbelianDirectImage.{u, 0} f).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app N)))) (add_zero q) = 0 := by
  have : IsFinite fZ := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹IsFinite f›
  have : IsFinite πZ := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq' ‹IsFinite π›
  have : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ)
      (etaleAbelianInverseImageCompIso.{u, 0} fZ i).symm
      ((etaleAbelianInverseImageCompIso.{u, 0} g f).symm ≪≫
        eqToIso (congrArg (fun k : YZ ⟶ X ↦ etaleAbelianInverseImage.{u, 0} k) sq.w))).natTrans :=
    isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f i g fZ sq
  have : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} π)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} πZ)
      (etaleAbelianInverseImageCompIso.{u, 0} πZ g).symm
      ((etaleAbelianInverseImageCompIso.{u, 0} g' π).symm ≪≫
        eqToIso (congrArg (fun k : Y'Z ⟶ Y ↦ etaleAbelianInverseImage.{u, 0} k) sq'.w))).natTrans :=
    isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite π g g' πZ sq'
  have h1 := (etaleCohomologyRestrictionMap_apply.{u, 0, u + 1} πZ _ q _).symm.trans h
  exact Stacks.ExtAdjunction.comp_map_unit_eq_zero_of_mapExactFunctor_eq_zero
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ)
    (etaleAbelianInverseImageCompIso.{u, 0} fZ i).symm
    ((etaleAbelianInverseImageCompIso.{u, 0} g f).symm ≪≫
      eqToIso (congrArg (fun k : YZ ⟶ X ↦ etaleAbelianInverseImage.{u, 0} k) sq.w))
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} π)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} πZ)
    (etaleAbelianInverseImageCompIso.{u, 0} πZ g).symm
    ((etaleAbelianInverseImageCompIso.{u, 0} g' π).symm ≪≫
      eqToIso (congrArg (fun k : Y'Z ⟶ Y ↦ etaleAbelianInverseImage.{u, 0} k) sq'.w)) _ N q ξ
    (Stacks.ExtAdjunction.mapExactFunctor_eq_zero_of_comp (etaleAbelianInverseImage.{u, 0} πZ)
      ((etaleAbelianInverseImageConstantIso.{u, 0} fZ).app (AddCommGrpCat.of (ULift ℤ))).inv
      ((etaleAbelianInverseImageConstantIso.{u, 0} πZ).app (AddCommGrpCat.of (ULift ℤ))).inv
      (Stacks.ExtAdjunction.extMap (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ) _ _ q
        (ξ.comp (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map
          (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
          (etaleAbelianInverseImageDirectImageAdj.{u, 0} fZ)
          (etaleAbelianInverseImageCompIso.{u, 0} fZ i).symm
          ((etaleAbelianInverseImageCompIso.{u, 0} g f).symm ≪≫
            eqToIso (congrArg (fun k : YZ ⟶ X ↦ etaleAbelianInverseImage.{u, 0} k) sq.w)) N))
          (add_zero q))) h1)

end Geometric

end Stacks.EtaleCohomology
