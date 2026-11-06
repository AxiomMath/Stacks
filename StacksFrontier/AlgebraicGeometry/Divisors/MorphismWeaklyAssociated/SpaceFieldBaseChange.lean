module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFieldBaseChangeRepresented
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Weakly associated points under the base change of a field extension

Let `K/k` be a field extension, let `X` be an algebraic space over `k` and let `F` be a
quasi-coherent `𝒪_X`-module. If a point `y` of the base change `X_K` is weakly associated to
the pullback `F_K`, then its image `x` in `X` is weakly associated to `F`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_fieldBaseChange`: a point of the base change
  `X_K` weakly associated to `F_K` lies over a point weakly associated to `F`.

## References

* [Stacks Project, Lemma 71.3.5 (Tag 0CUS)](https://stacks.math.columbia.edu/tag/0CUS)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y Y' : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Weak association descends along a field extension.** Let `K/k` be a field extension,
presented by objects `Tk` and `Tk'` of the site with underlying schemes `Spec k` and `Spec K` and
a morphism `gk : Tk' ⟶ Tk` inducing `Spec K → Spec k`. Let `X` be an algebraic space over
`Y = h_{Tk}`, let `X' = X ×_Y Y'` be its base change along `g : Y' ⟶ Y` for `Y' = h_{Tk'}`, and
let `F` be a quasi-coherent `𝒪_X`-module. If a point `y` of `X'` is weakly associated to the
pullback of `F`, then its image in `X` is weakly associated to `F`. -/
@[stacks 0CUS]
theorem isWeaklyAssociatedPoint_of_fieldBaseChange (k K : Type u) [Field k] [Field K]
    [Algebra k K] (Tk Tk' : BigFppfOver B S hS) (gk : Tk' ⟶ Tk)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (π : X' ⟶ X) (sq : IsPullback π f' f g)
    (ek : (BigFppfOver.toScheme B S hS).obj Tk ≅ Spec (CommRingCat.of k))
    (eK : (BigFppfOver.toScheme B S hS).obj Tk' ≅ Spec (CommRingCat.of K))
    (hgk : (BigFppfOver.toScheme B S hS).map gk =
      eK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ ek.inv)
    (eY : Y.1 ≅ yoneda.obj Tk) (eY' : Y'.1 ≅ yoneda.obj Tk')
    (hg : g.hom ≫ eY.hom = eY'.hom ≫ yoneda.map gk)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (y : points B S hS X'.1)
    (hy : IsWeaklyAssociatedPoint B S hS X' ((modulePullback B S hS π).obj F) y) :
    IsWeaklyAssociatedPoint B S hS X F (pointsMap B S hS X'.1 π.hom y) := by
  obtain ⟨U, a, u, ha, hau, -, -⟩ := exists_etale_scheme_chart_through_point B S hS X.2
    (𝟙 X.1) (isEtale_id B S hS X.1) (pointsMap B S hS X'.1 π.hom y)
  set V : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  set φ : V ⟶ X := ObjectProperty.homMk a
  have hφhom : φ.hom = a := rfl
  have hφ : IsEtale B S hS φ.hom := hφhom ▸ ha
  set V' : AlgebraicSpaces B S hS :=
    ⟨pullback φ.hom π.hom, isAlgebraicSpace_pullback B S hS φ.hom π.hom V.2 X'.2 X.2⟩
  set p : V' ⟶ V := ObjectProperty.homMk (pullback.fst φ.hom π.hom)
  set q : V' ⟶ X' := ObjectProperty.homMk (pullback.snd φ.hom π.hom)
  have sqp : IsPullback p q φ π :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F)
      (IsPullback.of_hasPullback φ.hom π.hom)
  have hq : IsEtale B S hS q.hom := isEtale_of_isPullback B S hS p q φ π sqp hφ
  obtain ⟨w, hwp, hwq⟩ := exists_point_of_isPullback B S hS sqp u y (by rw [hφhom, hau])
  have hiso : (modulePullback B S hS q).obj ((modulePullback B S hS π).obj F) ≅
      (modulePullback B S hS p).obj ((modulePullback B S hS φ).obj F) :=
    (modulePullbackCompIso B S hS q π).app F ≪≫
      eqToIso (congrArg (fun kk ↦ (modulePullback B S hS kk).obj F) sqp.w.symm) ≪≫
      ((modulePullbackCompIso B S hS p φ).app F).symm
  have hw : IsWeaklyAssociatedPoint B S hS V'
      ((modulePullback B S hS p).obj ((modulePullback B S hS φ).obj F)) w :=
    (isWeaklyAssociatedPoint_congr B S hS hiso w).1
      ((isWeaklyAssociatedPoint_modulePullback_iff B S hS q hq
        ((modulePullback B S hS π).obj F) w).2 (by rwa [hwq]))
  have hu : IsWeaklyAssociatedPoint B S hS V ((modulePullback B S hS φ).obj F) u := by
    have := isWeaklyAssociatedPoint_of_fieldBaseChange_represented B S hS k K U Tk Tk' gk g
      ek eK hgk eY eY' hg (φ ≫ f) (q ≫ f') p (sqp.paste_vert sq)
      ((modulePullback B S hS φ).obj F)
      (isQuasicoherentOnSite_modulePullback_of_isEtale B S hS φ hφ F inferInstance) w hw
    rwa [hwp] at this
  have := (isWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ F u).1 hu
  rwa [hφhom, hau] at this

end AlgebraicGeometry.Space

end
