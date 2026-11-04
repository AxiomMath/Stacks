module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleBaseChangeCriteriaComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange

/-!
# The clause of Stacks 0D36 at one base change, from a single cartesian square

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, `L` an invertible
`𝒪_X`-module and `g : V ⟶ Y` a morphism from a scheme of the site. The clause
`AlgebraicGeometry.Space.IsAmpleOnBaseChange` of Stacks 0D36 at `g` asks that `X ×_Y V` be a
scheme and that the reading of `L` on *every* scheme presenting `X ×_Y V` be ample over `V`. This
file shows that one presenting scheme suffices: any two are isomorphic over `V`, and the reading
of `L` and its ampleness pass along that isomorphism. With Stacks 0D36, clause (4) implies clause
(1) (`AlgebraicGeometry.Space.isRelativelyAmple_tfae_of_isInvertible`), relative ampleness of `L`
along `f` — representability of `f` included — follows from one such square over one surjective
étale chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isPullback_of_isRelativelyAmple`: the clause
  of Stacks 0D36 at `g`, from one cartesian square over `g` with an ample reading of `L`.

## References

* [Stacks Project, Tag 0D36](https://stacks.math.columbia.edu/tag/0D36)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The clause of Stacks 0D36 at a base change, from one cartesian square.** Let `f : X ⟶ Y`
be a morphism of algebraic spaces, `L` an invertible `𝒪_X`-module and `g : V ⟶ Y` a morphism from
a scheme of the site. If one scheme `U_V` presents `X ×_Y V` and the reading of `L` on `U_V` is
invertible and ample relative to `U_V ⟶ V`, then
`AlgebraicGeometry.Space.IsAmpleOnBaseChange` holds at `g`: every other presenting scheme is
isomorphic to `U_V` over `V`, and ampleness passes along that isomorphism by Stacks 0893. -/
theorem isAmpleOnBaseChange_of_isPullback_of_isRelativelyAmple {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {V UV : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y.1} {qV : UV ⟶ V}
    {pV : yoneda.obj UV ⟶ X.1} (hsqV : IsPullback pV (yoneda.map qV) f.hom g)
    (hinvV : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj UV)
      (baseChangeModule B S hS L UV pV))
    (hamplV : @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map qV)
      (baseChangeModule B S hS L UV pV) hinvV) :
    IsAmpleOnBaseChange B S hS f L V g := by
  refine ⟨⟨UV, qV, pV, hsqV⟩, fun U p q hsq => ?_⟩
  have hsq' : IsPullback p (yoneda.map q) f.hom (yoneda.map (𝟙 V) ≫ g) := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hsq
  have hd := hsq'.of_right' hsqV
  set d : U ⟶ UV := yoneda.preimage (hsqV.lift p (yoneda.map q ≫ yoneda.map (𝟙 V))
    (by rw [hsq'.w, Category.assoc]))
  have hdmap : yoneda.map d = hsqV.lift p (yoneda.map q ≫ yoneda.map (𝟙 V))
      (by rw [hsq'.w, Category.assoc]) := yoneda.map_preimage _
  have hdp : yoneda.map d ≫ pV = p := by rw [hdmap]; exact hsqV.lift_fst _ _ _
  have hsqd : IsPullback d q qV (𝟙 V) :=
    IsPullback.of_map yoneda (yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hdmap]; exact hd.w))
      (by rw [hdmap]; exact hd)
  have := hinvV
  have hamp := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
    (hsqd.map (BigFppfOver.toScheme B S hS)) (baseChangeModule B S hS L UV pV) hamplV
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hL UV U pV d
  rw [hdp] at e
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p) := isInvertibleModule_baseChangeModule L hL U p
  exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mpr hamp⟩

end AlgebraicGeometry.Space

end
