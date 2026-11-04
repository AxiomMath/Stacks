module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationSquareFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedFieldGeneral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections

/-!
# Base change for a flat morphism with connected strict-henselization fibres, unconditionally

Let

```
Y --h--> X
|e       |f
v        v
T --g--> S
```

be a cartesian square of schemes with `f` flat and `g` quasi-compact and quasi-separated, and
suppose that at every geometric point `x̄` of `X` the morphism of strict henselizations
`σ : Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` has geometrically connected fibres. Then the
canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F`
on the small étale site of `T`. This is Tag 0F00.

## The proof

The source checks the claim on stalks (Tag 03PU), reads the stalks of the two sides at `x̄` as
the sections of `F` over `Spec(O^sh_{S,f(x̄)}) ×_S T` and over `Spec(O^sh_{X,x̄}) ×_X Y`
(Tag 03Q9), and identifies the two by Tag 0A3H applied to the canonical morphism between these
schemes, a base change of `σ`. The same three inputs are assembled here as follows.

Write `πX : X^sh ⟶ X` and `πS : S^sh ⟶ S` for the two strict henselizations, `x̃` for the
canonical lift of `x̄` to `X^sh` (so that `x̃ ≫ σ` is the canonical lift of `f(x̄)`),
`Y' = Y ×_X X^sh`, `T' = T ×_S S^sh` and `τ : Y' ⟶ T'` for the canonical morphism, the base change
of `σ` along `T' ⟶ S^sh`. The stalk at `x̄` of a sheaf on `X` is the set of global sections over
`X^sh` of its inverse image along `πX`, because `x̃` lies over the closed point of the strictly
henselian `X^sh`. The square of `Y' ⟶ T` over `X^sh ⟶ S` is pasted in two ways, from the given
square and the square of `h` over `πX`, and from the square of `g` over `πS` and the square of
`τ` over `σ`; by the cube of base change maps
(`Stacks.EtaleCohomology.isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage`)
the global sections over `X^sh` of `πX⁻¹` of the base change map are bijective as soon as those
of the three other base change maps are:

* the square of `h` over `πX`: Tag 03Q9 for sheaves of sets in degree zero
  (`Stacks.EtaleCohomology.isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`), `h` being
  quasi-compact and quasi-separated as a base change of `g`;
* the square of `g` over `πS`, after inverse image along `σ`: global sections over `X^sh` of an
  inverse image along `σ` are global sections over `S^sh`, both being the stalk at the canonical
  point, so this is again Tag 03Q9;
* the square of `τ` over `σ`: read through `Γ(X^sh, σ⁻¹ (T' ⟶ S^sh)_* -) = Γ(T', -)` and
  `Γ(X^sh, (Y' ⟶ X^sh)_* -) = Γ(Y', -)`, its global sections are a natural transformation
  `Γ(T', -) ⟶ Γ(Y', τ⁻¹ -)`, hence the canonical comparison
  (`Stacks.EtaleCohomology.globalSectionsNatTrans_ext`), which Tag 0A3H inverts because `τ` is
  flat, quasi-compact and has geometrically connected fibres, being a base change of `σ`.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_flat_strictHenselizationSquareMap` —
  the statement with the flatness of the morphisms of strict henselizations as the hypothesis.
* `isIso_smallEtaleSetBaseChange_of_geometricallyConnected_strictHenselization` — for `f` flat
  with geometrically connected fibres of the morphisms of strict henselizations, and `g`
  quasi-compact and quasi-separated, the base change map is an isomorphism.

## References

* [Stacks Project, Tag 0F00](https://stacks.math.columbia.edu/tag/0F00)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u})

section SquareMap

variable {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S)
  (x : GeometricPoint X)

/-- Global sections over `Spec(O^sh_{X,x̄})` of an inverse image along the morphism of strict
henselizations `σ : Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` are global sections over
`Spec(O^sh_{S,f(x̄)})`. -/
def strictHenselizationSquareMapGammaIso :
    Sheaf.Γ (strictHenselization B S hS (x.map f)).smallEtaleTopology (Type (u + 1)) ≅
      smallEtaleInverseImage.{u, 0} (strictHenselizationSquareMap B hX hS f x) ⋙
        Sheaf.Γ (strictHenselization B X hX x).smallEtaleTopology (Type (u + 1)) :=
  (sheafFiberClosedPointIsoGamma.{u, 0} (geometricPointToStrictHenselization B S hS (x.map f))
      (geometricPointToStrictHenselization_base_default B S hS (x.map f))).symm ≪≫
    eqToIso (congrArg (fun y ↦ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
      (geometricPointToStrictHenselization_strictHenselizationSquareMap B hX hS f x).symm) ≪≫
    (smallEtaleInverseImageStalkIso (strictHenselizationSquareMap B hX hS f x)
      (geometricPointToStrictHenselization B X hX x)).symm ≪≫
    Functor.isoWhiskerLeft
      (smallEtaleInverseImage.{u, 0} (strictHenselizationSquareMap B hX hS f x))
      (sheafFiberClosedPointIsoGamma.{u, 0} (geometricPointToStrictHenselization B X hX x)
        (geometricPointToStrictHenselization_base_default B X hX x))

/-- For a cartesian square of `τ : P ⟶ Q` over the morphism of strict henselizations `σ`, flat
with geometrically connected fibres, the base change map `σ⁻¹ l_* ⟶ k_* τ⁻¹` is bijective on
global sections over `Spec(O^sh_{X,x̄})`. -/
theorem isIso_whiskerRight_smallEtaleSetBaseChange_strictHenselizationSquareMap
    {P Q : Scheme.{u}} {τ : P ⟶ Q} {k : P ⟶ strictHenselization B X hX x}
    {l : Q ⟶ strictHenselization B S hS (x.map f)}
    (hpb : IsPullback τ k l (strictHenselizationSquareMap B hX hS f x))
    (hflat : Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : GeometricallyConnected (strictHenselizationSquareMap B hX hS f x)) :
    IsIso (Functor.whiskerRight (smallEtaleSetBaseChange.{u, 0} τ k l
        (strictHenselizationSquareMap B hX hS f x) hpb.w)
      (Sheaf.Γ (strictHenselization B X hX x).smallEtaleTopology (Type (u + 1)))) := by
  have : Flat τ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hflat
  have : QuasiCompact τ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
    (inferInstanceAs (QuasiCompact (strictHenselizationSquareMap B hX hS f x)))
  have : GeometricallyConnected τ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hconn
  have : IsIso (globalSectionsSmallEtaleInverseImage.{u, 0} τ) :=
    isIso_globalSectionsSmallEtaleInverseImage.{u, 0} τ
      (universally_isQuotientMap_of_flat_quasiCompact _)
  let A := (smallEtalePushforwardGammaIso.{u, 0} l).symm ≪≫
    Functor.isoWhiskerLeft _ (strictHenselizationSquareMapGammaIso B hX hS f x)
  let C := Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0} τ)
    (smallEtalePushforwardGammaIso.{u, 0} k)
  refine (isIso_comp_right_iff _ C.hom).1 ((isIso_comp_left_iff A.hom _).1 ?_)
  convert (inferInstance : IsIso (globalSectionsSmallEtaleInverseImage.{u, 0} τ)) using 1
  exact globalSectionsNatTrans_ext.{u, 0} τ _ _

/-- The components of `isIso_whiskerRight_smallEtaleSetBaseChange_strictHenselizationSquareMap`:
the base change map of a cartesian square of `τ` over the morphism of strict henselizations,
flat with geometrically connected fibres, is bijective on global sections over
`Spec(O^sh_{X,x̄})` at every sheaf of sets. -/
theorem isIso_Γ_map_smallEtaleSetBaseChange_strictHenselizationSquareMap
    {P Q : Scheme.{u}} {τ : P ⟶ Q} {k : P ⟶ strictHenselization B X hX x}
    {l : Q ⟶ strictHenselization B S hS (x.map f)}
    (hpb : IsPullback τ k l (strictHenselizationSquareMap B hX hS f x))
    (hflat : Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : GeometricallyConnected (strictHenselizationSquareMap B hX hS f x))
    (G : Sheaf Q.smallEtaleTopology (Type (u + 1))) :
    IsIso ((Sheaf.Γ (strictHenselization B X hX x).smallEtaleTopology (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} τ k l (strictHenselizationSquareMap B hX hS f x)
        hpb.w).app G)) := by
  have := isIso_whiskerRight_smallEtaleSetBaseChange_strictHenselizationSquareMap B hX hS f x
    hpb hflat hconn
  exact NatIso.isIso_app_of_isIso (Functor.whiskerRight _ _) G

end SquareMap

section Core

variable {X Y S T U Yi V Ti : Scheme.{u}}
  (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
  (u : U ⟶ X) (hi : Yi ⟶ U) (toY : Yi ⟶ Y) (wu : toY ≫ h = hi ≫ u)
  (fi : U ⟶ V) (v : V ⟶ S) (wf : u ≫ f = fi ≫ v)
  (ei : Yi ⟶ Ti) (gi : Ti ⟶ V) (wl : ei ≫ gi = hi ≫ fi)
  (toT : Ti ⟶ T) (wt : toT ≫ g = gi ≫ v)
  (wc : toY ≫ e = ei ≫ toT)

include wf wc in
/-- The cube of base change maps on global sections: given `Γ(V, -) ≅ Γ(U, fi⁻¹ -)`, if the base
change maps of the squares `(toY, hi, h, u)` and `(ei, hi, gi, fi)` are bijective on global
sections over `U` and that of the square `(toT, gi, g, v)` is bijective on global sections over
`V`, then the inverse image along `u` of the base change map of the square `(e, h, g, f)` is
bijective on global sections over `U`. -/
theorem isIso_Γ_inverseImage_smallEtaleSetBaseChange_of_cube
    (ε : Sheaf.Γ (smallEtaleTopology V) (Type (u + 1)) ≅
      smallEtaleInverseImage.{u, 0} fi ⋙ Sheaf.Γ (smallEtaleTopology U) (Type (u + 1)))
    (F : Sheaf (smallEtaleTopology T) (Type (u + 1)))
    (ht : IsIso ((Sheaf.Γ (smallEtaleTopology U) (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} toY hi h u wu).app
        ((smallEtaleInverseImage.{u, 0} e).obj F))))
    (ht' : IsIso ((Sheaf.Γ (smallEtaleTopology V) (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} toT gi g v wt).app F)))
    (hs' : IsIso ((Sheaf.Γ (smallEtaleTopology U) (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} ei hi gi fi wl).app
        ((smallEtaleInverseImage.{u, 0} toT).obj F)))) :
    IsIso ((Sheaf.Γ (smallEtaleTopology U) (Type (u + 1))).map
      ((smallEtaleInverseImage.{u, 0} u).map ((smallEtaleSetBaseChange.{u, 0} e h g f w).app F))) :=
  isIso_map_inverseImage_smallEtaleSetBaseChange_of_cube_of_inverseImage.{u, 0} e h g f w u hi toY
    wu fi v wf ei gi wl toT wt wc (Sheaf.Γ (smallEtaleTopology U) (Type (u + 1)))
    (Sheaf.Γ (smallEtaleTopology V) (Type (u + 1))) ε F ((smallEtaleInverseImage.{u, 0} e).obj F)
    rfl ht ht' hs'

end Core

section Conclusion

variable {X S Y T : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S)
  {h : Y ⟶ X} {e : Y ⟶ T} {g : T ⟶ S}

/-- **The base change map is bijective on global sections over the strict henselization, after
inverse image to it.** In a cartesian square with `g` quasi-compact and quasi-separated, let
`x̄` be a geometric point of `X` at which the morphism of strict henselizations is flat with
geometrically connected fibres. Then the inverse image along `Spec(O^sh_{X,x̄}) ⟶ X` of the base
change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is bijective on global sections. -/
theorem isIso_Γ_inverseImage_smallEtaleSetBaseChange_of_strictHenselizationSquareMap
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) (Type (u + 1))) (x : GeometricPoint X)
    (hflat : Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : GeometricallyConnected (strictHenselizationSquareMap B hX hS f x)) :
    IsIso ((Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) (Type (u + 1))).map
      ((smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B X hX x)).map
        ((smallEtaleSetBaseChange.{u, 0} e h g f sq.w.symm).app F))) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip inferInstance
  have hσ : strictHenselizationToBase B X hX x ≫ f =
      strictHenselizationSquareMap B hX hS f x ≫ strictHenselizationToBase B S hS (x.map f) :=
    (strictHenselizationSquareMap_comp B hX hS f x).symm
  have hτ : (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e) ≫ g =
      (pullback.snd h (strictHenselizationToBase B X hX x) ≫
        strictHenselizationSquareMap B hX hS f x) ≫
        strictHenselizationToBase B S hS (x.map f) := by
    rw [Category.assoc, Category.assoc, ← hσ, ← sq.w, ← Category.assoc, pullback.condition,
      Category.assoc]
  have hτp : pullback.lift _ _ hτ ≫ pullback.fst g (strictHenselizationToBase B S hS (x.map f)) =
      pullback.fst h (strictHenselizationToBase B X hX x) ≫ e :=
    pullback.lift_fst _ _ _
  have hτg : pullback.lift _ _ hτ ≫ pullback.snd g (strictHenselizationToBase B S hS (x.map f)) =
      pullback.snd h (strictHenselizationToBase B X hX x) ≫
        strictHenselizationSquareMap B hX hS f x :=
    pullback.lift_snd _ _ _
  have hpbτ : IsPullback (pullback.lift _ _ hτ)
      (pullback.snd h (strictHenselizationToBase B X hX x))
      (pullback.snd g (strictHenselizationToBase B S hS (x.map f)))
      (strictHenselizationSquareMap B hX hS f x) := by
    have hout : IsPullback (pullback.fst h (strictHenselizationToBase B X hX x) ≫ e)
        (pullback.snd h (strictHenselizationToBase B X hX x)) g
        (strictHenselizationToBase B X hX x ≫ f) :=
      (IsPullback.of_hasPullback h (strictHenselizationToBase B X hX x)).paste_horiz sq.flip
    rw [← hτp, hσ] at hout
    exact IsPullback.of_right hout hτg
      (IsPullback.of_hasPullback g (strictHenselizationToBase B S hS (x.map f)))
  have ht := isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B X hX x h
    ((smallEtaleInverseImage.{u, 0} e).obj F)
  have ht' := isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B S hS (x.map f) g F
  have hs' := isIso_Γ_map_smallEtaleSetBaseChange_strictHenselizationSquareMap B hX hS f x hpbτ
    hflat hconn ((smallEtaleInverseImage.{u, 0}
      (pullback.fst g (strictHenselizationToBase B S hS (x.map f)))).obj F)
  exact isIso_Γ_inverseImage_smallEtaleSetBaseChange_of_cube e h g f sq.w.symm
    (strictHenselizationToBase B X hX x) (pullback.snd h (strictHenselizationToBase B X hX x))
    (pullback.fst h (strictHenselizationToBase B X hX x)) pullback.condition
    (strictHenselizationSquareMap B hX hS f x) (strictHenselizationToBase B S hS (x.map f)) hσ
    (pullback.lift _ _ hτ) (pullback.snd g (strictHenselizationToBase B S hS (x.map f)))
    hpbτ.w (pullback.fst g (strictHenselizationToBase B S hS (x.map f))) pullback.condition
    hτp.symm (strictHenselizationSquareMapGammaIso B hX hS f x) F ht ht' hs'

/-- **Tag 0F00 with the flatness of the morphisms of strict henselizations as hypothesis.** In a
cartesian square with `g` quasi-compact and quasi-separated, if at every geometric point `x̄` of
`X` the morphism of strict henselizations `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` is flat with
geometrically connected fibres, then the base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T`. -/
theorem isIso_smallEtaleSetBaseChange_of_flat_strictHenselizationSquareMap
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (hflat : ∀ x : GeometricPoint X, Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : ∀ x : GeometricPoint X,
      GeometricallyConnected (strictHenselizationSquareMap B hX hS f x)) :
    IsIso (smallEtaleSetBaseChange.{u, 0} e h g f sq.w.symm) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun F ↦ ?_
  refine isIso_of_geometricStalk_family.{0, u} (fun z : X ↦ (GeometricPoint.ofPoint X z).hom) ?_ _
    fun z ↦ ?_
  · refine Set.eq_univ_iff_forall.mpr fun z ↦ Set.mem_iUnion.mpr ⟨z, default, ?_⟩
    exact GeometricPoint.ofPoint_liesOver X z
  · exact (isIso_sheafFiber_map_iff_isIso_Γ_map_inverseImage_strictHenselization B hX
      (GeometricPoint.ofPoint X z) _).2
      (isIso_Γ_inverseImage_smallEtaleSetBaseChange_of_strictHenselizationSquareMap B hX hS f sq F
        (GeometricPoint.ofPoint X z) (hflat _) (hconn _))

/-- Let `f : X ⟶ S` be flat, and suppose that for every geometric
point `x̄` of `X` the morphism `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` of strict henselizations
has geometrically connected fibres. Then for every cartesian square

```
Y --h--> X
|e       |f
v        v
T --g--> S
```

with `g` quasi-compact and quasi-separated, the canonical base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of sets `F` on `T_étale`.

The strict henselizations are those constructed inside a big étale site `B` containing `X` and
`S`; the base change map is `Stacks.EtaleCohomology.smallEtaleSetBaseChange`, and the conclusion
is that it is an isomorphism of functors, that is, at every `F`. -/
@[stacks 0F00]
theorem isIso_smallEtaleSetBaseChange_of_geometricallyConnected_strictHenselization [Flat f]
    (hconn : ∀ x : GeometricPoint X,
      GeometricallyConnected (strictHenselizationSquareMap B hX hS f x))
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g] :
    IsIso (smallEtaleSetBaseChange.{u, 0} e h g f sq.w.symm) :=
  isIso_smallEtaleSetBaseChange_of_flat_strictHenselizationSquareMap B hX hS f sq
    (fun x ↦ flat_strictHenselizationSquareMap B hX hS f x) hconn

end Conclusion

end Stacks.EtaleCohomology

end
