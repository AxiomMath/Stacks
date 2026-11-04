module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GlueAbstract
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GlueStalk

/-!
# Glueing modules across an elementary distinguished square

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, with intersection `P = U ×_W V`, and write `(-)|_Y` for restriction of modules along
an étale morphism `j_Y : Y ⟶ W` and `j_{Y!}` for extension by zero, its left adjoint.  Given an
`𝒪_W`-module `F`, modules `G_U` on `U` and `H` on `V` with maps `ψ_U : G_U ⟶ F|_U` and
`ψ_V : H ⟶ F|_V`, and an identification `θ : H|_P ≅ G_U|_P` compatible with them, this file
glues `G_U` and `H` to an `𝒪_W`-module `G` with a map `ψ : G ⟶ F` restricting to `ψ_U` and
`ψ_V`.

## Construction

Write `q : P ⟶ V` for the second projection.  The module `G` is the pushout of

* `a : j_{V!}q_!(H|_P) ⟶ j_{U!}G_U`, the adjoint, along `j_{V!} ⊣ (-)|_V` and then
  `q_! ⊣ (-)|_P`, of `H|_P ⟶ G_U|_P ⟶ ((j_{U!}G_U)|_U)|_P ≅ ((j_{U!}G_U)|_V)|_P` (the
  identification `θ`, the unit of `j_{U!}` restricted to `P`, and the two composition
  comparisons of restrictions), and
* `b = j_{V!}(ε_H) : j_{V!}q_!(H|_P) ⟶ j_{V!}H`, extension by zero of the counit of `q_!`.

The map `ψ` is induced by the adjoints of `ψ_U` and `ψ_V`; the two agree on the source of the
pushout by the compatibility of `θ`, an adjunction computation.  The comparisons are
`α_U = η ≫ ι_U|_U : G_U ⟶ G|_U` and `α_V = η ≫ ι_V|_V : H ⟶ G|_V`, and the two equations
`α_U ≫ ψ|_U = ψ_U`, `α_V ≫ ψ|_V = ψ_V` are triangle identities.  All of this is formal and is
done for an abstract square of functors with left adjoints in
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GlueAbstract`
(`CategoryTheory.GlueSquare`); this file instantiates it with the restriction functors of the
square and supplies the geometry.

## Invertibility of the comparisons

Both are checked on geometric stalks, which detect isomorphisms (Stacks 04K5), the stalk functor
being exact (Stacks 04EQ) and so preserving the pushout.

* At a geometric point `x̄` of `W` lying in `U`, every lift of `x̄` to `V` lifts uniquely to `P`,
  so the counit of `q_!` is invertible on stalks there and, by Equation 08GU, `b` is invertible
  on the stalk at `x̄`; hence so is `ι_U`.  As `x̄` lifts uniquely to `U`, the unit of `j_{U!}`
  is invertible on the stalk at that lift, and Equation 08GT identifies the stalk of `ι_U|_U`
  with that of `ι_U`.  This proves that `α_U` is invertible.
* At a geometric point of `V` over a point `x̄ ∉ U`, the source of the pushout and `j_{U!}G_U`
  have vanishing stalk at `x̄`, which has no lift to `U` nor to `P`, so `ι_V` is invertible on
  the stalk at `x̄`; and `x̄` has a unique lift to `V`, so the unit of `j_{V!}` is invertible
  there.
* At a geometric point of `V` over a point of `U`: transposing the commutativity of the pushout
  square shows `α_V|_P = θ ≫ α_U|_P` (read through the composition comparisons), so `α_V|_P` is
  invertible; the point lifts to `P`, where the stalk of `α_V|_P` is that of `α_V`.

## Main results

* `AlgebraicGeometry.Space.isIso_edsGlueαU` and `AlgebraicGeometry.Space.isIso_edsGlueαV`: the
  two comparisons of the glued module are invertible.
* `AlgebraicGeometry.Space.exists_glue_hom_of_isElementaryDistinguishedSquare`: the glueing.

## Implementation notes

The stalk functor is applied to the pushout through
`Stacks.exactFunctor_sheafModuleFiber`, whose sheafification hypotheses on the site of `W` are
not instances for `AlgebraicGeometry.Space.smallEtaleRingedSite` and are restated by
`inferInstanceAs`.  The stalk computations themselves are
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GlueStalk`.

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

section Construction

variable (GU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)
  (H : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
  (θ : (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj H ≅
      (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)).obj GU)

/-- The first map `j_{V!} q_!(H|_P) ⟶ j_{U!}G_U` of the glueing pushout of an elementary
distinguished square: `CategoryTheory.GlueSquare.glueLeft` for its square of restrictions. -/
abbrev edsGlueLeft :=
  GlueSquare.glueLeft
    (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))
    (edsFactorIsoOpen B S hS hsq) (edsFactorIsoEtale B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    GU H θ

/-- The second map `j_{V!} q_!(H|_P) ⟶ j_{V!}H` of the glueing pushout of an elementary
distinguished square: extension by zero of the counit of `q_!`. -/
abbrev edsGlueRight :=
  GlueSquare.glueRight
    (LV := etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)) H

/-- The comparison `α_U : G_U ⟶ G|_U` of the glueing of an elementary distinguished square. -/
abbrev edsGlueαU :=
  GlueSquare.glueαU
    (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))
    (edsFactorIsoOpen B S hS hsq) (edsFactorIsoEtale B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    GU H θ

/-- The comparison `α_V : H ⟶ G|_V` of the glueing of an elementary distinguished square. -/
abbrev edsGlueαV :=
  GlueSquare.glueαV
    (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))
    (edsFactorIsoOpen B S hS hsq) (edsFactorIsoEtale B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq))
    GU H θ

/-- **At a geometric point of the open subspace the second map of the glueing pushout is
invertible on stalks**: every lift of the point to the étale algebraic space lifts uniquely to
the intersection, so the counit of `q_!` is invertible on the stalks at all those lifts, and
Equation 08GU assembles them. -/
theorem isIso_sheafFiber_edsGlueRight_of_mem (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).map (edsGlueRight B S hS hsq H))) :=
  isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) x _ fun t => by
      have := unique_geometricPointLift_edsSnd_of_mem B S hS hsq
        (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)
        (by rw [geometricPointMap_liftGeometricPoint]; exact hx)
      exact isIso_sheafFiber_etaleModuleCounit_of_unique B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq) (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t) H

variable
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The common source `j_{V!} q_!(H|_P)` of the glueing pushout has vanishing stalk at a
geometric point outside the open subspace**: it is the extension by zero from the
intersection, to which such a point does not lift. -/
theorem isZero_edsModuleStalk_edsGlueSource_of_notMem (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((edsModuleStalk B S hS x).obj
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj
        ((etaleModuleLowerShriek B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj
          ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).obj H)))) := by
  have := isEmpty_geometricPointLift_edsInterHom_of_notMem B S hS hsq x hx
  let adj : etaleModuleLowerShriek B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) ⋙
        etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⊣
      etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) :=
    ((etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).comp
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))).ofNatIsoRight (edsFactorIsoEtale B S hS hsq)
  refine IsZero.of_iso ?_ ((edsModuleStalk B S hS x).mapIso
    ((Adjunction.leftAdjointUniq adj (etaleModuleLowerShriekAdjunction B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))).app
        ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).obj H)))
  exact isZero_edsModuleStalk_of_isZero_sheafFiber B S hS _ x
    (isZero_sheafFiber_etaleModuleShriek_of_isEmpty B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq) x _)

/-- **The extension by zero from the open subspace of an arbitrary module has vanishing stalk at
a geometric point outside the open subspace.** -/
theorem isZero_edsModuleStalk_edsOpen_shriek_obj_of_notMem (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((edsModuleStalk B S hS x).obj
      ((etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj GU)) := by
  have := isEmpty_geometricPointLift_edsOpenHom_of_notMem B S hS hsq x hx
  exact isZero_edsModuleStalk_of_isZero_sheafFiber B S hS _ x
    (isZero_sheafFiber_etaleModuleShriek_of_isEmpty B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) x _)

/-- **At a geometric point of the open subspace the first coprojection of the glueing pushout
is invertible on stalks**: the stalk functor preserves the pushout, and the second map is
invertible on the stalk there. -/
theorem isIso_sheafFiber_edsGlue_inl_of_mem (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).map
        (pushout.inl (edsGlueLeft B S hS hsq GU H θ) (edsGlueRight B S hS hsq H)))) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp
    (Stacks.exactFunctor_sheafModuleFiber (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W))
  have hp := (IsPushout.of_hasPushout (edsGlueLeft B S hS hsq GU H θ)
    (edsGlueRight B S hS hsq H)).map (edsModuleStalk B S hS x)
  have : IsIso ((edsModuleStalk B S hS x).map (edsGlueRight B S hS hsq H)) :=
    isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ x
      (isIso_sheafFiber_edsGlueRight_of_mem B S hS hsq H x hx)
  exact isIso_sheafFiber_of_isIso_edsModuleStalk B S hS _ x hp.isIso_inl_of_isIso

/-- **At a geometric point outside the open subspace the second coprojection of the glueing
pushout is invertible on stalks**: the stalk functor preserves the pushout, and the first map
is a map between vanishing stalks there. -/
theorem isIso_sheafFiber_edsGlue_inr_of_notMem (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).map
        (pushout.inr (edsGlueLeft B S hS hsq GU H θ) (edsGlueRight B S hS hsq H)))) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp
    (Stacks.exactFunctor_sheafModuleFiber (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W))
  have hp := (IsPushout.of_hasPushout (edsGlueLeft B S hS hsq GU H θ)
    (edsGlueRight B S hS hsq H)).map (edsModuleStalk B S hS x)
  have : IsIso ((edsModuleStalk B S hS x).map (edsGlueLeft B S hS hsq GU H θ)) :=
    isIso_of_source_target_iso_zero _
      (isZero_edsModuleStalk_edsGlueSource_of_notMem B S hS hsq H x hx).isoZero
      (isZero_edsModuleStalk_edsOpen_shriek_obj_of_notMem B S hS hsq GU x hx).isoZero
  exact isIso_sheafFiber_of_isIso_edsModuleStalk B S hS _ x hp.isIso_inr_of_isIso

/-- If `x̄` has a unique lift along an étale `f`, then `η_M ≫ f^*g` is invertible on the stalk at
a point `ȳ` over `x̄` as soon as `g : f_!M ⟶ N` is invertible on the stalk at `x̄`. -/
private theorem isIso_sheafFiber_unit_comp_pullback_map {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (y : GeometricPoint B S hS X.1)
    [Unique (GeometricPointLift B S hS f.hom (geometricPointMap f.hom y))]
    (M : Modules.{u, u} B S hS X.1 X.2) {N : Modules.{u, u} B S hS Y.1 Y.2}
    (g : (etaleModuleLowerShriek B S hS f hf).obj M ⟶ N)
    (hg : IsIso ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom y) Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map g))) :
    IsIso ((etaleSitePoint B S hS X.1 y X.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M ≫
          (etaleModulePullback.{u, u} B S hS f hf).map g))) := by
  have h₁ := isIso_sheafFiber_etaleModuleUnit_of_unique B S hS f hf _
    (tautologicalGeometricPointLift B S hS f y) M
  have h₂ := (isIso_sheafFiber_etaleModulePullback_map_iff B S hS f hf
    (tautologicalGeometricPointLift B S hS f y) g).2 hg
  have e := (SheafOfModules.toSheaf (etaleRingSheaf B S hS X) ⋙
    (etaleSitePoint B S hS X.1 y X.2).sheafFiber (A := AddCommGrpCat.{u})).map_comp
    ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M)
    ((etaleModulePullback.{u, u} B S hS f hf).map g)
  exact e ▸ IsIso.comp_isIso' h₁ h₂

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison `α_U : G_U ⟶ G|_U` of the glueing is invertible.**  At a geometric point
`ȳ` of `U` with image `x̄` in `W`, the unit of `j_{U!}` is invertible on the stalk because `x̄`
lifts uniquely to `U`, and the restriction of the first coprojection has, by Equation 08GT, the
stalk at `x̄` of that coprojection, which is invertible. -/
theorem isIso_edsGlueαU : IsIso (edsGlueαU B S hS hsq GU H θ) := by
  refine isIso_of_isIso_geometricModuleStalk B S hS _ (edsOpen B S hS hsq).2
    (etaleRingSheaf B S hS (edsOpen B S hS hsq)) _ fun y => ?_
  refine isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ y ?_
  have hx : (geometricPointMap (edsOpenHom B S hS hsq).hom y).image ∈
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) :=
    (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo hsq.isOpenSubspace
      _).1 ⟨tautologicalGeometricPointLift B S hS (edsOpenHom B S hS hsq) y⟩
  have := unique_geometricPointLift_edsOpenHom_of_mem B S hS hsq _ hx
  exact isIso_sheafFiber_unit_comp_pullback_map B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) y GU _
    (isIso_sheafFiber_edsGlue_inl_of_mem B S hS hsq GU H θ _ hx)

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison `α_V : H ⟶ G|_V` of the glueing is invertible.**  At a geometric point `ȳ`
of `V` over a point `x̄ ∉ U`, the unit of `j_{V!}` is invertible on the stalk because `x̄` lifts
uniquely to `V`, and the restriction of the second coprojection has, by Equation 08GT, the stalk
at `x̄` of that coprojection, which is invertible.  At a point `ȳ` over `U`, `ȳ` lifts to the
intersection, where the restriction of `α_V` is `θ` followed by the restriction of `α_U`,
which is invertible. -/
theorem isIso_edsGlueαV : IsIso (edsGlueαV B S hS hsq GU H θ) := by
  have hU := isIso_edsGlueαU B S hS hsq GU H θ
  have hP : IsIso ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).map (edsGlueαV B S hS hsq GU H θ)) := by
    rw [GlueSquare.r₂_map_glueαV]
    infer_instance
  have hP' : IsIso ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsInter B S hS hsq))).map
      ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map (edsGlueαV B S hS hsq GU H θ))) :=
    Iso.isIso_hom ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsInter B S hS hsq))).mapIso
      (@asIso _ _ _ _ ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map (edsGlueαV B S hS hsq GU H θ)) hP))
  refine isIso_of_isIso_geometricModuleStalk B S hS _ (edsEtale B S hS hsq).2
    (etaleRingSheaf B S hS (edsEtale B S hS hsq)) _ fun y => ?_
  refine isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ y ?_
  by_cases hx : (geometricPointMap (edsEtaleHom B S hS hsq).hom y).image ∈
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
  · have := unique_geometricPointLift_edsSnd_of_mem B S hS hsq y hx
    exact (isIso_sheafFiber_etaleModulePullback_map_iff B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (default : GeometricPointLift B S hS (edsSnd B S hS hsq).hom y)
      (edsGlueαV B S hS hsq GU H θ)).1
        inferInstance
  · have := unique_geometricPointLift_edsEtaleHom_of_notMem B S hS hsq _ hx
    exact isIso_sheafFiber_unit_comp_pullback_map B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) y H _
      (isIso_sheafFiber_edsGlue_inr_of_notMem B S hS hsq GU H θ _ hx)

end Construction

/-- **Glueing across an elementary distinguished square.**  Given an `𝒪_W`-module `F`, modules
`G_U` on the open subspace and `H` on the étale member mapping to the restrictions of `F`, and an
identification `θ : H|_P ≅ G_U|_P` over the intersection compatible with the two maps to `F`,
there is an `𝒪_W`-module `G` with a map to `F` whose restrictions to `U` and to `V` are `G_U` and
`H`, compatibly with the maps to `F`. -/
theorem exists_glue_hom_of_isElementaryDistinguishedSquare
    (F : Modules.{u, u} B S hS W.1 W.2)
    (GU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)
    (H : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (ψU : GU ⟶ (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj F)
    (ψV : H ⟶ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj F)
    (θ : (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj H ≅
      (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)).obj GU)
    (hθ : θ.hom ≫ (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
          (isEtale_edsFst B S hS hsq)).map ψU ≫ (edsFactorIsoOpen B S hS hsq).hom.app F =
      (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).map ψV ≫
        (edsFactorIsoEtale B S hS hsq).hom.app F) :
    ∃ (G : Modules.{u, u} B S hS W.1 W.2) (ψ : G ⟶ F)
      (αU : GU ⟶ (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj G)
      (αV : H ⟶ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj G),
      IsIso αU ∧ IsIso αV ∧
        αU ≫ (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).map ψ = ψU ∧
        αV ≫ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).map ψ = ψV :=
  ⟨_, _, edsGlueαU B S hS hsq GU H θ, edsGlueαV B S hS hsq GU H θ,
    isIso_edsGlueαU B S hS hsq GU H θ, isIso_edsGlueαV B S hS hsq GU H θ,
    GlueSquare.glueαU_comp_map_glueDesc _ _ _ _ _ _ _ _ _ _ GU H θ F ψU ψV hθ,
    GlueSquare.glueαV_comp_map_glueDesc _ _ _ _ _ _ _ _ _ _ GU H θ F ψU ψV hθ⟩

end AlgebraicGeometry.Space

end
