module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartDerivedStalk

/-!
# The chart identification of Stacks 0DJ8 (2), transposed across the derived Spec–Γ adjunction

`AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeMap` is an eight-factor composite in
`D(𝒪_{X'}(U'))`, and the first of its factors is the unit of the derived Spec–Γ adjunction of
Stacks 06Z0. The remaining seven are all `RΓ(U', -)` of morphisms of sheaves on
`Spec 𝒪_{X'}(U')`. So the whole map is the adjoint transpose of a single morphism

`(RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U'))^~  ⟶  L(U' ⟶ X')^* L(g')^* K`

of complexes of sheaves on `Spec 𝒪_{X'}(U')`, and the transpose is recovered from it by the
triangle identity. This module performs that transposition, which is the first step of comparing
the chart identification with the derived-pullback stalk comparison: the unit and the counit of
Stacks 06Z0 disappear from the comparison, and what is left is a statement about derived
pullbacks and sheafification only.

The reason the step is worth isolating is that the counit which the triangle identity consumes is
*exactly* the counit that `AlgebraicGeometry.tildeDerivedSectionsIso` — hence
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` at `U'` — is built from. So the
transposition is not bookkeeping that is undone later: it cancels the two Spec–Γ factors of the
comparison against each other.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeTildeMap`: the morphism displayed above,
  the six factors of `sectionsBaseChangeMap` other than the Spec–Γ unit and the identification
  `AlgebraicGeometry.derivedTildeCompι`.
* `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeSheafMap`: the same read on
  `derivedTilde ⋙ ι`, which is the left adjoint of the derived Spec–Γ adjunction.

## Main results

* `StacksDraft.AdjunctionTranspose.map_comp_counit_of_eq_unit_comp`: a morphism which is the
  adjoint transpose of `Θ` is carried back to `Θ` by the left adjoint and the counit.
* `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeMap_eq_unit_comp`: the chart
  identification *is* that adjoint transpose.
* `AlgebraicGeometry.BaseChangeChart.derivedTilde_map_sectionsBaseChangeMap_comp_counit`:
  **the transposition.** Sheafifying the chart identification and composing with the derived
  Spec–Γ counit gives `sectionsBaseChangeSheafMap` back.

## Implementation notes

The transposition lemma is stated and proved in a namespace of its own, for a free adjunction
between free categories, and applied to the derived Spec–Γ adjunction afterwards. Proving it in
place fails: `CategoryTheory.Adjunction.counit_naturality` does not rewrite against the
component of the counit at a derived pullback of a derived pullback, the two spellings of the
category of modules on a scheme carrying two `Category` instances which are definitionally but
not reducibly equal. With every category, functor and object a variable there is one instance in
sight and the rewrite is immediate.

`sectionsBaseChangeSheafMap` is the composite of `derivedTildeCompι` with
`sectionsBaseChangeTildeMap` rather than a seven-factor composite of its own, so that the
`derivedTildeCompι` factor can be cancelled against the one inside
`AlgebraicGeometry.tildeDerivedSectionsIso` without being re-derived.

No tag attribute is placed here: nothing below is a clause of Stacks 0DJ8. The tag belongs on the
three-way equivalence, and this is an input to it.

*Where the comparison is completed.* What
`extendScalars_map_sectionsBaseChangeMap_comp` leaves of the comparison is this: the derived stalk
at `y` of `sectionsBaseChangeTildeMap`, followed by the stalk comparison for `U' ⟶ X'`, is the
source identification at `U`. That is
`AlgebraicGeometry.BaseChangeChart.derivedStalk_sectionsBaseChangeTildeMap_comp` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartMorphismMatch`, and
composing it with the transposition above gives
`AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq` there: the
germ-localized chart identification *is* the derived-pullback stalk comparison of Stacks 0098 at
`ch.incU' y`, read through `AlgebraicGeometry.derivedStalkAffineSectionsIso` at `U` and at `U'`.

That statement is a trade, factor by factor, against three coherences. Two are instances of one:
the coherence of the derived stalk formula of Stacks 0098 with the composition formula of
Stacks 0D5S, `AlgebraicGeometry.derivedPullbackStalkCompIso_eq_general` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionCoherence`;
`sectionsBaseChangeTildeMap` carries the composition isomorphism of Stacks 0D5S for each of the
two factorizations `Spec ch.c ≫ ch.incU` and `ch.incU' ≫ g'` of `Spec 𝒪_{X'}(U') ⟶ X`, and each
is traded for the two-step stalk computation along that factorization, unconditionally and at the
locally small model, which is the model the chart works at.

The third is the affine case of the same coherence, which no composition formula covers: that
`AlgebraicGeometry.derivedTildeStalkIso` at `𝒪_{X'}(U')`, read backwards along the affine
comparison square of Stacks 08DW, is the derived-pullback stalk comparison for `Spec ch.c`
followed by `derivedTildeStalkIso` at `𝒪_X(U)`, under the composition isomorphism for derived
extension of scalars along the two germ maps. Precisely, for `N` in `D(𝒪_X(U))`,

`𝒪_{Spec 𝒪_{X'}(U'), y} ⊗ᴸ_{𝒪_{X'}(U')} (𝒪_{X'}(U') ⊗ᴸ_{𝒪_X(U)} N) ≅ (Ñ ⊗ᴸ)^~_y`

computed through `Ñ` on `Spec 𝒪_{X'}(U')` and computed through `Ñ` on `Spec 𝒪_X(U)` agree. That
is `AlgebraicGeometry.derivedAffineTildeStalkLeft_eq_right` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineTildeStalkCoherence`: both sides
are morphisms of functors on `D(𝒪_X(U))`, so
`StacksDraft.LeftResolutions.natTrans_eq_of_left_resolutions` reduces the statement to the K-flat
complexes of `𝒪_X(U)`-modules, and its degreewise heart is the *underived* compatibility
`AlgebraicGeometry.affineTildeStalkCompatibility` — the stalk of Stacks 01HV, the affine pullback
isomorphism of Stacks 01I9 and the stalk formula of Stacks 0098 agree at a module, the analogue,
for a `Spec` of a ring map against sheafification, of what
`Stacks.ModuleSkyscraper.pullbackStalkIso_comp_app` is for a composition of morphisms.

*Why the uniqueness route does not reach further.* One cannot instead pin the whole composite down
by `AlgebraicGeometry.derivedPullbackStalkIso_hom_eq_of_kFlat` at `g'` and `ch.incU' y`. That
lemma asks for a morphism of functors on the *whole* of `D(𝒪_X)` and tests it at K-flat
complexes; a candidate built from the chart identification is defined only where `K` has
quasi-coherent cohomology sheaves, since both `AlgebraicGeometry.tildeDerivedSectionsIso` and
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` take that as data and the chart
identification is invertible only there, and a K-flat complex of `𝒪_X`-modules need not have
quasi-coherent cohomology. The candidate that *is* defined on all of `D(𝒪_X)` carries no
sections at all — it is built from the stalk comparisons alone — and the equation it has to
satisfy is exactly `AlgebraicGeometry.derivedPullbackStalkCompIso_hcomp`, which is why that is
proved rather than assumed. The two transposition statements above are what survives of the route
on the sections side: they are equations between morphisms, at one `K`, and they need no
uniqueness argument.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft.AdjunctionTranspose

/-- **The adjoint transpose, read backwards.** If `u` is the adjoint transpose `η_M ≫ R(Θ)` of a
morphism `Θ : L M ⟶ N`, then `L(u)` composed with the counit at `N` is `Θ`. This is one half of
the bijection `CategoryTheory.Adjunction.homEquiv`, written as an equation so that a consumer
holding a composite in the shape of a transpose can replace it. -/
public theorem map_comp_counit_of_eq_unit_comp {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M : C} {N : D} (Θ : L.obj M ⟶ N)
    (u : M ⟶ R.obj N) (hu : u = adj.unit.app M ≫ R.map Θ) :
    L.map u ≫ adj.counit.app N = Θ := by
  subst hu
  simp


/-- **The adjoint transpose, read backwards through a presentation of the left adjoint.** If `u`
is the adjoint transpose of `e.hom ≫ Θ` for an isomorphism `e : L ≅ L'` of left adjoints, then
`L'(u)`, read back along `e` and composed with the counit, is `Θ`. This is the shape a consumer
meets when the left adjoint is presented as a derived functor through an identification. -/
public theorem map_comp_inv_comp_counit_of_eq_unit_comp {C D : Type*} [Category* C]
    [Category* D] {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (e : L ≅ L') {M : C} {N : D}
    (Θ : L'.obj M ⟶ N) (u : M ⟶ R.obj N)
    (hu : u = adj.unit.app M ≫ R.map (e.hom.app M ≫ Θ)) :
    L'.map u ≫ e.inv.app (R.obj N) ≫ adj.counit.app N = Θ := by
  rw [← Category.assoc, e.inv.naturality u, Category.assoc,
    map_comp_counit_of_eq_unit_comp adj (e.hom.app M ≫ Θ) u hu, ← Category.assoc,
    e.inv_hom_id_app, Category.id_comp]


/-- **One naturality square against a functor applied to a determined composite.** If `α` is a
morphism of functors `F ⟶ G ⋙ H` and `G(φ) ≫ b` is known to be `Θ`, then `F(φ)` followed by `α`
at the target and `H(b)` is `α` at the source followed by `H(Θ)`; a further morphism `c` is
carried along, which is the shape a consumer with a longer composite has. -/
public theorem map_comp_app_comp_map {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (α : F ⟶ G ⋙ H) {M N : C} (φ : M ⟶ N) {W : D}
    (b : G.obj N ⟶ W) {Θ : G.obj M ⟶ W} (h : G.map φ ≫ b = Θ) {Z : E} (c : H.obj W ⟶ Z) :
    F.map φ ≫ α.app N ≫ H.map b ≫ c = α.app M ≫ H.map Θ ≫ c := by
  subst h
  have hnat := α.naturality φ
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hnat, Category.assoc]
  rfl

end StacksDraft.AdjunctionTranspose

namespace AlgebraicGeometry

/-- The three factors of `AlgebraicGeometry.derivedStalkAffineSectionsIso`, as an equation of
morphisms rather than of isomorphisms. -/
public theorem derivedStalkAffineSectionsIso_hom {A : CommRingCat.{u}} {Z : Scheme.{u}}
    (i : Spec A ⟶ Z) (y : Spec A) (K : DerivedCategory Z.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Z.Modules n).obj K).IsQuasicoherent) :
    (derivedStalkAffineSectionsIso i y K hK).hom =
      (derivedTildeStalkIso A y).hom.app ((affineDerivedSections i).obj K) ≫
        (derivedStalkFunctor y).map (tildeDerivedSectionsIso i K hK).hom ≫
        (derivedPullbackStalkIso i y).hom.app K :=
  rfl

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The chart identification of Stacks 0DJ8 (2), before taking derived sections.** On a chart,
the morphism

`(RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U'))^~  ⟶  L(U' ⟶ X')^* L(g')^* K`

in `D(𝒪_{Spec 𝒪_{X'}(U')})`: the affine comparison square of Stacks 08DW read backwards, the
derived Spec–Γ counit at `K|_U` pulled back to `Spec 𝒪_{X'}(U')`, and the two composition
isomorphisms of Stacks 0D5S for the two factorizations of `Spec 𝒪_{X'}(U') ⟶ X`. -/
public def sectionsBaseChangeTildeMap (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) :
    (tilde.functor ch.A').mapDerivedCategory.obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K)) ⟶
      (Stacks.Duality.derivedPullback ch.incU').obj
        ((Stacks.Duality.derivedPullback g').obj K) :=
  (affinePullbackComparison ch.A ch.A' ch.c).inv.app
      ((affineDerivedSections ch.incU).obj K) ≫
    (Stacks.Duality.derivedPullback (Spec.map ch.c)).map
      ((derivedTildeCompι ch.A).inv.app ((affineDerivedSections ch.incU).obj K)) ≫
    (Stacks.Duality.derivedPullback (Spec.map ch.c)).map
      ((derivedTildeGlobalSectionsAdjunction ch.A).val.counit.app
        ((Stacks.Duality.derivedPullback ch.incU).obj K)) ≫
    (Stacks.Duality.derivedPullbackCompIso (Spec.map ch.c) ch.incU).hom.app K ≫
    eqToHom (congrArg
      (fun t : Spec ch.A' ⟶ X => (Stacks.Duality.derivedPullback t).obj K) ch.wU'U.symm) ≫
    (Stacks.Duality.derivedPullbackCompIso ch.incU' g').inv.app K

/-- `sectionsBaseChangeTildeMap` read on the left adjoint `derivedTilde ⋙ ι` of the derived
Spec–Γ adjunction of Stacks 06Z0, which is the shape the triangle identity consumes. -/
public def sectionsBaseChangeSheafMap (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) :
    (derivedTilde ch.A' ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec ch.A').Modules)
          (SheafOfModules.isQuasicoherent (Spec ch.A').ringCatSheaf)).ι).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K)) ⟶
      (Stacks.Duality.derivedPullback ch.incU').obj
        ((Stacks.Duality.derivedPullback g').obj K) :=
  (derivedTildeCompι ch.A').hom.app _ ≫ ch.sectionsBaseChangeTildeMap K

/-- **The chart identification is an adjoint transpose.** `sectionsBaseChangeMap` is the derived
Spec–Γ unit followed by derived sections of `sectionsBaseChangeSheafMap`: its first factor is
that unit and its other seven are `RΓ(U', -)` of the factors of
`sectionsBaseChangeSheafMap`. -/
public theorem sectionsBaseChangeMap_eq_unit_comp (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) :
    ch.sectionsBaseChangeMap K =
      (derivedTildeGlobalSectionsAdjunction ch.A').val.unit.app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K)) ≫
        (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map (ch.sectionsBaseChangeSheafMap K) := by
  dsimp only [sectionsBaseChangeMap, sectionsBaseChangeSheafMap, sectionsBaseChangeTildeMap]
  simp only [Functor.map_comp]

/-- **The transposition.** Sheafifying the chart identification of Stacks 0DJ8 (2) and composing
with the derived Spec–Γ counit at `L(U' ⟶ X')^* L(g')^* K` returns `sectionsBaseChangeSheafMap`:
the unit and the counit of Stacks 06Z0 cancel by the triangle identity.

The counit here is the one `AlgebraicGeometry.tildeDerivedSectionsIso` at `U'` is built from, so
this is what removes both Spec–Γ factors from the comparison of the chart identification with the
derived-pullback stalk comparison. -/
public theorem derivedTilde_map_sectionsBaseChangeMap_comp_counit
    (ch : BaseChangeChart f g f' g') (K : DerivedCategory X.Modules) :
    (derivedTilde ch.A' ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec ch.A').Modules)
          (SheafOfModules.isQuasicoherent (Spec ch.A').ringCatSheaf)).ι).map
          (ch.sectionsBaseChangeMap K) ≫
        (derivedTildeGlobalSectionsAdjunction ch.A').val.counit.app
          ((Stacks.Duality.derivedPullback ch.incU').obj
            ((Stacks.Duality.derivedPullback g').obj K)) =
      ch.sectionsBaseChangeSheafMap K :=
  StacksDraft.AdjunctionTranspose.map_comp_counit_of_eq_unit_comp
    (derivedTildeGlobalSectionsAdjunction ch.A').val (ch.sectionsBaseChangeSheafMap K)
    (ch.sectionsBaseChangeMap K) (ch.sectionsBaseChangeMap_eq_unit_comp K)

/-- **The derived sheafification of the chart identification against the Spec–Γ counit.**
Sheafifying `sectionsBaseChangeMap` degreewise and composing with
`AlgebraicGeometry.tildeDerivedSectionsIso` at `U'` — which is `derivedTildeCompι` read backwards
followed by the derived Spec–Γ counit — returns `sectionsBaseChangeTildeMap`.

This is `derivedTilde_map_sectionsBaseChangeMap_comp_counit` with the `derivedTildeCompι` factor
of `sectionsBaseChangeSheafMap` cancelled against the one inside `tildeDerivedSectionsIso`. -/
public theorem tilde_map_sectionsBaseChangeMap_comp_tildeDerivedSectionsIso
    (ch : BaseChangeChart f g f' g') (K : DerivedCategory X.Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      ((Stacks.Duality.derivedPullback g').obj K)).IsQuasicoherent) :
    (tilde.functor ch.A').mapDerivedCategory.map (ch.sectionsBaseChangeMap K) ≫
        (tildeDerivedSectionsIso ch.incU' ((Stacks.Duality.derivedPullback g').obj K) hK').hom =
      ch.sectionsBaseChangeTildeMap K :=
  StacksDraft.AdjunctionTranspose.map_comp_inv_comp_counit_of_eq_unit_comp
    (derivedTildeGlobalSectionsAdjunction ch.A').val (derivedTildeCompι ch.A')
    (ch.sectionsBaseChangeTildeMap K) (ch.sectionsBaseChangeMap K)
    (ch.sectionsBaseChangeMap_eq_unit_comp K)

/-- **The transposition at a point.** The chart identification of Stacks 0DJ8 (2), base changed
along the germ map at `y` and read through `AlgebraicGeometry.derivedStalkAffineSectionsIso` at
`U'` on the target, is the derived stalk at `y` of `sectionsBaseChangeTildeMap`, followed by the
derived-pullback stalk comparison for `U' ⟶ X'`.

This is the whole Spec–Γ content of the comparison of the chart identification with the
derived-pullback stalk comparison of Stacks 0098: the unit of Stacks 06Z0 inside
`sectionsBaseChangeMap` and the counit inside `derivedStalkAffineSectionsIso` cancel, and what is
left mentions only derived pullbacks, derived sheafification and the stalk comparisons. -/
public theorem extendScalars_map_sectionsBaseChangeMap_comp
    (ch : BaseChangeChart f g f' g') (K : DerivedCategory X.Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      ((Stacks.Duality.derivedPullback g').obj K)).IsQuasicoherent) (y : Spec ch.A') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A' y)).functor.map (ch.sectionsBaseChangeMap K) ≫
        (derivedStalkAffineSectionsIso ch.incU' y
          ((Stacks.Duality.derivedPullback g').obj K) hK').hom =
      (derivedTildeStalkIso ch.A' y).hom.app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K)) ≫
        (derivedStalkFunctor y).map (ch.sectionsBaseChangeTildeMap K) ≫
        (derivedPullbackStalkIso ch.incU' y).hom.app
          ((Stacks.Duality.derivedPullback g').obj K) := by
  rw [derivedStalkAffineSectionsIso_hom]
  exact StacksDraft.AdjunctionTranspose.map_comp_app_comp_map
    (derivedTildeStalkIso ch.A' y).hom (ch.sectionsBaseChangeMap K)
    (tildeDerivedSectionsIso ch.incU' ((Stacks.Duality.derivedPullback g').obj K) hK').hom
    (ch.tilde_map_sectionsBaseChangeMap_comp_tildeDerivedSectionsIso K hK')
    ((derivedPullbackStalkIso ch.incU' y).hom.app
      ((Stacks.Duality.derivedPullback g').obj K))

end BaseChangeChart

end AlgebraicGeometry

end
