module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# Descent along a presentation of a morphism out of the structure sheaf

Let `X = U/R` be a presentation of an algebraic space, and let `(M, τ)` be a quasi-coherent module
on the presenting scheme `U` with a scheme transition satisfying the cocycle and unit conditions,
so that it descends to a quasi-coherent `𝒪_X`-module `D(M)`
(`AlgebraicGeometry.Space.presentationDescendedModule`, Stacks 03M3).  This file descends a unit:
a morphism `ν : 𝒪_U ⟶ M^a` on the atlas which carries the identification `t^*𝒪_U ≅ 𝒪_R ≅ s^*𝒪_U`
of Stacks 03LU to the transition `τ^a` descends to a unique morphism `𝒪_X ⟶ D(M)` whose inverse
image along the atlas is `ν`, through Stacks 03LU and the chart identification.  This is the
companion of `AlgebraicGeometry.Space.existsUnique_presentationDescendedTensorHom` for the unit,
the step of Stacks 084D that descends the unit of the twists.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentSheavesUnit`: `𝒪_X` as a quasi-coherent `𝒪_X`-module.
* `AlgebraicGeometry.Space.presentationDescendedUnitChartHom`: the morphism on the atlas to be
  descended.
* `AlgebraicGeometry.Space.presentationDescendedUnitHom`: **the descended unit**.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompHom_unit`: the composition law of the
  identification `h^*𝒪 ≅ 𝒪` of Stacks 03LU, in the direction of
  `AlgebraicGeometry.Space.modulePullbackCompHom`.
* `AlgebraicGeometry.Space.spaceBaseDescent_structureSheaf`: **the canonical transition morphism of
  the inverse image of `𝒪_X` to a groupoid is the identification `t^*𝒪 ≅ 𝒪 ≅ s^*𝒪`.**
* `AlgebraicGeometry.Space.transitionCommutes_spaceBaseDescent_structureSheaf`: a morphism out of
  `𝒪_U` compatible with the transitions gives a morphism out of `φ^*𝒪_X` compatible with the
  canonical transition morphisms.
* `AlgebraicGeometry.Space.existsUnique_presentationDescendedUnitHom`, with
  `AlgebraicGeometry.Space.presentationDescendedUnitHom_spec` and
  `AlgebraicGeometry.Space.presentationDescendedUnitHom_unique`: **descent of a unit along a
  presentation**.

## Implementation notes

The compatibility is proved at a general groupoid, morphism `φ` and module `D`
(`AlgebraicGeometry.Space.transitionCommutes_spaceBaseDescent_structureSheaf`, itself an instance
of an abstract lemma at variables) and instantiated once at the presentation, with every argument
explicit.  Restating `AlgebraicGeometry.Space.spaceBaseDescent_structureSheaf` at the atlas of a
presentation and comparing it with the instance exhausts even fifteen times the default heartbeat
budget, although each of the two sides, and each factor of them, is compared with its instance by
`rfl` at low cost; stating the whole compatibility generically avoids the comparison.  The
crossing between the groupoid module `(e.functor.obj Y).F.obj` and the inverse
image `φ^*Y` goes through
`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_compatible_iff`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The abstract shape of `AlgebraicGeometry.Space.spaceBaseDescent_structureSheaf`, at
variables. -/
private theorem unflatten_unit_of_readings {𝒞 : Type*} [Category 𝒞] {a b c d e : 𝒞}
    (cHt : a ⟶ b) (Ut : b ⟶ e) (V : a ⟶ e) (ht : cHt ≫ Ut = V) (tr : b ⟶ c) (Us : c ⟶ e)
    (htr : tr ≫ Us = Ut) (cI : c ⟶ d) (cH : d ⟶ c) (hinv : cI ≫ cH = 𝟙 c) (W : d ⟶ e)
    (hs : cH ≫ Us = W) :
    V = (cHt ≫ tr ≫ cI) ≫ W := by
  rw [← ht, ← hs, ← htr]
  simp only [Category.assoc, reassoc_of% hinv]

/-- The abstract shape of the compatibility in
`AlgebraicGeometry.Space.existsUnique_presentationDescendedUnitHom`, at variables. -/
private theorem descend_unit_compatible_of_readings {CU CV : Type*} [Category CU] [Category CV]
    (Pt Ps : CU ⥤ CV) {Y₀ I A YK : CU} {I' : CV} (pA : Y₀ ⟶ I) (ν : I ⟶ A) (cK : YK ≅ A)
    (δ₀ : Pt.obj Y₀ ⟶ Ps.obj Y₀) (δK : Pt.obj YK ⟶ Ps.obj YK) (αK : Pt.obj A ⟶ Ps.obj A)
    (tI : Pt.obj I ≅ I') (sI : Ps.obj I ≅ I')
    (hL : Pt.map pA ≫ tI.hom = δ₀ ≫ Ps.map pA ≫ sI.hom)
    (hK : δK ≫ Ps.map cK.hom = Pt.map cK.hom ≫ αK)
    (hν : (tI.hom ≫ sI.inv) ≫ Ps.map ν = Pt.map ν ≫ αK) :
    δ₀ ≫ Ps.map (pA ≫ ν ≫ cK.inv) = Pt.map (pA ≫ ν ≫ cK.inv) ≫ δK := by
  have hK' : αK ≫ Ps.map cK.inv = Pt.map cK.inv ≫ δK := by
    rw [← cancel_epi (Pt.map cK.hom), ← reassoc_of% hK, ← Pt.map_comp_assoc, Iso.hom_inv_id,
      Pt.map_id, Category.id_comp, ← Ps.map_comp, Iso.hom_inv_id, Ps.map_id, Category.comp_id]
  have hL' : δ₀ ≫ Ps.map pA = Pt.map pA ≫ tI.hom ≫ sI.inv := by
    rw [reassoc_of% hL, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc] at hν
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hL', reassoc_of% hν, hK']

section Unit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The composition law of the identification `h^*𝒪 ≅ 𝒪` of Stacks 03LU**, in the direction of
`AlgebraicGeometry.Space.modulePullbackCompHom`: for `f : X ⟶ Y` and `g : Y ⟶ Z`, the comparison
`f^*g^*𝒪_Z ⟶ (f ≫ g)^*𝒪_Z` followed by the identification for `f ≫ g` is the inverse image along
`f` of the identification for `g` followed by the identification for `f`. -/
theorem modulePullbackCompHom_unit {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompHom B S hS f g (SheafOfModules.unit (structureRingSheaf B S hS Z)) ≫
        (modulePullbackUnitIso B S hS (f ≫ g)).hom =
      (modulePullback B S hS f).map (modulePullbackUnitIso B S hS g).hom ≫
        (modulePullbackUnitIso B S hS f).hom := by
  have h := modulePullbackTriangle_hom_app_unit_comp B S hS f g rfl
  rw [modulePullbackTriangle_rfl, Iso.symm_hom] at h
  exact (congrArg (modulePullbackCompHom B S hS f g _ ≫ ·) h).symm.trans
    ((modulePullbackCompIso B S hS f g).hom_inv_id_app_assoc _ _)

/-- Transporting `𝒪` along an equality of morphisms is compatible with the identifications
`h^*𝒪 ≅ 𝒪` of Stacks 03LU. -/
theorem pullbackTransport_unit {T X : AlgebraicSpaces B S hS} {f g : T ⟶ X} (h : f = g) :
    pullbackTransport (SheafOfModules.unit (structureRingSheaf B S hS X)) h ≫
        (modulePullbackUnitIso B S hS g).hom =
      (modulePullbackUnitIso B S hS f).hom := by
  subst h
  exact Category.id_comp _

/-- **Unflattening the transport of `𝒪` is the identification of Stacks 03LU.**  For
`a, b : V ⟶ U` and `φ : U ⟶ X` with `a ≫ φ = b ≫ φ`, the identification `a^*φ^*𝒪_X ⟶ b^*φ^*𝒪_X`
obtained by unflattening the transport along `a ≫ φ = b ≫ φ` is carried, through the
identifications of Stacks 03LU along `φ`, `a` and `b`, to the identity of `𝒪_V`. -/
theorem modulePullbackUnflatten_pullbackTransport_unit {V U X : AlgebraicSpaces B S hS}
    (a b : V ⟶ U) (φ : U ⟶ X) (h : a ≫ φ = b ≫ φ) :
    (modulePullback B S hS a).map (modulePullbackUnitIso B S hS φ).hom ≫
        (modulePullbackUnitIso B S hS a).hom =
      modulePullbackUnflatten φ
          (pullbackTransport (SheafOfModules.unit (structureRingSheaf B S hS X)) h) ≫
        (modulePullback B S hS b).map (modulePullbackUnitIso B S hS φ).hom ≫
          (modulePullbackUnitIso B S hS b).hom := by
  have e := unflatten_unit_of_readings _ _ _ (modulePullbackCompHom_unit B S hS a φ) _ _
    (pullbackTransport_unit B S hS h) _ _
    (modulePullbackCompInv_comp_compHom B S hS b φ _) _
    (modulePullbackCompHom_unit B S hS b φ)
  have e' := modulePullbackUnflatten_eq_compHom B S hS φ
    (pullbackTransport (SheafOfModules.unit (structureRingSheaf B S hS X)) h)
  rw [e']
  exact e

/-- **The canonical transition morphism of the inverse image of `𝒪_X` to a groupoid is the
identification `t^*𝒪 ≅ 𝒪 ≅ s^*𝒪`.**  For a groupoid `(U, R, s, t, c)` in algebraic spaces and
`φ : U ⟶ X` with `t ≫ φ = s ≫ φ`, the canonical transition morphism
`AlgebraicGeometry.Space.spaceBaseDescent` of `φ^*𝒪_X` is carried, through the identifications
of Stacks 03LU along `φ`, `t` and `s`, to the identity of `𝒪_R`. -/
theorem spaceBaseDescent_structureSheaf {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφ : G.target ≫ φ = G.source ≫ φ) :
    (modulePullback B S hS G.target).map (modulePullbackUnitIso B S hS φ).hom ≫
        (modulePullbackUnitIso B S hS G.target).hom =
      spaceBaseDescent B S hS G φ hφ (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePullback B S hS G.source).map (modulePullbackUnitIso B S hS φ).hom ≫
          (modulePullbackUnitIso B S hS G.source).hom :=
  modulePullbackUnflatten_pullbackTransport_unit B S hS G.target G.source φ hφ

/-- **A morphism out of `𝒪_X` read on a groupoid through Stacks 03LU is compatible with the
canonical transition morphisms.**  For a groupoid `(U, R, s, t, c)` in algebraic spaces,
`φ : U ⟶ X` with `t ≫ φ = s ≫ φ`, an `𝒪_X`-module `D` with an identification `c : φ^*D ≅ F`
carrying the canonical transition morphism of `φ^*D` to a transition `α` of `F`, and a morphism
`ν : 𝒪_U ⟶ F` carrying the identification `t^*𝒪_U ≅ 𝒪_R ≅ s^*𝒪_U` to `α`, the morphism
`φ^*𝒪_X ≅ 𝒪_U ⟶ F ≅ φ^*D` carries the canonical transition morphism of `φ^*𝒪_X` to that of
`φ^*D`. -/
theorem transitionCommutes_spaceBaseDescent_structureSheaf {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (D : Modules.{u, u} B S hS X.1 X.2)
    {F : Modules.{u, u} B S hS G.objects.1 G.objects.2} (c : (modulePullback B S hS φ).obj D ≅ F)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (hK : TransitionCommutes B S hS (spaceBaseDescent B S hS G φ hφ D) α c.hom)
    (ν : SheafOfModules.unit (structureRingSheaf B S hS G.objects) ⟶ F)
    (hν : TransitionCommutes B S hS
      ((modulePullbackUnitIso B S hS G.target).hom ≫ (modulePullbackUnitIso B S hS G.source).inv)
      α ν) :
    TransitionCommutes B S hS
      (spaceBaseDescent B S hS G φ hφ (SheafOfModules.unit (structureRingSheaf B S hS X)))
      (spaceBaseDescent B S hS G φ hφ D) ((modulePullbackUnitIso B S hS φ).hom ≫ ν ≫ c.inv) :=
  descend_unit_compatible_of_readings (modulePullback B S hS G.target)
    (modulePullback B S hS G.source) _ ν c _ _ α (modulePullbackUnitIso B S hS G.target)
    (modulePullbackUnitIso B S hS G.source) (spaceBaseDescent_structureSheaf B S hS G φ hφ) hK hν

end Unit

section Descent

attribute [local irreducible] CategoryTheory.yoneda

/-- The structure sheaf `𝒪_X` of an algebraic space, as a quasi-coherent `𝒪_X`-module. -/
abbrev quasicoherentSheavesUnit {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS) : QuasicoherentSheaves.{u, u} B S hS X.obj X.property :=
  ⟨SheafOfModules.unit (structureRingSheaf B S hS X), SheafOfModules.isQuasicoherentOnSite_unit _⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (hc : PresentationSchemeCocycle P M τ) (hu : PresentationSchemeUnit P M τ)
  (ν : SheafOfModules.unit (structureRingSheaf B S hS (presentationGroupoid P).objects) ⟶
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj)
  (hν : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    ((modulePullbackUnitIso B S hS (presentationGroupoid P).target).hom ≫
      (modulePullbackUnitIso B S hS (presentationGroupoid P).source).inv)
    (presentationSchemeTransition P M τ) ν)

/-- The morphism on the atlas to be descended: the inverse image of `𝒪_X` along the atlas is
`𝒪_U` through Stacks 03LU, followed by `ν` and the chart identification of `D(M)`. -/
def presentationDescendedUnitChartHom :
    (modulePullback B S hS (presentationAtlas P)).obj (quasicoherentSheavesUnit X).obj ⟶
      (modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P M τ hc hu).obj :=
  (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫ ν ≫
    (presentationDescendedModuleChartIso P M τ hc hu).inv

/-- The chart morphism, written out. -/
theorem presentationDescendedUnitChartHom_eq :
    presentationDescendedUnitChartHom P τ hc hu ν =
      (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫ ν ≫
        (presentationDescendedModuleChartIso P M τ hc hu).inv :=
  rfl

include hν in
/-- The chart morphism carries the canonical transition morphism of the inverse image of `𝒪_X`
to that of the inverse image of `D(M)`. -/
theorem presentationDescendedUnitChartHom_transitionCommutes :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) (quasicoherentSheavesUnit X).obj)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj)
      (presentationDescendedUnitChartHom P τ hc hu ν) :=
  transitionCommutes_spaceBaseDescent_structureSheaf B S hS (presentationGroupoid P)
    (presentationAtlas P) (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj
    (presentationDescendedModuleChartIso P M τ hc hu) (presentationSchemeTransition P M τ)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent P τ hc hu) ν hν

include hν in
/-- The chart morphism is a morphism of quasi-coherent modules on the groupoid of the
presentation. -/
theorem presentationDescendedUnitChartHom_compatible :
    QuasicoherentModule.Compatible
      (M := (presentationQuasicoherentEquivalence P).functor.obj (quasicoherentSheavesUnit X))
      (N := (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P M τ hc hu))
      (presentationDescendedUnitChartHom P τ hc hu ν) :=
  (presentationQuasicoherentEquivalence_compatible_iff P _).2
    (presentationDescendedUnitChartHom_transitionCommutes P τ hc hu ν hν)

/-- The groupoid morphism of the chart morphism. -/
def presentationDescendedUnitGroupoidHom :
    (presentationQuasicoherentEquivalence P).functor.obj (quasicoherentSheavesUnit X) ⟶
      (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P M τ hc hu) :=
  QuasicoherentModule.homMk (presentationDescendedUnitChartHom P τ hc hu ν)
    (presentationDescendedUnitChartHom_compatible P τ hc hu ν hν)

/-- The morphism of quasi-coherent `𝒪_X`-modules `𝒪_X ⟶ D(M)` corresponding to the groupoid
morphism of the chart morphism under the equivalence of Stacks 03M3. -/
def presentationDescendedUnitQuasicoherentHom :
    quasicoherentSheavesUnit X ⟶ presentationDescendedModule P M τ hc hu :=
  (presentationQuasicoherentEquivalence P).functor.preimage
    (presentationDescendedUnitGroupoidHom P τ hc hu ν hν)

/-- The image of the descended morphism under the equivalence of Stacks 03M3 is the groupoid
morphism of the chart morphism. -/
theorem functor_map_presentationDescendedUnitQuasicoherentHom :
    (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedUnitQuasicoherentHom P τ hc hu ν hν) =
      presentationDescendedUnitGroupoidHom P τ hc hu ν hν :=
  (presentationQuasicoherentEquivalence P).functor.map_preimage
    (presentationDescendedUnitGroupoidHom P τ hc hu ν hν)

/-- **The descent of a unit**: the morphism `𝒪_X ⟶ D(M)` corresponding, under the equivalence of
Stacks 03M3, to the morphism `ν` read on the atlas through Stacks 03LU and the chart
identification. -/
def presentationDescendedUnitHom :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (presentationDescendedModule P M τ hc hu).obj :=
  (presentationDescendedUnitQuasicoherentHom P τ hc hu ν hν).hom

/-- The inverse image along the atlas of the descended unit is the chart morphism. -/
theorem modulePullback_map_presentationDescendedUnitHom :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedUnitHom P τ hc hu ν hν) =
      presentationDescendedUnitChartHom P τ hc hu ν :=
  (presentationQuasicoherentEquivalence_functor_map_hom P _).symm.trans
    (congrArg QuasicoherentModule.Hom.hom
      (functor_map_presentationDescendedUnitQuasicoherentHom P τ hc hu ν hν))

/-- **The inverse image along the atlas of the descended unit is `ν`**, through Stacks 03LU and
the chart identification. -/
theorem presentationDescendedUnitHom_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedUnitHom P τ hc hu ν hν) ≫
        (presentationDescendedModuleChartIso P M τ hc hu).hom =
      (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫ ν :=
  (Iso.eq_comp_inv _).1
    (((modulePullback_map_presentationDescendedUnitHom P τ hc hu ν hν).trans
      (presentationDescendedUnitChartHom_eq P τ hc hu ν)).trans (Category.assoc _ _ _).symm)

/-- **The descended unit is unique**: a morphism `𝒪_X ⟶ D(M)` whose inverse image along the atlas
is `ν`, through Stacks 03LU and the chart identification, is the descended unit. -/
theorem presentationDescendedUnitHom_unique
    (ψ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (presentationDescendedModule P M τ hc hu).obj)
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P M τ hc hu).hom =
      (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫ ν) :
    ψ = presentationDescendedUnitHom P τ hc hu ν hν := by
  have h1 : (modulePullback B S hS (presentationAtlas P)).map ψ =
      presentationDescendedUnitChartHom P τ hc hu ν :=
    ((Iso.eq_comp_inv _).2 hψ).trans
      ((Category.assoc _ _ _).trans (presentationDescendedUnitChartHom_eq P τ hc hu ν).symm)
  have h2 : (presentationQuasicoherentEquivalence P).functor.map
      (ObjectProperty.homMk ψ : quasicoherentSheavesUnit X ⟶
        presentationDescendedModule P M τ hc hu) =
      (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedUnitQuasicoherentHom P τ hc hu ν hν) := by
    refine QuasicoherentModule.Hom.ext ?_
    refine (presentationQuasicoherentEquivalence_functor_map_hom P _).trans ?_
    refine Eq.trans ?_ (presentationQuasicoherentEquivalence_functor_map_hom P _).symm
    exact h1.trans (modulePullback_map_presentationDescendedUnitHom P τ hc hu ν hν).symm
  exact congrArg (fun k => k.hom)
    ((presentationQuasicoherentEquivalence P).functor.map_injective h2)

include hν in
/-- **Descent of a unit along a presentation.**  Let `X = U/R` be a presentation of an algebraic
space and `(M, τ)` a quasi-coherent module on the presenting scheme with a scheme transition
satisfying the cocycle and unit conditions.  A morphism `ν : 𝒪_U ⟶ M^a` on the atlas which
carries the identification `t^*𝒪_U ≅ 𝒪_R ≅ s^*𝒪_U` of Stacks 03LU to the transition `τ^a`
descends to a unique morphism `𝒪_X ⟶ D(M)` of `𝒪_X`-modules whose inverse image along the atlas
is `ν`, through Stacks 03LU and the chart identification. -/
theorem existsUnique_presentationDescendedUnitHom :
    ∃! ψ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
        (presentationDescendedModule P M τ hc hu).obj,
      (modulePullback B S hS (presentationAtlas P)).map ψ ≫
          (presentationDescendedModuleChartIso P M τ hc hu).hom =
        (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫ ν :=
  ⟨presentationDescendedUnitHom P τ hc hu ν hν,
    presentationDescendedUnitHom_spec P τ hc hu ν hν,
    fun ψ hψ => presentationDescendedUnitHom_unique P τ hc hu ν hν ψ hψ⟩

end Descent

end AlgebraicGeometry.Space

end
