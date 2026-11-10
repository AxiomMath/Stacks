module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.TwoIso

/-!
# The inverse image of a chart sheaf along the morphism of small étale ringed topoi

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `V` be an étale
scheme chart of `Y`.  This file identifies the inverse image `f_small⁻¹h_V` of the chart sheaf
along the morphism of small étale ringed topoi of Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom`) with the sheaf of chart maps over `f` into
`V`, that is with the sheaf represented by the cartesian base change `X ×_Y V`.

The morphism `f` is **not** assumed representable, so `X ×_Y V` is only an algebraic space étale
over `X` and not an étale scheme chart; what represents it on the small étale site is therefore
not an object of that site but the presheaf `AlgebraicGeometry.Space.chartFiber` of chart maps
over `f`, whose sections over a chart `U` of `X` are the morphisms `U ⟶ X ×_Y V` over `X`
(`AlgebraicGeometry.Space.chartFiberOfBaseChangeArrow`).  Accordingly the identification is
stated as a canonical map of presheaves from `chartFiber f V` into `f_small⁻¹h_V` which is a
local isomorphism, i.e. which exhibits `f_small⁻¹h_V` as the sheafification of `chartFiber f V`.

The construction compares the two descriptions of the sections of the direct image over `V`
which this development already has, and which are both available for an arbitrary `f`:
`AlgebraicGeometry.Space.invSectionEquiv` reads such a section as a map `f_small⁻¹h_V ⟶ F`, and
`AlgebraicGeometry.Space.sectionEquivChartFiberHom` reads it as a map `chartFiber f V ⟶ F`.
Both are natural in the sheaf `F`, so the resulting natural bijection of corepresentations is
precomposition with a single map `chartFiber f V ⟶ f_small⁻¹h_V`, the image of the identity;
and a map precomposition with which is bijective into every sheaf is exactly a member of
`CategoryTheory.GrothendieckTopology.W`.

## Main definitions

* `AlgebraicGeometry.Space.invRepChartFiberHomEquiv`: the bijection between the maps
  `f_small⁻¹h_V ⟶ F` and the maps `chartFiber f V ⟶ F`.
* `AlgebraicGeometry.Space.chartFiberToInvRep`: the canonical map
  `chartFiber f V ⟶ f_small⁻¹h_V`.

## Main results

* `AlgebraicGeometry.Space.W_chartFiberToInvRep`: the canonical map is a local isomorphism.
  This is the identification `f_small⁻¹h_V = h_{X ×_Y V}` for a not necessarily representable
  `f`.
* `AlgebraicGeometry.Space.chartRingHom_chartFiberToInvRep` and
  `AlgebraicGeometry.Space.chartSchemeHom_chartFiberToInvRep`: the ring map and, for an affine
  `V`, the morphism of schemes which
  `StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartRingMap.lean` attaches to a
  section of `f_small⁻¹h_V` coming from a chart map are the pullback of regular functions along
  that chart map, and the chart map itself.  So the chart morphisms of `(f_small, f♯)` are the
  chart maps over `f` that it tautologically carries.

## Implementation notes

`AlgebraicGeometry.Space.fmapInverseImageEquiv` (Stacks 03G4, (2) ⟺ (3)) is the corepresentation
of `f_small⁻¹Q` by the `f`-maps out of `Q`, for an arbitrary sheaf `Q` on the small étale site of
`Y`.  It is not what is used here: at `Q = h_V` it describes the maps out of `f_small⁻¹h_V` by
`AlgebraicGeometry.Space.FMap`s rather than by maps out of `chartFiber f V`, and it is the
`chartFiber` form that the chart morphisms of
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartComparison.lean` are stated
against.

The identification is not the one of
`AlgebraicGeometry.Space.smallEtalePullbackRepresentableNatIso` (Stacks 04K2, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleInverseImage.lean`): that one is stated for
`AlgebraicGeometry.Space.smallToposMorphism`, the morphism of small étale topoi at the universe
`u + 1` of the sites, and with the spaces-étale sheafified Yoneda presheaf restricted along the
comparison functor of Stacks 03G1 in place of the chart sheaf.  The morphism of ringed topoi of
Stacks 03G8 carries its topos at the universe `u` of the structure rings, which is where the chart
sheaf `(SmallEtale.topology B S hS Y.1).yoneda.obj V` and the ring map
`AlgebraicGeometry.Space.chartRingHom` live, and the `u + 1` statement does not specialize to it.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

variable (f : X ⟶ Y)

/-- **The two corepresentations of the sections of the direct image agree.** For an étale scheme
chart `V` of `Y` and a sheaf of sets `F` on the small étale site of `X`, the maps
`f_small⁻¹h_V ⟶ F` are the maps `chartFiber f V ⟶ F`: both are the sections of `f_*F` over `V`,
by `AlgebraicGeometry.Space.invSectionEquiv` and by
`AlgebraicGeometry.Space.sectionEquivChartFiberHom`. -/
def invRepChartFiberHomEquiv (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶ F.obj) ≃
      ((chartFiber B S hS f V).toFunctor ⟶ F.obj) :=
  (invSectionEquiv (smallEtaleRingedToposHom B S hS f) V F).symm.trans
    (sectionEquivChartFiberHom B S hS f V F)

/-- The bijection of corepresentations is natural in the sheaf. -/
theorem invRepChartFiberHomEquiv_comp (V : SmallEtale B S hS Y.1)
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (ψ : (invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶ F.obj) (q : F ⟶ G) :
    invRepChartFiberHomEquiv f V G (ψ ≫ q.hom) =
      invRepChartFiberHomEquiv f V F ψ ≫ q.hom := by
  have h : invSectionEquiv (smallEtaleRingedToposHom B S hS f) V G
      (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map q).hom.app (op V)
        ((invSectionEquiv (smallEtaleRingedToposHom B S hS f) V F).symm ψ)) = ψ ≫ q.hom := by
    rw [invSectionEquiv_naturality, Equiv.apply_symm_apply]
  rw [invRepChartFiberHomEquiv, invRepChartFiberHomEquiv, Equiv.trans_apply, Equiv.trans_apply,
    ← h, Equiv.symm_apply_apply, sectionEquivChartFiberHom_naturality]

/-- **The canonical map `chartFiber f V ⟶ f_small⁻¹h_V`**: the section of `f_small⁻¹h_V` over an
étale chart `U` of `X` attached to a chart map `U ⟶ V` over `f`.  It is the universal element of
the corepresentation `AlgebraicGeometry.Space.invRepChartFiberHomEquiv`, i.e. the image of the
identity of `f_small⁻¹h_V`. -/
def chartFiberToInvRep (V : SmallEtale B S hS Y.1) :
    (chartFiber B S hS f V).toFunctor ⟶
      (invRep (smallEtaleRingedToposHom B S hS f) V).obj :=
  invRepChartFiberHomEquiv f V (invRep (smallEtaleRingedToposHom B S hS f) V) (𝟙 _)

/-- **The bijection of corepresentations is precomposition with the canonical map.** -/
theorem invRepChartFiberHomEquiv_eq (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (ψ : (invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶ F.obj) :
    invRepChartFiberHomEquiv f V F ψ = chartFiberToInvRep f V ≫ ψ := by
  have h := invRepChartFiberHomEquiv_comp f V
    (F := invRep (smallEtaleRingedToposHom B S hS f) V) (G := F) (𝟙 _)
    (ObjectProperty.homMk ψ)
  rw [Category.id_comp] at h
  exact h

/-- **The inverse image of a chart sheaf is the sheafification of the presheaf of chart maps.**
For a morphism `f : X ⟶ Y` of algebraic spaces — *not* assumed representable — and an étale
scheme chart `V` of `Y`, the canonical map from the presheaf of chart maps over `f` into `V` to
`f_small⁻¹h_V` is a local isomorphism.  Equivalently `f_small⁻¹h_V` is the sheaf represented by
the algebraic space `X ×_Y V` étale over `X`, whose sections over a chart `U` of `X` are the
morphisms `U ⟶ X ×_Y V` over `X`. -/
theorem W_chartFiberToInvRep (V : SmallEtale B S hS Y.1) :
    (SmallEtale.topology B S hS X.1).W (chartFiberToInvRep f V) := by
  intro G hG
  have h : (fun ψ : (invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶ G =>
        chartFiberToInvRep f V ≫ ψ) =
      invRepChartFiberHomEquiv f V ⟨G, hG⟩ := by
    funext ψ
    exact (invRepChartFiberHomEquiv_eq f V ⟨G, hG⟩ ψ).symm
  rw [h]
  exact (invRepChartFiberHomEquiv f V ⟨G, hG⟩).bijective

/-- **Every section of `f_small⁻¹h_V` is étale-locally the section of a chart map over `f`.** The
arrows `i : U' ⟶ U` along which the restriction of a section `s` of `f_small⁻¹h_V` over `U` is
`AlgebraicGeometry.Space.chartFiberToInvRep` of a chart map over `f` form a covering sieve of
`U`.

This is the local factorization which the local isomorphism
`AlgebraicGeometry.Space.W_chartFiberToInvRep` provides, read off the subsheaf of
`f_small⁻¹h_V` generated by the image: the retraction which the local isomorphism supplies
exhibits every section as a section of that subsheaf. -/
theorem sieveOfSection_range_chartFiberToInvRep_mem (V : SmallEtale B S hS Y.1)
    (U : SmallEtale B S hS X.1)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U)) :
    (Subfunctor.range (chartFiberToInvRep f V)).sieveOfSection s ∈
      SmallEtale.topology B S hS X.1 U := by
  set m := chartFiberToInvRep f V with hm
  obtain ⟨r, hr⟩ := ((W_chartFiberToInvRep f V).homEquiv
    (Stacks.Sites.sheafOfMono (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).obj
    (Stacks.Sites.sheafOfMono (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).property
      ).surjective
      (Stacks.Sites.sheafOfMonoUnit (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m)
  have hr' : m ≫ r =
      Stacks.Sites.sheafOfMonoUnit (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m := hr
  have hri : r ≫ (Stacks.Sites.sheafOfMonoι
      (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).hom =
      𝟙 (invRep (smallEtaleRingedToposHom B S hS f) V).obj := by
    refine ((W_chartFiberToInvRep f V).homEquiv
      (invRep (smallEtaleRingedToposHom B S hS f) V).obj
      (invRep (smallEtaleRingedToposHom B S hS f) V).property).injective ?_
    change m ≫ r ≫ (Stacks.Sites.sheafOfMonoι
        (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).hom =
      m ≫ 𝟙 (invRep (smallEtaleRingedToposHom B S hS f) V).obj
    rw [← Category.assoc, hr', Stacks.Sites.sheafOfMonoUnit_ι, Category.comp_id]
  have hs : ((Stacks.Sites.sheafOfMonoι
      (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).hom.app (op U))
      (r.app (op U) s) = s := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hri]
    simp
  have h2 : (Subfunctor.range m).sieveOfSection
      ((Stacks.Sites.sheafOfMonoι (Q := invRep (smallEtaleRingedToposHom B S hS f) V) m).hom.app
        (op U) (r.app (op U) s)) ∈
      SmallEtale.topology B S hS X.1 U := (r.app (op U) s).property
  rwa [hs] at h2

/-- **The coordinate maps of `(f_small, f♯)` on the chart maps.** Composing the canonical map
with the coordinate map of a regular function `b` on `V` gives the pullback of `b` along the
chart maps. -/
theorem chartFiberToInvRep_comp_invCoord (V : SmallEtale B S hS Y.1)
    (b : (setO Y).obj.obj (op V)) :
    chartFiberToInvRep f V ≫ (invCoord (smallEtaleRingedToposHom B S hS f) V b).hom =
      chartFiberCoordinate B S hS f V b := by
  have h : invSectionEquiv (smallEtaleRingedToposHom B S hS f) V (setO X)
      ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b) =
      (invCoord (smallEtaleRingedToposHom B S hS f) V b).hom := by
    rw [invSectionEquiv_apply]
    exact congrArg (fun φ ↦ φ.hom)
      (homEquiv_symm_forgetFSharp (smallEtaleRingedToposHom B S hS f) V b)
  rw [← invRepChartFiberHomEquiv_eq, invRepChartFiberHomEquiv, Equiv.trans_apply, ← h,
    Equiv.symm_apply_apply]
  exact sectionEquivChartFiberHom_fSharp B S hS f V b

/-- The coordinate map of `(f_small, f♯)` evaluated on the section attached to a chart map is the
pullback of the regular function along that chart map. -/
theorem invCoord_app_chartFiberToInvRep (V : SmallEtale B S hS Y.1)
    (U : SmallEtale B S hS X.1) (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (b : (setO Y).obj.obj (op V)) :
    (invCoord (smallEtaleRingedToposHom B S hS f) V b).hom.app (op U)
        ((chartFiberToInvRep f V).app (op U) c) =
      (chartFiberCoordinate B S hS f V b).app (op U) c := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, chartFiberToInvRep_comp_invCoord]
  rfl

/-- **The ring map of `(f_small, f♯)` on the section attached to a chart map** is the pullback of
regular functions along that chart map. -/
theorem chartRingHom_chartFiberToInvRep (V : SmallEtale B S hS Y.1)
    (U : SmallEtale B S hS X.1) (c : (chartFiber B S hS f V).toFunctor.obj (op U)) :
    chartRingHom (smallEtaleRingedToposHom B S hS f) V U
        ((chartFiberToInvRep f V).app (op U) c) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c.val).op := by
  ext b
  exact (chartRingHom_apply (smallEtaleRingedToposHom B S hS f) V U _ b).trans
    (invCoord_app_chartFiberToInvRep f V U c b)

/-- **The chart morphism of `(f_small, f♯)` is the chart map it comes from.** For an affine étale
chart `V` of `Y`, the morphism of schemes which
`AlgebraicGeometry.Space.chartSchemeHom` attaches to the section of `f_small⁻¹h_V` of a chart map
over `f` is that chart map.

This is the tautological identification which the direct-image route of Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`) supplies only for a
representable `f`. -/
theorem chartSchemeHom_chartFiberToInvRep (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (c : (chartFiber B S hS f V).toFunctor.obj (op U)) :
    chartSchemeHom (smallEtaleRingedToposHom B S hS f) V U
        ((chartFiberToInvRep f V).app (op U) c) =
      (BigFppfOver.toScheme B S hS).map c.val := by
  apply ext_of_isAffine
  rw [chartSchemeHom_appTop, chartRingHom_chartFiberToInvRep, Scheme.Γ_map_op]

end AlgebraicGeometry.Space

end
