module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# The comparison map of equation 076R is an isomorphism on quasi-coherent modules

Let `φ : a ⋙ g ≅ f` be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}`, with `𝒰 --a--> 𝒱`, `f : 𝒰 ⥤ 𝒳`, `g : 𝒱 ⥤ 𝒳`, whose source categories
`𝒰` and `𝒱` are representable by algebraic spaces `U` and `V`, and let `aSpace : U ⟶ V` be the
morphism of algebraic spaces corresponding to `a`.  For an `𝒪_𝒳`-module `ℱ` on the inherited
étale site of `𝒳`, equation 076R of the source is the comparison map

```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```

(`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`).  This file proves that **`c_φ` is
an isomorphism when `ℱ` is a quasi-coherent module on the fppf site of `𝒳`** (Stacks 06WG),
read on the inherited étale site.  This is the fact the proof of Stacks 06WT uses when it applies
Stacks 0GQD "several times compatibly with pullbacks", and the module analogue for algebraic
spaces of condition (2) of Stacks 06WK.

## Main results

* `AlgebraicGeometry.Space.isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules`:
  **`c_φ` is an isomorphism**, for an arbitrary category `𝒳 : Type v''` with `Category.{w''}`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_fppf`: for
  `ℱ` quasi-coherent, `f^*ℱ|_{U_étale}` is a quasi-coherent `𝒪_U`-module, for every 1-morphism
  `f` out of a category representable by an algebraic space.
* `AlgebraicGeometry.Space.bijective_comparisonAlgebraicSpacesModules_app_of_fppf`: `c_φ` is
  bijective on the sections over the chart of a diagram of affine étale charts over `aSpace`.
* `AlgebraicGeometry.Space.bijective_liftBaseChange_etaleRestriction_of_isHomLift`: the sections of
  `f₁^*ℱ|_{U₁}` over an affine chart are the base change of the sections of `f₂^*ℱ|_{U₂}` over a
  second affine chart, along any morphism of `𝒳` lying over a morphism of the two charts.
* `AlgebraicGeometry.Space.isIso_of_bijective_app_of_hasAffineChartDiagram`: a morphism of
  `𝒪_X`-modules bijective on the sections over the charts carrying an affine chart diagram over
  some morphism `X ⟶ X'` is an isomorphism.

## Proof

Both sides are computed on the sections over the chart `W` of a commutative diagram of étale
scheme charts `W ⟶ V'` over `aSpace` with `W` and `V'` affine; such charts are cover-dense in
`U_étale` (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), so bijectivity there
is enough.

* The source: `g^*ℱ|_{V_étale}` is quasi-coherent, being cartesian on affine charts because `ℱ`
  is quasi-coherent on the big site (the forward direction of Descent, Proposition 03DX, on the
  slices of `𝒳`, `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation`),
  and the converse direction of Descent, Proposition 03DX(2) on `V_étale`.  So by the chart
  bijectivity of Stacks 083K its pullback along `aSpace` has sections
  `𝒪_U(W) ⊗_{𝒪_V(V')} ℱ(g(u_V V'))` over `W`.
* The target: its sections over `W` are `ℱ(f(u_U W))`, which is the same base change because the
  comparison morphism `f(u_U W) ⟶ g(u_V V')` lies over `W ⟶ V'`
  (`AlgebraicGeometry.Space.isHomLift_comparisonMorphism`), again by quasi-coherence of `ℱ` on
  the big site.
* Under these two identifications `c_φ` is the identity, because on chart sections it is
  restriction along the comparison morphism
  (`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_app_chartSection`).

The rings of regular functions on the charts are identified with the rings of global functions
of the corresponding objects of `𝒳` only through the identification of equation 075K
(`AlgebraicGeometry.Space.etaleChartFppfStructureRingEquiv`), which is why the base change
statement on the big site is first restated over isomorphic rings
(`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction_of_ringEquiv`).

## Implementation notes

No `@[stacks]` attribute is carried: the source does not state this as a numbered result.  It is
the module analogue of Stacks 075D (2) for an arbitrary morphism of algebraic spaces, which the
source uses without statement in the proofs of Stacks 06WT and 076S.

The module universe is the universe `u` of the schemes, which is the universe at which
`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules` is built (the module chart
correspondence of Stacks 03LU lives there) and at which Stacks 083K and Descent,
Proposition 03DX(2) are available.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w v' w' v'' w'' v₁ w₁ v₂ w₂

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

/-- **The sections over `y` are the base change of the sections over `x`, over any rings
identified with the rings of global functions.**  For a quasi-coherent module `M` on the fppf
site of `𝒳` and a morphism `n : y ⟶ x` between objects lying over affine schemes, the comparison
`Bc ⊗_A M(x) ⟶ M(y)` of any `A`-linear map agreeing with the restriction is bijective, for any
commutative rings `A`, `Bc` identified with the rings of global functions of `x` and `y`
compatibly with the scalar actions and with pullback along `n`.

This is `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction` with the two
rings of global functions replaced by isomorphic rings, which is the form in which it applies to
the restriction of `M` to the small étale site of an algebraic space: there the scalars are the
regular functions on an étale chart, identified with the global functions of the corresponding
object of `𝒳` only up to the canonical isomorphism. -/
theorem bijective_liftBaseChange_of_eq_restriction_of_ringEquiv
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {x y : 𝒳} (n : y ⟶ x)
    (hx : IsAffineOver B S hS (p.obj x)) (hy : IsAffineOver B S hS (p.obj y))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [iAx : Module A (M.val.obj (op x))] [iAy : Module A (M.val.obj (op y))]
    [iBy : Module Bc (M.val.obj (op y))] [iT : IsScalarTower A Bc (M.val.obj (op y))]
    (fA : ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op x) : Type u) ≃+* A)
    (hfA : ∀ (c : ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op x) : Type u))
      (m : M.val.obj (op x)), fA c • m = c • m)
    (fB : ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op y) : Type u) ≃+* Bc)
    (hfB : ∀ (c : ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op y) : Type u))
      (m : M.val.obj (op y)), fB c • m = c • m)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB (((ringStructureSheafCore B S hS p hp .fppf).obj.map n.op).hom (fA.symm c)))
    (r : M.val.obj (op x) →ₗ[A] M.val.obj (op y)) (hr : ∀ s, r s = M.val.map n.op s) :
    Function.Bijective (r.liftBaseChange Bc) :=
  @bijective_liftBaseChange_of_hasGlobalPresentation B S hS 𝒳 _ p hp x (M.over x)
    (hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS p hp M hM ⟨x, hx⟩)
    (Over.mk (𝟙 x)) (Over.mk n) (Over.homMk n : (Over.mk n : Over x) ⟶ Over.mk (𝟙 x)) hx hy
    A Bc _ _ _ iAx iAy iBy iT fA hfA fB hfB halg r
    (fun s => (hr s).trans rfl)

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of the structure sheaf of `(Sch/S)_{fppf}` along an identification of two objects,
followed by restriction along the inverse identification, is the identity. -/
private theorem structureSheaf_map_eqToHom_symm_apply {T T' : BigFppfOver B S hS} (h : T = T')
    (x : ((BigFppfOver.structureSheaf B S hS).obj.obj (op T') : Type u)) :
    ((BigFppfOver.structureSheaf B S hS).obj.map (eqToHom h.symm).op).hom
      (((BigFppfOver.structureSheaf B S hS).obj.map (eqToHom h).op).hom x) = x := by
  subst h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
  rfl

/-- Two successive restrictions along opposite morphisms of a presheaf of rings are the
restriction along their composite. -/
private theorem ringPresheaf_map_comp_apply {C : Type*} [Category C] (K : Cᵒᵖ ⥤ RingCat.{u})
    {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (a : K.obj (op Z)) :
    K.map x.op (K.map y.op a) = K.map (x ≫ y).op a := by
  rw [op_comp, K.map_comp]
  rfl

/-- **A morphism of `𝒪_X`-modules bijective on the sections over the charts carrying an affine
chart diagram over some `g : X ⟶ X'` is an isomorphism.**  Those charts are cover-dense in the
small étale site of `X` (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), so such
a morphism is locally injective and locally surjective. -/
theorem isIso_of_bijective_app_of_hasAffineChartDiagram {X X' : AlgebraicSpaces B S hS}
    (g : X ⟶ X') {M N : Modules.{u, u} B S hS X.1 X.2} (c : M ⟶ N)
    (h : ∀ W : SmallEtale B S hS X.1, HasAffineChartDiagram B S hS g W →
      Function.Bijective (c.val.app (op W)).hom) :
    IsIso c := by
  have hinj : PresheafOfModules.IsLocallyInjective (SmallEtale.topology B S hS X.1) c.val :=
    ⟨fun {U} x y hxy => mem_topology_of_hasAffineChartDiagram B S hS g U.unop _
      fun W i hW => (h W hW).1 <| by
        refine (PresheafOfModules.naturality_apply c.val i.op x).trans ?_
        refine Eq.trans ?_ (PresheafOfModules.naturality_apply c.val i.op y).symm
        exact congrArg (fun z => N.val.map i.op z) hxy⟩
  have hsurj : PresheafOfModules.IsLocallySurjective (SmallEtale.topology B S hS X.1) c.val :=
    ⟨fun {U} s => mem_topology_of_hasAffineChartDiagram B S hS g U _
      fun W i hW => (h W hW).2 (N.val.map i.op s)⟩
  exact @Stacks.SheafOfModules.isIso_of_isLocallyBijective _ _ _ _ _ _ c hinj hsurj

section Chart

variable {U : AlgebraicSpaces B S hS} {𝒰 : Type v} [Category.{w} 𝒰]
  {𝒳 : Type v''} [Category.{w''} 𝒳] (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)

/-- **The identification of structure sheaves of equation 075K is an isomorphism on each chart.**
The homomorphism `AlgebraicGeometry.Space.etaleChartStructureHom` is, on sections over an étale
chart `W` of `U`, restriction of global functions along an identification of two objects of
`(Sch/S)_{fppf}`; restriction along the inverse identification inverts it. -/
noncomputable def etaleChartFppfStructureRingEquiv (W : SmallEtale B S hS U.1) :
    chartRing B S hS U.1 U.2 W ≃+*
      ((FibredSite.ringStructureSheafCore B S hS r hr .fppf).obj.obj
        (op ((etaleChartToFibred B S hS p eU f).obj W)) : Type u) :=
  RingEquiv.ofRingHom ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W)).hom
    ((BigFppfOver.structureSheaf B S hS).obj.map
      (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W).symm).op).hom
    (RingHom.ext fun x => by
      change ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W)).hom _ = x
      rw [etaleChartStructureHom_app]
      exact structureSheaf_map_eqToHom_symm_apply B S hS
        (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W).symm x)
    (RingHom.ext fun x => by
      change _ = x
      rw [etaleChartStructureHom_app]
      exact structureSheaf_map_eqToHom_symm_apply B S hS _ x)

/-- The ring isomorphism `etaleChartFppfStructureRingEquiv` is given by the sections over `W` of
`AlgebraicGeometry.Space.etaleChartStructureHom`. -/
theorem etaleChartFppfStructureRingEquiv_apply (W : SmallEtale B S hS U.1)
    (c : chartRing B S hS U.1 U.2 W) :
    etaleChartFppfStructureRingEquiv B S hS p r hp hr eU f hf W c =
      (etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W) c :=
  rfl

end Chart

section Core

variable {U₁ U₂ : AlgebraicSpaces B S hS}
  {𝒰₁ : Type v₁} [Category.{w₁} 𝒰₁] {𝒰₂ : Type v₂} [Category.{w₂} 𝒰₂]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p₁ : 𝒰₁ ⥤ BigFppfOver B S hS) (p₂ : 𝒰₂ ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp₁ : p₁.IsFiberedInGroupoids) (hp₂ : p₂.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (e₁ : StacksRepresentableCFG.EquivalenceOver p₁ (presheafOfCategories (U₁.1 ⋙ typeToCat)).p)
  (e₂ : StacksRepresentableCFG.EquivalenceOver p₂ (presheafOfCategories (U₂.1 ⋙ typeToCat)).p)
  (f₁ : 𝒰₁ ⥤ 𝒳) (f₂ : 𝒰₂ ⥤ 𝒳) (hf₁ : p₁.IsFibredOneMorphism r f₁)
  (hf₂ : p₂.IsFibredOneMorphism r f₂)

/-- **Restriction along a morphism of `𝒳` lying over a morphism of charts is pullback of regular
functions, read through the identifications of equation 075K.**  If `n : f₁(u W₁) ⟶ f₂(u W₂)`
lies over the morphism `t : W₁ ⟶ W₂` of `(Sch/S)_{fppf}`, then pulling back a regular function on
`W₂` along `t` and identifying it with a global function of `f₁(u W₁)` is the same as identifying
it with a global function of `f₂(u W₂)` and restricting along `n`.

This is `AlgebraicGeometry.Space.structureSheaf_map_comparisonMorphism` for an arbitrary morphism
lying over an arbitrary morphism of the underlying objects. -/
theorem structureSheaf_map_of_isHomLift {W₁ : SmallEtale B S hS U₁.1}
    {W₂ : SmallEtale B S hS U₂.1}
    (t : (SmallEtale.toOver B S hS U₁.1).obj W₁ ⟶ (SmallEtale.toOver B S hS U₂.1).obj W₂)
    (n : (etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁ ⟶
      (etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂) [r.IsHomLift t n]
    (c : chartRing B S hS U₂.1 U₂.2 W₂) :
    ((FibredSite.ringStructureSheafCore B S hS r hr .fppf).obj.map n.op).hom
        ((etaleChartStructureHom B S hS p₂ r hp₂ hr e₂ f₂ hf₂).hom.app (op W₂) c) =
      (etaleChartStructureHom B S hS p₁ r hp₁ hr e₁ f₁ hf₁).hom.app (op W₁)
        (((BigFppfOver.structureSheaf B S hS).obj.map t.op).hom c) := by
  have key := (IsHomLift.commSq r t n).w
  rw [etaleChartStructureHom_app, etaleChartStructureHom_app]
  refine Eq.trans (ringPresheaf_map_comp_apply (BigFppfOver.structureSheaf B S hS).obj
    (r.map n) (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p₂ r e₂ f₂ hf₂) W₂)) c) ?_
  refine Eq.trans ?_ (ringPresheaf_map_comp_apply (BigFppfOver.structureSheaf B S hS).obj
    (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p₁ r e₁ f₁ hf₁) W₁)) t c).symm
  exact congrArg (fun m : (etaleChartToFibred B S hS p₁ e₁ f₁ ⋙ r).obj W₁ ⟶
      (SmallEtale.toOver B S hS U₂.1).obj W₂ =>
    (BigFppfOver.structureSheaf B S hS).obj.map m.op c) key

/-- **The sections of the restriction of a quasi-coherent module over a chart are the base change
of its sections over a second chart**, along any morphism of `𝒳` between the corresponding
objects lying over a morphism of the two affine charts.

Let `ℱ` be a quasi-coherent module on the fppf site of `𝒳` and read it on the inherited étale
site.  For étale charts `W₁` of `U₁` and `W₂` of `U₂` with affine underlying schemes, a morphism
`t : W₁ ⟶ W₂` of `(Sch/S)_{fppf}` and a morphism `n : f₁(u W₁) ⟶ f₂(u W₂)` of `𝒳` lying over
`t`, the comparison `𝒪_{U₁}(W₁) ⊗_{𝒪_{U₂}(W₂)} (f₂^*ℱ|_{U₂})(W₂) ⟶ (f₁^*ℱ|_{U₁})(W₁)` of any
linear map agreeing with restriction along `n` is bijective.  The algebra structure is any one
whose structure map is pullback along `t`.

This is `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction_of_ringEquiv`,
the forward direction of Descent, Proposition 03DX, on the slice of `𝒳` at `f₂(u W₂)`, read
through the identifications `AlgebraicGeometry.Space.etaleChartFppfStructureRingEquiv` of the two
rings of regular functions with the rings of global functions of the two objects of `𝒳`; the
compatibility of those identifications with `n` is
`AlgebraicGeometry.Space.structureSheaf_map_of_isHomLift`. -/
theorem bijective_liftBaseChange_etaleRestriction_of_isHomLift
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS r hr .fppf))
    (hℱ : ℱ.IsQuasicoherentOnSite) {W₁ : SmallEtale B S hS U₁.1} {W₂ : SmallEtale B S hS U₂.1}
    (hW₁ : IsAffine ((SmallEtale.toOver B S hS U₁.1 ⋙ BigFppfOver.toScheme B S hS).obj W₁))
    (hW₂ : IsAffine ((SmallEtale.toOver B S hS U₂.1 ⋙ BigFppfOver.toScheme B S hS).obj W₂))
    (t : (SmallEtale.toOver B S hS U₁.1).obj W₁ ⟶ (SmallEtale.toOver B S hS U₂.1).obj W₂)
    (n : (etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁ ⟶
      (etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂) [r.IsHomLift t n]
    [Algebra (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)]
    (halg : ∀ c, algebraMap (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁) c =
      ((BigFppfOver.structureSheaf B S hS).obj.map t.op).hom c)
    [iA : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₁))]
    [iT : IsScalarTower (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₁))]
    (ρ : (etaleRestrictedModuleInverseImage B S hS p₂ r hp₂ hr e₂ f₂ hf₂
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₂)
      →ₗ[chartRing B S hS U₂.1 U₂.2 W₂]
        (etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁
          ((Stacks.Sites.CoarserTopology.modulePushforward
            (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₁))
    (hρ : ∀ s, ρ s = ℱ.val.map n.op s) :
    Function.Bijective (ρ.liftBaseChange (chartRing B S hS U₁.1 U₁.2 W₁)) := by
  have hx : IsAffineOver B S hS (r.obj ((etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂)) := by
    rw [IsHomLift.codomain_eq r t n]
    exact hW₂
  have hy : IsAffineOver B S hS (r.obj ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁)) := by
    rw [IsHomLift.domain_eq r t n]
    exact hW₁
  let e₁' := etaleChartFppfStructureRingEquiv B S hS p₁ r hp₁ hr e₁ f₁ hf₁ W₁
  let e₂' := etaleChartFppfStructureRingEquiv B S hS p₂ r hp₂ hr e₂ f₂ hf₂ W₂
  let iAx : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂))) :=
    inferInstanceAs (Module (chartRing B S hS U₂.1 U₂.2 W₂)
      ((etaleRestrictedModuleInverseImage B S hS p₂ r hp₂ hr e₂ f₂ hf₂
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₂)))
  let iBy : Module (chartRing B S hS U₁.1 U₁.2 W₁)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) :=
    inferInstanceAs (Module (chartRing B S hS U₁.1 U₁.2 W₁)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.obj (op W₁)))
  let iAy : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) := iA
  have iT' : IsScalarTower (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) := iT
  exact FibredSite.bijective_liftBaseChange_of_eq_restriction_of_ringEquiv ℱ hℱ
    n hx hy (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁) e₂'.symm
    (fun c m => congrArg (fun z => z • m) (e₂'.apply_symm_apply c))
    e₁'.symm
    (fun c m => congrArg (fun z => z • m) (e₁'.apply_symm_apply c))
    (fun c => by
      rw [halg c, RingEquiv.symm_symm]
      refine (RingEquiv.eq_symm_apply e₁').2 ?_
      exact (structureSheaf_map_of_isHomLift B S hS p₁ p₂ r hp₁ hp₂ hr e₁ e₂ f₁ f₂ hf₁ hf₂ t n
        c).symm)
    ρ hρ

end Core

section Restriction

variable {U : AlgebraicSpaces B S hS} {𝒰 : Type v} [Category.{w} 𝒰]
  {𝒳 : Type v''} [Category.{w''} 𝒳] (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)

/-- **The restriction to `U_étale` of the inverse image of a quasi-coherent module is cartesian on
affine charts.**  For a quasi-coherent module `ℱ` on the fppf site of `𝒳`, read on the inherited
étale site, and a 1-morphism `f : 𝒰 ⥤ 𝒳` out of a category representable by the algebraic space
`U`, the sections of `f^*ℱ|_{U_étale}` over a smaller affine étale chart are the base change of
its sections over a larger one.

Both sections are sections of `ℱ` over the images under `f` of the two charts, and the morphism
between those images lies over the morphism of charts; so this is
`AlgebraicGeometry.Space.bijective_liftBaseChange_etaleRestriction_of_isHomLift`. -/
theorem isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_fppf
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS r hr .fppf))
    (hℱ : ℱ.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)) := by
  intro W₂ W₁ hW₂ hW₁ j
  have : r.IsHomLift ((SmallEtale.toOver B S hS U.1).map j)
      ((etaleChartToFibred B S hS p eU f).map j) :=
    Functor.isHomLift_map_of_comp_eq (etaleChartToFibred_comp B S hS p r eU f hf) _ j
  let := chartAlgebra (hF := U.2) j
  let := chartSectionsModule (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)) j
  have := chartSections_isScalarTower (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)) j
  have halg : ∀ c, algebraMap (chartRing B S hS U.1 U.2 W₂) (chartRing B S hS U.1 U.2 W₁) c =
      ((BigFppfOver.structureSheaf B S hS).obj.map
        ((SmallEtale.toOver B S hS U.1).map j).op).hom c := fun c => rfl
  have hρ : ∀ s, chartRestrictLinear (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)) j s =
      ℱ.val.map ((etaleChartToFibred B S hS p eU f).map j).op s := fun s => rfl
  exact bijective_liftBaseChange_etaleRestriction_of_isHomLift B S hS p p r hp hp hr eU eU f f
    hf hf ℱ hℱ hW₁ hW₂ _ _ halg _ hρ

/-- **The restriction to `U_étale` of the inverse image of a quasi-coherent module is
quasi-coherent.**  For a quasi-coherent module `ℱ` on the fppf site of `𝒳`, read on the
inherited étale site, and a 1-morphism `f : 𝒰 ⥤ 𝒳` out of a category representable by the
algebraic space `U`, the `𝒪_U`-module `f^*ℱ|_{U_étale}` is quasi-coherent.

It is cartesian on affine charts
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_fppf`),
and a module cartesian on affine charts is quasi-coherent by Descent, Proposition 03DX(2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`). -/
theorem isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_fppf
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS r hr .fppf))
    (hℱ : ℱ.IsQuasicoherentOnSite) :
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_fppf B S hS p r hp hr eU f hf
      ℱ hℱ)

end Restriction

section Triangle

variable {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hf : p.IsFibredOneMorphism r f) (hg : q.IsFibredOneMorphism r g)
  (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hr : r.IsFiberedInGroupoids)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))

/-- **The comparison map of equation 076R on a chart section.**  On the section of
`a_small^*(g^*ℱ|_{V_étale})` over the chart `W` of a commutative diagram of étale scheme charts
attached to a section `s` of `g^*ℱ|_{V_étale}` over the chart `V'`, the comparison map is
restriction of `s` along the comparison morphism `f(u_U W) ⟶ g(u_V V')`.

This is the adjunction defining `c_φ` read on sections: its transpose is
`AlgebraicGeometry.Space.moduleComparisonPushforwardHom`, the homomorphism the chart
correspondence attaches to `AlgebraicGeometry.Space.moduleComparisonFMap`, and the chart sections
are the chart components of the unit. -/
theorem comparisonAlgebraicSpacesModules_app_chartSection
    (ℱ : inheritedEtaleModules B S hS r hr) (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).val.obj (op d.V)) :
    (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ).val.app (op d.U)
        (modulePullbackChartSection B S hS aSpace
          (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) d s) =
      ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection, ← modulePullbackHomFMap_app]
  have h : modulePullbackHomFMap B S hS aSpace
      (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)
      (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
      (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ℱ) =
      moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ :=
    (congrArg (modulePushforwardHomEquiv B S hS aSpace
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
        (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ))
      (comparisonAlgebraicSpacesModules_adjoint B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
        hr hφ hab ℱ)).trans
      ((modulePushforwardHomEquiv B S hS aSpace
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
        (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)).apply_symm_apply _)
  rw [h]
  rfl

/-- **The comparison map of equation 076R is bijective on the sections over the chart of an
affine chart diagram**, for the étale reading of a quasi-coherent module on the fppf site of `𝒳`.

Let `d` be a commutative diagram of étale scheme charts over `aSpace`, a chart `W` of `U` above a
chart `V'` of `V`, both affine.  The sections of `a_small^*(g^*ℱ|_{V_étale})` over `W` are the
base change `𝒪_U(W) ⊗_{𝒪_V(V')} ℱ(g(u_V V'))`, because `g^*ℱ|_{V_étale}` is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_fppf`) and by
the chart bijectivity of Stacks 083K
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`).
The sections of `f^*ℱ|_{U_étale}` over `W` are `ℱ(f(u_U W))`, which is the same base change
because `ℱ` is quasi-coherent and the comparison morphism `f(u_U W) ⟶ g(u_V V')` lies over the
morphism `W ⟶ V'` of affine schemes
(`AlgebraicGeometry.Space.bijective_liftBaseChange_etaleRestriction_of_isHomLift`).  Under these
two identifications `c_φ` is the identity of the base change, by
`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_app_chartSection`. -/
theorem bijective_comparisonAlgebraicSpacesModules_app_of_fppf
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS r hr .fppf))
    (hℱ : ℱ.IsQuasicoherentOnSite) (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (hdU : IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hdV : IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective
      ((comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ)).val.app
          (op d.U)).hom := by
  let ℱe := (Stacks.Sites.CoarserTopology.modulePushforward
    (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ
  let G := etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱe
  let F := etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱe
  let c := comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
    hφ hab ℱe
  have hG : G.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_fppf B S hS q r hq hr eV g hg ℱ hℱ
  let := chartDiagramAlgebra B S hS aSpace d
  have h1 := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS aSpace G hG d
    hdU hdV
  have := isHomLift_comparisonMorphism B S hS p q r eU eV a f g hg φ aSpace ha hφ hab d
  let : Module (chartRing B S hS V.1 V.2 d.V) (F.val.obj (op d.U)) :=
    Module.compHom _ (chartDiagramRestrict B S hS aSpace d)
  have : IsScalarTower (chartRing B S hS V.1 V.2 d.V) (chartRing B S hS U.1 U.2 d.U)
      (F.val.obj (op d.U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : G.val.obj (op d.V) →ₗ[chartRing B S hS V.1 V.2 d.V] F.val.obj (op d.U) :=
    { toFun := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱe).app d
      map_add' := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱe).map_add d
      map_smul' := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ℱe).map_smul d }
  have halg : ∀ x, algebraMap (chartRing B S hS V.1 V.2 d.V) (chartRing B S hS U.1 U.2 d.U) x =
      ((BigFppfOver.structureSheaf B S hS).obj.map d.g.op).hom x := fun _ => rfl
  have hρ : ∀ x, ρ x =
      ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op x := fun _ => rfl
  have h2 := bijective_liftBaseChange_etaleRestriction_of_isHomLift B S hS p q r hp hq hr eU eV f g
    hf hg ℱ hℱ hdU hdV d.g (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d) halg ρ hρ
  have h3 : (c.val.app (op d.U)).hom ∘ modulePullbackChartBaseChange B S hS aSpace G d =
      ρ.liftBaseChange (chartRing B S hS U.1 U.2 d.U) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | tmul x s =>
      rw [Function.comp_apply, modulePullbackChartBaseChange_tmul, LinearMap.map_smul,
        LinearMap.liftBaseChange_tmul]
      exact congrArg (fun y => x • y)
        (comparisonAlgebraicSpacesModules_app_chartSection B S hS p q r hp hq eU eV a f g hf hg φ
          aSpace ha hr hφ hab ℱe d s)
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  exact (Function.Bijective.of_comp_iff _ h1).1 (h3 ▸ h2)

/-- **The comparison map of equation 076R is an isomorphism on quasi-coherent modules.**

Let `φ : a ⋙ g ≅ f` be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose source categories `𝒰`, `𝒱` are representable by algebraic spaces
`U`, `V`, with `aSpace : U ⟶ V` the morphism of algebraic spaces corresponding to `a`, and let
`ℱ` be a quasi-coherent `𝒪_𝒳`-module (Stacks 06WG), read on the inherited étale site of `𝒳`.
Then the comparison map
```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```
of equation 076R is an isomorphism of `𝒪_U`-modules.

This is the module analogue for algebraic spaces of the statement of Stacks 06WK that the
comparison maps of a quasi-coherent module are isomorphisms, and it is what the proof of
Stacks 06WT uses when it applies Stacks 0GQD "compatibly with pullbacks".  The proof checks
bijectivity on the sections over the charts carrying an affine chart diagram over `aSpace`
(`AlgebraicGeometry.Space.bijective_comparisonAlgebraicSpacesModules_app_of_fppf`), which are
cover-dense (`AlgebraicGeometry.Space.isIso_of_bijective_app_of_hasAffineChartDiagram`). -/
theorem isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules
    (ℱ : FibredSite.quasicoherentModules.{u, v'', w'', u} B S hS r hr) :
    IsIso (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
      hab ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS r .etale) _).obj ℱ.obj)) := by
  refine isIso_of_bijective_app_of_hasAffineChartDiagram B S hS aSpace _ fun W hW => ?_
  obtain ⟨hWaff, V', t, ht, hV'aff⟩ := hW
  exact bijective_comparisonAlgebraicSpacesModules_app_of_fppf B S hS p q r hp hq eU eV a f g hf hg
    φ aSpace ha hr hφ hab ℱ.obj ℱ.property ⟨W, V', t, ht.symm⟩ hWaff hV'aff

end Triangle

end AlgebraicGeometry.Space

end
