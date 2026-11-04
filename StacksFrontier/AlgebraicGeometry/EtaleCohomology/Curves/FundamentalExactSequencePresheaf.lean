module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorPresheafCoproduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.IntegralCompactEtaleCovering
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement

/-!
# The second map of the fundamental exact sequence of Stacks 03RI, as a morphism of sheaves

Let `X` be a smooth curve over a field, let `η` be its generic point with inclusion `j : η ↪ X`,
and let `X_0` be its set of closed points. The second map of the fundamental exact sequence of
Stacks 03RI,
`j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙`,
is built here as a morphism of abelian sheaves on the small étale site of `X`.

On sections over an irreducible quasi-compact étale `X`-scheme `U` the map is already available:
it is `Stacks.EtaleCohomology.genericFibreDivisorSections`, the family of orders of vanishing of
an invertible global function on the generic fibre of `U`. Three things turn that into a morphism
of sheaves.

* **Naturality.** The `x`-component of the family is a locally constant `𝐙`-valued function on
  the fibre `x ×_X U`, and its value at a point is the order of vanishing at the image point of
  `U`. That order is unchanged by restriction along a morphism `h : V ⟶ U` of the small étale
  site, by `Stacks.EtaleCohomology.etaleGenericFibreOrd_restrict`, and the identification of the
  sections of `(i_x)_* 𝐙` with the locally constant functions is natural, being the component of
  a natural isomorphism of presheaves. Together these give
  `Stacks.EtaleCohomology.genericFibreDivisorPresheafMap_naturality`.

* **Landing in the coproduct.** A coproduct of sheaves has no universal property for morphisms
  *into* it; the coproduct of the underlying presheaves does, and the finitely supported family
  of orders of vanishing is a section of that presheaf coproduct. The passage is
  `Stacks.EtaleCohomology.closedPointDivisorSheaf.fromPresheafCoproduct`.

* **Extension to the whole site.** The irreducible quasi-compact objects are cover-dense, by
  `Stacks.EtaleCohomology.isCoverDense_isIntegralCompactEtale_ι`, so
  `CategoryTheory.Functor.IsCoverDense.sheafHom` extends a morphism of presheaves defined on them
  into a sheaf, uniquely, to the whole small étale site. No irreducibility hypothesis survives in
  the morphism of sheaves: it is a morphism of sheaves on the small étale site of `X`, defined at
  every étale `X`-scheme.

## Main definitions

* `Stacks.EtaleCohomology.genericFibreUnitsRestrict`: restriction of a section of `j_* 𝐆_{m,η}`
  along a morphism of the small étale site.
* `Stacks.EtaleCohomology.genericFibreDivisorPresheafMap`: the divisor map on sections over an
  irreducible quasi-compact étale `X`-scheme, with values in the coproduct of the underlying
  presheaves of the skyscrapers.
* `Stacks.EtaleCohomology.genericFibreDivisorIntegral`: the same as a morphism of presheaves on
  the integral quasi-compact subsite.
* `Stacks.EtaleCohomology.closedPointDivisorMap`: **the second map of the fundamental exact
  sequence of Stacks 03RI**, as a morphism of abelian sheaves on the small étale site.

## Main results

* `Stacks.EtaleCohomology.toAddMonoid_mapRange` and `Stacks.EtaleCohomology.comp_toAddMonoid`:
  the map out of a direct sum determined by a family, pre- and postcomposed.
* `Stacks.EtaleCohomology.residueFibreOrd_genericFibreUnitsRestrict` and
  `Stacks.EtaleCohomology.integerSkyscraperDivisor_genericFibreUnitsRestrict`: the components of
  the divisor map are natural in the étale `X`-scheme.
* `Stacks.EtaleCohomology.genericFibreDivisorPresheafMap_naturality`: the divisor map on sections
  is natural.
* `Stacks.EtaleCohomology.closedPointDivisorMap_app`: the second map restricted to an integral
  quasi-compact object is the divisor map on sections.
* `Stacks.EtaleCohomology.comparison_comp_closedPointDivisorMap`: **the sequence is a complex** —
  the composite of the first two maps of the fundamental exact sequence is zero.

## Implementation notes

The direct sum over the closed points needs decidable equality on them, which is supplied
classically by making `Classical.decEq` a local instance; every direct-sum construction in the
file is then on the same instance, which is what lets `DirectSum.toAddMonoid_of` apply.

The two lemmas `Stacks.EtaleCohomology.toAddMonoid_mapRange` and
`Stacks.EtaleCohomology.comp_toAddMonoid` are stated for an abstract direct sum rather than
proved inline: the naturality square is exactly the statement that the two ways of composing a
map out of a direct sum with a termwise map and with a homomorphism agree, and separating them
keeps the naturality proof free of `DFinsupp`.

The naturality proof is a `calc` chain of terms rather than a sequence of rewrites. The type
`X.Etale` elaborates with the morphism property `Etale` unapplied, which makes the goals of this
file ill-typed at the `implicit` transparency level at which `rw` checks its motive; `rw`
therefore fails on them where `exact` and `calc` succeed.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5): the sections of a
  constant sheaf are the locally constant maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Components

variable {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Etale}
  [AlgebraicGeometry.IsIntegral U.left] [AlgebraicGeometry.IsIntegral V.left]
  [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]

/-- **Restriction of a section of `j_* 𝐆_{m,η}` along a morphism of the small étale site**, read
on invertible global functions of the generic fibre written additively. -/
def genericFibreUnitsRestrict (h : V ⟶ U) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      Additive ((Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :=
  MonoidHom.toAdditive (Units.map
    (((smallEtaleBaseChange (genericPointInclusion X)).map h).left).appTop.hom.toMonoidHom)

/-- **The `x`-component of the divisor map is natural in the étale `X`-scheme**, read as a
locally constant function on the fibre over `x`: the order of vanishing of the restricted section
at a point of the fibre of `V` is the order of vanishing of the section at the image point of the
fibre of `U`. -/
theorem residueFibreOrd_genericFibreUnitsRestrict (h : V ⟶ U) (x : X)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    residueFibreOrd.{u, v} V x (genericFibreUnitsRestrict h a) =
      LocallyConstant.comap
        (((smallEtaleBaseChange (X.fromSpecResidueField x)).map h).left).base.hom
        (residueFibreOrd.{u, v} U x a) := by
  refine LocallyConstant.ext fun y => ?_
  rw [residueFibreOrd_apply, LocallyConstant.coe_comap_apply, residueFibreOrd_apply]
  refine congrArg ULift.up ?_
  refine (etaleGenericFibreOrd_restrict h _ (Additive.toMul a)).trans ?_
  refine congrArg (fun z : U.left => etaleGenericFibreOrd U z (Additive.ofMul _)) ?_
  exact (congrArg
    (fun φ : pullback V.hom (X.fromSpecResidueField x) ⟶ U.left => φ.base y)
    (smallEtaleBaseChange_map_left_comp_fst (X.fromSpecResidueField x) h)).symm

omit [IrreducibleSpace X] [AlgebraicGeometry.IsIntegral U.left]
  [AlgebraicGeometry.IsIntegral V.left] [IsLocallyNoetherian U.left]
  [IsLocallyNoetherian V.left] in
/-- **Restriction in the skyscraper `(i_x)_* 𝐙` is pullback of locally constant functions along
the induced morphism of fibres.** This is the naturality of the identification of the sections of
`(i_x)_* 𝐙` with the locally constant `𝐙`-valued functions on the fibre, Stacks 03P5. -/
theorem integerSkyscraper_map_eq (h : V ⟶ U) (x : X)
    (γ : (integerSkyscraper.{u, v} X x).obj.obj (op U)) :
    (integerSkyscraper.{u, v} X x).obj.map h.op γ =
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x V).inv
        (LocallyConstant.comap
          (((smallEtaleBaseChange (X.fromSpecResidueField x)).map h).left).base.hom
          ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom γ)) := by
  have hγ : (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).inv
      ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom γ) = γ :=
    ConcreteCategory.congr_hom
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom_inv_id γ
  refine (congrArg ((integerSkyscraper.{u, v} X x).obj.map h.op) hγ).symm.trans ?_
  exact (ConcreteCategory.congr_hom
    (((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v}
      (Spec (X.residueField x)) (ULift.{max (u + 1) v} ℤ)).inv.naturality
        ((smallEtaleBaseChange (X.fromSpecResidueField x)).map h).op))
    ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom γ)).symm

/-- **The `x`-component of the divisor map is natural in the étale `X`-scheme**, read as a
section of the skyscraper `(i_x)_* 𝐙`. -/
theorem integerSkyscraperDivisor_genericFibreUnitsRestrict (h : V ⟶ U) (x : X)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    integerSkyscraperDivisor.{u, v} V x (genericFibreUnitsRestrict h a) =
      (integerSkyscraper.{u, v} X x).obj.map h.op
        (integerSkyscraperDivisor.{u, v} U x a) := by
  rw [integerSkyscraperDivisor, AddMonoidHom.comp_apply,
    residueFibreOrd_genericFibreUnitsRestrict.{u, v} h x a, integerSkyscraperDivisor,
    AddMonoidHom.comp_apply]
  refine Eq.trans ?_ (integerSkyscraper_map_eq h x _).symm
  simp

end Components

section DirectSumLemmas

variable {ι : Type*} [DecidableEq ι] {β₁ β₂ : ι → Type*} [∀ i, AddCommMonoid (β₁ i)]
  [∀ i, AddCommMonoid (β₂ i)] {γ δ : Type*} [AddCommMonoid γ] [AddCommMonoid δ]

/-- The map out of a direct sum determined by a family, precomposed with a termwise map, is the
map determined by the composed family. -/
theorem toAddMonoid_mapRange (f : ∀ i, β₁ i →+ β₂ i) (φ : ∀ i, β₂ i →+ γ) (d : DirectSum ι β₁) :
    DirectSum.toAddMonoid φ (DFinsupp.mapRange (fun i b => f i b) (fun i => map_zero (f i)) d) =
      DirectSum.toAddMonoid (fun i => (φ i).comp (f i)) d := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (fun i b => ?_) :
    (DirectSum.toAddMonoid φ).comp (DFinsupp.mapRange.addMonoidHom f) =
      DirectSum.toAddMonoid fun i => (φ i).comp (f i)) d
  rw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp,
    Function.comp_apply, show DFinsupp.mapRange.addMonoidHom f (DirectSum.of β₁ i b) =
      DirectSum.of β₂ i (f i b) from DFinsupp.mapRange_single
        (hf := fun j => map_zero (f j)), DirectSum.toAddMonoid_of]

/-- The map out of a direct sum determined by a family, postcomposed with a homomorphism, is the
map determined by the postcomposed family. -/
theorem comp_toAddMonoid (ψ : γ →+ δ) (φ : ∀ i, β₁ i →+ γ) (d : DirectSum ι β₁) :
    ψ (DirectSum.toAddMonoid φ d) = DirectSum.toAddMonoid (fun i => ψ.comp (φ i)) d := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (fun i b => ?_) :
    ψ.comp (DirectSum.toAddMonoid φ) = DirectSum.toAddMonoid fun i => ψ.comp (φ i)) d
  rw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
  rfl

end DirectSumLemmas

section Presheaf

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

attribute [local instance] Classical.decEq

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]

/-- **The divisor map on sections over an irreducible quasi-compact étale `X`-scheme**, with
values in the coproduct of the *underlying presheaves* of the skyscrapers `(i_x)_* 𝐙`: an
invertible global function on the generic fibre of `U` is sent to its finitely supported family of
orders of vanishing, assembled by the universal property of the direct sum.

The family is finitely supported because a rational function on a Noetherian scheme has finitely
many zeros and poles, which is where quasi-compactness of `U` is used. -/
def genericFibreDivisorPresheafMap (U : X.Etale) [AlgebraicGeometry.IsIntegral U.left]
    [IsLocallyNoetherian U.left] [NoetherianSpace U.left] :
    ((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
        (Spec X.functionField))).obj.obj (op U) ⟶
      (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).obj (op U) :=
  AddCommGrpCat.ofHom
    ((DirectSum.toAddMonoid fun x : closedPoints X =>
        ((Sigma.ι (fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj) x).app
          (op U)).hom).comp
      ((genericFibreDivisorSections.{u, v} U).comp AddEquiv.ulift.toAddMonoidHom))

/-- The divisor map sends a section `s` to the image of its family of orders of vanishing under
the map out of the direct sum given by the coproduct inclusions of the skyscrapers. -/
theorem genericFibreDivisorPresheafMap_apply (U : X.Etale)
    [AlgebraicGeometry.IsIntegral U.left] [IsLocallyNoetherian U.left] [NoetherianSpace U.left]
    (s : ToType (((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
      (Spec X.functionField))).obj.obj (op U))) :
    genericFibreDivisorPresheafMap.{u, v} U s =
      DirectSum.toAddMonoid (fun x : closedPoints X =>
          ((Sigma.ι (fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj) x).app
            (op U)).hom)
        (genericFibreDivisorSections.{u, v} U s.down) :=
  rfl

/-- **The divisor map on sections is natural in the irreducible quasi-compact étale
`X`-scheme.** -/
theorem genericFibreDivisorPresheafMap_naturality {U V : X.Etale}
    [AlgebraicGeometry.IsIntegral U.left] [IsLocallyNoetherian U.left] [NoetherianSpace U.left]
    [AlgebraicGeometry.IsIntegral V.left] [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (h : V ⟶ U) :
    ((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
          (Spec X.functionField))).obj.map h.op ≫ genericFibreDivisorPresheafMap.{u, v} V =
      genericFibreDivisorPresheafMap.{u, v} U ≫
        (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).map h.op := by
  ext s
  set f : ∀ x : closedPoints X,
      ((closedPointSkyscraper.{u, v} X x).obj.obj (op U) : Type _) →+
        ((closedPointSkyscraper.{u, v} X x).obj.obj (op V) : Type _) :=
    fun x => ((closedPointSkyscraper.{u, v} X x).obj.map h.op).hom with hf
  set ιV : ∀ x : closedPoints X,
      ((closedPointSkyscraper.{u, v} X x).obj.obj (op V) : Type _) →+
        ((∐ fun y : closedPoints X ↦
          (closedPointSkyscraper.{u, v} X y).obj).obj (op V) : Type _) :=
    fun x => ((Sigma.ι (fun y : closedPoints X ↦
      (closedPointSkyscraper.{u, v} X y).obj) x).app (op V)).hom with hιV
  set ιU : ∀ x : closedPoints X,
      ((closedPointSkyscraper.{u, v} X x).obj.obj (op U) : Type _) →+
        ((∐ fun y : closedPoints X ↦
          (closedPointSkyscraper.{u, v} X y).obj).obj (op U) : Type _) :=
    fun x => ((Sigma.ι (fun y : closedPoints X ↦
      (closedPointSkyscraper.{u, v} X y).obj) x).app (op U)).hom with hιU
  set mapH := ((∐ fun x : closedPoints X ↦
    (closedPointSkyscraper.{u, v} X x).obj).map h.op).hom with hmapH
  have hstep : genericFibreDivisorSections.{u, v} V (genericFibreUnitsRestrict h s.down) =
      DFinsupp.mapRange (fun (x : closedPoints X) b => f x b) (fun x => map_zero (f x))
        (genericFibreDivisorSections.{u, v} U s.down) := by
    refine DFinsupp.ext fun x => ?_
    refine (genericFibreDivisorSections_apply.{u, v} V _ x).trans ?_
    refine (integerSkyscraperDivisor_genericFibreUnitsRestrict.{u, v} h x.1 s.down).trans ?_
    exact ((DFinsupp.mapRange_apply (fun (y : closedPoints X) b => f y b)
      (fun y => map_zero (f y)) _ x).trans
        (congrArg (f x) (genericFibreDivisorSections_apply.{u, v} U s.down x))).symm
  have hfam : (fun x : closedPoints X => (ιV x).comp (f x)) =
      fun x : closedPoints X => mapH.comp (ιU x) := by
    refine funext fun x => AddMonoidHom.ext fun b => ?_
    exact ConcreteCategory.congr_hom
      ((Sigma.ι (fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj) x).naturality
        h.op) b
  calc DirectSum.toAddMonoid ιV
        (genericFibreDivisorSections.{u, v} V (genericFibreUnitsRestrict h s.down))
      = DirectSum.toAddMonoid ιV
          (DFinsupp.mapRange (fun (x : closedPoints X) b => f x b) (fun x => map_zero (f x))
            (genericFibreDivisorSections.{u, v} U s.down)) := congrArg _ hstep
    _ = DirectSum.toAddMonoid (fun x : closedPoints X => (ιV x).comp (f x))
          (genericFibreDivisorSections.{u, v} U s.down) := toAddMonoid_mapRange f ιV _
    _ = DirectSum.toAddMonoid (fun x : closedPoints X => mapH.comp (ιU x))
          (genericFibreDivisorSections.{u, v} U s.down) :=
        congrArg (fun ψ => DirectSum.toAddMonoid ψ
          (genericFibreDivisorSections.{u, v} U s.down)) hfam
    _ = mapH (DirectSum.toAddMonoid ιU (genericFibreDivisorSections.{u, v} U s.down)) :=
        (comp_toAddMonoid mapH ιU _).symm

end Presheaf


section Integral

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsCurve k fX]

/-- **The divisor map of Stacks 03RI as a morphism of presheaves on the integral quasi-compact
subsite of the small étale site of a curve.** On each object it is
`Stacks.EtaleCohomology.genericFibreDivisorPresheafMap`, and the naturality is
`Stacks.EtaleCohomology.genericFibreDivisorPresheafMap_naturality`. -/
def genericFibreDivisorIntegral :
    (isIntegralCompactEtale X).ι.op ⋙
        ((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
          (Spec X.functionField))).obj ⟶
      (isIntegralCompactEtale X).ι.op ⋙
        (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) where
  app W :=
    haveI : AlgebraicGeometry.IsIntegral ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      W.unop.property.1
    haveI : CompactSpace ((isIntegralCompactEtale X).ι.obj W.unop).left := W.unop.property.2
    haveI : IsLocallyNoetherian ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      isLocallyNoetherian_of_etale_over_isCurve fX _
    haveI : NoetherianSpace ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      noetherianSpace_of_etale_over_isCurve fX _
    genericFibreDivisorPresheafMap.{u, v} ((isIntegralCompactEtale X).ι.obj W.unop)
  naturality W W' φ := by
    have : AlgebraicGeometry.IsIntegral ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      W.unop.property.1
    have : CompactSpace ((isIntegralCompactEtale X).ι.obj W.unop).left := W.unop.property.2
    have : IsLocallyNoetherian ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      isLocallyNoetherian_of_etale_over_isCurve fX _
    have : NoetherianSpace ((isIntegralCompactEtale X).ι.obj W.unop).left :=
      noetherianSpace_of_etale_over_isCurve fX _
    have : AlgebraicGeometry.IsIntegral ((isIntegralCompactEtale X).ι.obj W'.unop).left :=
      W'.unop.property.1
    have : CompactSpace ((isIntegralCompactEtale X).ι.obj W'.unop).left := W'.unop.property.2
    have : IsLocallyNoetherian ((isIntegralCompactEtale X).ι.obj W'.unop).left :=
      isLocallyNoetherian_of_etale_over_isCurve fX _
    have : NoetherianSpace ((isIntegralCompactEtale X).ι.obj W'.unop).left :=
      noetherianSpace_of_etale_over_isCurve fX _
    exact genericFibreDivisorPresheafMap_naturality.{u, v}
      ((isIntegralCompactEtale X).ι.map φ.unop)

variable [Smooth fX]

/-- **The second map of the fundamental exact sequence of Stacks 03RI**,
`j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙`, as a morphism of étale sheaves on a smooth curve.

It is obtained from the divisor map on the integral quasi-compact subsite by
`CategoryTheory.Functor.IsCoverDense.sheafHom`: those objects are cover-dense, so a morphism of
presheaves defined on them into a sheaf extends uniquely to the whole site. -/
def closedPointDivisorMap :
    (genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
        (Spec X.functionField)) ⟶ closedPointDivisorSheaf.{u, v} X :=
  haveI : IsNormal X := isNormal_of_smooth_isCurve fX
  ⟨Functor.IsCoverDense.sheafHom (G := (isIntegralCompactEtale X).ι)
    (genericFibreDivisorIntegral.{u, v} fX ≫
      Functor.whiskerLeft (isIntegralCompactEtale X).ι.op
        (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X))⟩

/-- **On an integral quasi-compact étale `X`-scheme the second map of the fundamental exact
sequence is the divisor map on sections**, followed by the comparison from the coproduct of the
underlying presheaves. -/
theorem closedPointDivisorMap_app (W : (isIntegralCompactEtale X).FullSubcategory) :
    (closedPointDivisorMap.{u, v} fX).hom.app (op W.obj) =
      (genericFibreDivisorIntegral.{u, v} fX).app (op W) ≫
        (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op W.obj) :=
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := (isIntegralCompactEtale X).ι) _) (op W)

/-- **The fundamental exact sequence of Stacks 03RI is a complex**: an invertible global function
on an étale `X`-scheme restricts to a function on the generic fibre with no zeros and no poles, so
its divisor vanishes. -/
theorem comparison_comp_closedPointDivisorMap :
    multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X) ≫
      closedPointDivisorMap.{u, v} fX = 0 := by
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  refine Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom
    (G := (isIntegralCompactEtale X).ι)).symm.injective ?_)
  ext W a
  obtain ⟨b, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} a
  have : AlgebraicGeometry.IsIntegral W.unop.obj.left := W.unop.property.1
  have : CompactSpace W.unop.obj.left := W.unop.property.2
  have : IsLocallyNoetherian W.unop.obj.left :=
    isLocallyNoetherian_of_etale_over_isCurve fX W.unop.obj
  have : NoetherianSpace W.unop.obj.left :=
    noetherianSpace_of_etale_over_isCurve fX W.unop.obj
  have hzero : genericFibreDivisorSections.{u, v} W.unop.obj
      (Additive.ofMul (Units.map (pullback.fst W.unop.obj.hom
        (genericPointInclusion X)).appTop.hom.toMonoidHom b)) = 0 :=
    genericFibreDivisorSections_restrict_eq_zero.{u, v} W.unop.obj b
  have key : (closedPointDivisorMap.{u, v} fX).hom.app (op W.unop.obj)
      ((multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom.app
        (op W.unop.obj) (Stacks.Kummer.ofUnit.{u, v} b)) = 0 := by
    refine (ConcreteCategory.congr_hom (closedPointDivisorMap_app.{u, v} fX W.unop) _).trans ?_
    calc (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op W.unop.obj)
          (DirectSum.toAddMonoid (fun x : closedPoints X =>
              ((Sigma.ι (fun y : closedPoints X ↦
                (closedPointSkyscraper.{u, v} X y).obj) x).app (op W.unop.obj)).hom)
            (genericFibreDivisorSections.{u, v} W.unop.obj
              (Additive.ofMul (Units.map (pullback.fst W.unop.obj.hom
                (genericPointInclusion X)).appTop.hom.toMonoidHom b))))
        = (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op W.unop.obj)
            (DirectSum.toAddMonoid (fun x : closedPoints X =>
              ((Sigma.ι (fun y : closedPoints X ↦
                (closedPointSkyscraper.{u, v} X y).obj) x).app (op W.unop.obj)).hom) 0) :=
          congrArg _ (congrArg _ hzero)
      _ = 0 := by rw [map_zero, map_zero]
  exact key

end Integral

end Stacks.EtaleCohomology

end
