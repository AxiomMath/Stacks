module

public import Mathlib.Topology.Category.TopCommRingCat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical
public import StacksFrontier.Topology.Algebra.RingLimits

/-!
# Structure sheaves of formal algebraic spaces

Let `X` be a formal algebraic space over a scheme `S` of a big fppf site. Section 0DEI of the
Stacks project calls a *structure sheaf for `X`* a sheaf of topological rings `𝒪_X` on the small
étale site `X_étale` (Section 0DE9) such that

`𝒪_X(U_red) = lim Γ(U_λ, 𝒪_{U_λ})` as topological rings

whenever `φ : U ⟶ X` is a morphism of formal algebraic spaces with `U` an affine formal algebraic
space and `φ` representable by algebraic spaces and étale, `U_red ⟶ X_red` is the corresponding
affine object of `X_étale` (Stacks 0DEH), and `U = colim U_λ` is a colimit presentation of `U` as
in Stacks 0AI7. This file sets up that definition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.discreteRingULift`: a commutative ring, raised one universe and
  given the discrete topology.
* `AlgebraicGeometry.FormalSpace.discreteFunctions`: the global functions `Γ(T, 𝒪_T)` of the
  affine objects `T` of the site, as discrete topological rings.
* `AlgebraicGeometry.FormalSpace.ThickeningPresentation`: a colimit presentation
  `U = colim U_λ` of an fppf sheaf as in Stacks 0AI7, as data; its
  `AlgebraicGeometry.FormalSpace.ThickeningPresentation.rings` is the inverse system
  `λ ↦ Γ(U_λ, 𝒪_{U_λ})` of discrete rings, whose limit in topological rings carries the
  inverse-limit topology.
* `AlgebraicGeometry.FormalSpace.Reduction.affineChartMap`: an affine object `W` of `X_étale`,
  read as a morphism into the reduction `X_red`.
* `AlgebraicGeometry.FormalSpace.IsStructureSheaf`: **the structure sheaves of Section 0DEI**.

## Implementation notes

*The affine object corresponding to `U`.* Stacks 0DEH identifies the affine objects of
`X_étale` with the morphisms `φ : U ⟶ X` above, by `U ↦ U ×_X X_red`. The definition does not
fix a model of that fibre product: it quantifies over every affine object `W` of `X_étale`
together with a morphism `a : W ⟶ U` exhibiting `W` as `U ×_X X_red`, i.e. making the square
with `φ`, the inclusion `X_red ⟶ X` and the structure morphism `W ⟶ X_red` cartesian. Any two
such `W` are canonically isomorphic, and the identifications are required to commute with
them, so this is the source's condition with the choice of model removed.

*"`=` as topological rings".* The equality is an isomorphism of topological rings
`𝒪_X(W) ≅ lim_λ Γ(U_λ, 𝒪_{U_λ})`, one for each square and each presentation, and these
isomorphisms are required to be the canonical ones: for a morphism `g : U ⟶ V` over `X`, a
morphism `h : W ⟶ W'` of affine objects over it, and a morphism `t : U_λ ⟶ V_μ` of stages over
it, restriction along `h` followed by the projection to `Γ(U_λ)` is the projection to `Γ(V_μ)`
followed by `t^*`. With `g`, `h` the identities this says that the isomorphisms attached to two
presentations of one `U` differ by the canonical identification of the two limits, and in
general that the identifications are compatible with the restriction maps of `𝒪_X`.

*Universes.* The stages of a presentation are indexed by a directed preorder in `Type (u + 1)`,
as in `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`, so the limit is taken in
`TopCommRingCat.{u + 1}` and the rings `Γ(U_λ, 𝒪_{U_λ})` are raised to that universe.

## References

* [Stacks Project, Section 0DEI](https://stacks.math.columbia.edu/tag/0DEI)
* [Stacks Project, Tag 0DEH](https://stacks.math.columbia.edu/tag/0DEH)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.FormalSpace

/-! ### Discrete rings of functions -/

/-- A commutative ring raised to a higher universe and given the discrete topology, as a
topological ring. -/
noncomputable def discreteRingULift : CommRingCat.{u} ⥤ TopCommRingCat.{max u v} where
  obj R :=
    letI : TopologicalSpace (ULift.{v} R) := ⊥
    haveI : DiscreteTopology (ULift.{v} R) := ⟨rfl⟩
    TopCommRingCat.of (ULift.{v} R)
  map {R R'} f :=
    letI : TopologicalSpace (ULift.{v} R) := ⊥
    letI : TopologicalSpace (ULift.{v} R') := ⊥
    haveI : DiscreteTopology (ULift.{v} R) := ⟨rfl⟩
    ⟨ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom),
      continuous_of_discreteTopology⟩
  map_id _ := Subtype.ext (RingHom.ext fun _ => rfl)
  map_comp _ _ := Subtype.ext (RingHom.ext fun _ => rfl)

/-- The topology on `discreteRingULift.obj R` is discrete. -/
instance (R : CommRingCat.{u}) : DiscreteTopology (discreteRingULift.{v}.obj R) := ⟨rfl⟩

/-- The ring map `discreteRingULift.map f` sends `x` to `ULift.up (f x.down)`. -/
@[simp]
theorem discreteRingULift_map_apply {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (x : discreteRingULift.{v}.obj R) :
    discreteRingULift.{v}.map f x = ULift.up (f x.down) :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global functions `Γ(T, 𝒪_T)` of the affine objects `T` of the big fppf site of `S`, as
discrete topological rings in the universe of the formal algebraic spaces over `S`. -/
noncomputable def discreteFunctions : (BigAffineFppf B S hS)ᵒᵖ ⥤ TopCommRingCat.{u + 1} :=
  (BigAffineFppf.toScheme B S hS).op ⋙ Scheme.Γ ⋙ discreteRingULift.{u + 1}

/-- The topology on `(discreteFunctions B S hS).obj T` is discrete. -/
instance (T : (BigAffineFppf B S hS)ᵒᵖ) : DiscreteTopology ((discreteFunctions B S hS).obj T) :=
  inferInstanceAs (DiscreteTopology (discreteRingULift.{u + 1}.obj _))

/-! ### Colimit presentations of affine formal algebraic spaces -/

/-- A *colimit presentation* `U = colim U_λ` of an fppf sheaf `U` over `S` as in Stacks 0AI7: a
directed system of affine objects of the site whose transition morphisms are thickenings,
together with an identification of `U` with the colimit of the sheaves they represent. An fppf
sheaf satisfying the set-theoretic condition of Stacks 0AIS is an affine formal algebraic space
exactly when it has one (`AlgebraicGeometry.FormalSpace.nonempty_thickeningPresentation`). -/
structure ThickeningPresentation (U : FppfSheaf B S hS) where
  /-- The index of the stages. -/
  Index : Type (u + 1)
  /-- The directed preorder on the index. -/
  [preorder : Preorder Index]
  [nonempty : Nonempty Index]
  [directed : IsDirected Index (· ≤ ·)]
  /-- The stages, affine objects of the site. -/
  diagram : Index ⥤ BigAffineFppf B S hS
  /-- The transition morphisms are thickenings. -/
  isThickening : ∀ ⦃i j : Index⦄ (f : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (diagram.map f))
  /-- The identification of `U` with the colimit of the represented stages. -/
  iso : U ≅ colimit (diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

attribute [instance] ThickeningPresentation.preorder ThickeningPresentation.nonempty
  ThickeningPresentation.directed

namespace ThickeningPresentation

variable {B S hS} {U : FppfSheaf B S hS} (P : ThickeningPresentation B S hS U)

/-- The inverse system `λ ↦ Γ(U_λ, 𝒪_{U_λ})` of discrete topological rings of a presentation;
its limit in `TopCommRingCat` is the inverse limit with its inverse-limit topology. -/
noncomputable abbrev rings : P.Indexᵒᵖ ⥤ TopCommRingCat.{u + 1} :=
  P.diagram.op ⋙ discreteFunctions B S hS

/-- The inclusion of the stage `U_λ` into `U`. -/
noncomputable def stageMap (i : P.Index) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj i)) ⟶ U :=
  colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ P.iso.inv

/-- The stage inclusions are compatible with the transition morphisms. -/
@[reassoc]
theorem map_stageMap {i j : P.Index} (f : i ⟶ j) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) ≫ P.stageMap j =
      P.stageMap i := by
  rw [stageMap, stageMap]
  exact colimit.w_assoc (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f P.iso.inv

end ThickeningPresentation

/-- **Stacks 0AI7**, read through presentations: an fppf sheaf over `S` is an affine formal
algebraic space exactly when it satisfies the set-theoretic condition of Stacks 0AIS and has a
colimit presentation by affine thickenings. -/
theorem isAffineFormalAlgebraicSpace_iff_nonempty_thickeningPresentation (U : FppfSheaf B S hS) :
    IsAffineFormalAlgebraicSpace B S hS U ↔
      SatisfiesSetTheoreticCondition B S hS U ∧ Nonempty (ThickeningPresentation B S hS U) := by
  constructor
  · rintro ⟨hset, I, pre, hne, hdir, D, hD, ⟨e⟩⟩
    exact ⟨hset, ⟨@ThickeningPresentation.mk B S hS U I pre hne hdir D hD e⟩⟩
  · rintro ⟨hset, ⟨P⟩⟩
    exact ⟨hset, P.Index, P.preorder, P.nonempty, P.directed, P.diagram, P.isThickening,
      ⟨P.iso⟩⟩

/-- An affine formal algebraic space has a colimit presentation by affine thickenings. -/
theorem nonempty_thickeningPresentation {U : FppfSheaf B S hS}
    (hU : IsAffineFormalAlgebraicSpace B S hS U) :
    Nonempty (ThickeningPresentation B S hS U) :=
  ((isAffineFormalAlgebraicSpace_iff_nonempty_thickeningPresentation B S hS U).mp hU).2

/-! ### Affine objects of the small étale site as charts of the reduction -/

/-- The identification of the universe lift of a representable algebraic space with the
sheafified representable is natural. -/
@[reassoc]
theorem sheafifiedYoneda_map_liftSheafYonedaSpaceIsoSheafifiedYoneda_inv
    {T T' : BigFppfOver B S hS} (f : T ⟶ T') :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f ≫
        (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS T').inv =
      (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS T).inv ≫
        liftSheafMap B S hS ((schemeSpaceFunctor B S hS).map f) :=
  (yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda B S hS).inv.naturality f

namespace Reduction

variable {B S hS} {X : FppfSheaf B S hS} (R : Reduction B S hS X)

/-- The scheme underlying an affine object `W` of `X_affine,étale = X_red,affine,étale`. -/
abbrev affineChartObj (W : R.AffineEtale) : BigFppfOver B S hS :=
  (Space.AffineEtale.toOver B S hS R.space.obj).obj W

/-- An affine object `W` of `X_affine,étale` as a morphism of algebraic spaces from the scheme
underlying it to the reduction `X_red`. -/
def affineChartSpaceMap (W : R.AffineEtale) :
    (schemeSpaceFunctor B S hS).obj (R.affineChartObj W) ⟶ R.space :=
  ObjectProperty.homMk W.obj.obj.hom

/-- The chart morphisms of affine objects as morphisms of algebraic spaces are compatible with
the morphisms between them. -/
@[reassoc]
theorem map_affineChartSpaceMap {W W' : R.AffineEtale} (h : W ⟶ W') :
    (schemeSpaceFunctor B S hS).map ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫
      R.affineChartSpaceMap W' = R.affineChartSpaceMap W :=
  ObjectProperty.hom_ext _ (CostructuredArrow.w h.hom.hom)

/-- An affine object `W` of `X_affine,étale` as a morphism of fppf sheaves from the sheaf it
represents to the reduction `X_red`: the universe lift of its chart morphism. -/
noncomputable def affineChartMap (W : R.AffineEtale) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      liftSheaf B S hS R.space :=
  (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS (R.affineChartObj W)).inv ≫
    liftSheafMap B S hS (R.affineChartSpaceMap W)

/-- The chart morphisms of affine objects of `X_affine,étale` are compatible with the morphisms
between them. -/
@[reassoc]
theorem map_affineChartMap {W W' : R.AffineEtale} (h : W ⟶ W') :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ R.affineChartMap W' =
      R.affineChartMap W := by
  rw [affineChartMap, affineChartMap, ← Category.assoc,
    sheafifiedYoneda_map_liftSheafYonedaSpaceIsoSheafifiedYoneda_inv, Category.assoc,
    ← liftSheafMap_comp, R.map_affineChartSpaceMap h]

end Reduction

/-! ### Structure sheaves -/

variable {B S hS}

/-- **Section 0DEI, the structure sheaves of a formal algebraic space.** A sheaf `O` of
topological rings on the small étale site `X_étale` of a formal algebraic space `X` is a
*structure sheaf for `X`* when its sections over the affine object of `X_étale` corresponding to
a morphism `φ : U ⟶ X` — with `U` an affine formal algebraic space and `φ` representable by
algebraic spaces and étale — are `lim_λ Γ(U_λ, 𝒪_{U_λ})` as topological rings, for every colimit
presentation `U = colim U_λ` as in Stacks 0AI7, canonically.

Precisely, there are isomorphisms of topological rings
`compare U W a P : O(W) ≅ lim_λ Γ(U_λ, 𝒪_{U_λ})`, for every object `U` of the category of
Stacks 0DEE over `X`, every affine object `W` of `X_étale` and morphism `a` exhibiting `W` as
`U ×_X X_red` (the corresponding affine object of Stacks 0DEH), and every presentation `P` of
`U`, which are compatible with all morphisms: given `g : U ⟶ V` over `X`, a morphism `h : W ⟶ W'`
of affine objects lying over it, and a morphism `t : U_λ ⟶ V_μ` of stages lying over it,
restricting along `h` and projecting to `Γ(U_λ)` is projecting to `Γ(V_μ)` and pulling back
along `t`. See the module docstring for why this is the source's "`=`". -/
def IsStructureSheaf {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (O : Sheaf (canonicalSmallEtaleTopology hX) TopCommRingCat.{u + 1}) : Prop :=
  ∃ compare : ∀ (U : AffineEtaleFormalCharts B S hS X) (W : canonicalAffineEtale hX)
      (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((canonicalReduction hX).affineChartObj W) ⟶ U.obj.left),
      IsPullback a ((canonicalReduction hX).affineChartMap W) U.obj.hom
        (canonicalReduction hX).inclusion →
      ∀ P : ThickeningPresentation B S hS U.obj.left,
        O.obj.obj (op ((Space.AffineEtale.inclusion B S hS (canonicalReduction hX).space.obj).obj
          W)) ≅ limit P.rings,
    ∀ (U V : AffineEtaleFormalCharts B S hS X) (W W' : canonicalAffineEtale hX)
      (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((canonicalReduction hX).affineChartObj W) ⟶ U.obj.left)
      (a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((canonicalReduction hX).affineChartObj W') ⟶ V.obj.left)
      (ha : IsPullback a ((canonicalReduction hX).affineChartMap W) U.obj.hom
        (canonicalReduction hX).inclusion)
      (ha' : IsPullback a' ((canonicalReduction hX).affineChartMap W') V.obj.hom
        (canonicalReduction hX).inclusion)
      (g : U ⟶ V) (h : W ⟶ W'),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((Space.AffineEtale.toOver B S hS (canonicalReduction hX).space.obj).map h) ≫ a' =
        a ≫ g.hom.left →
      ∀ (P : ThickeningPresentation B S hS U.obj.left)
        (Q : ThickeningPresentation B S hS V.obj.left) (i : P.Index) (j : Q.Index)
        (t : P.diagram.obj i ⟶ Q.diagram.obj j),
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map t) ≫ Q.stageMap j =
          P.stageMap i ≫ g.hom.left →
        O.obj.map ((Space.AffineEtale.inclusion B S hS
              (canonicalReduction hX).space.obj).map h).op ≫
            (compare U W a ha P).hom ≫ limit.π P.rings (op i) =
          (compare V W' a' ha' Q).hom ≫ limit.π Q.rings (op j) ≫
            (discreteFunctions B S hS).map t.op

end AlgebraicGeometry.FormalSpace

end
