module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.Cotangent.SchemeCotangentComplex
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilon

/-!
# The square of Remark 08GH for a morphism of representable algebraic spaces

Let `h : T₁ ⟶ T₂` be a morphism of the big fppf site over `S`, let `f : X ⟶ Y` be the morphism
of algebraic spaces it represents and `f₀ : X₀ ⟶ Y₀` the morphism of schemes underlying it.  The
comparisons `ε` of `StacksFrontier/Cotangent/Spaces/RepresentableEpsilon.lean` sit in the
commutative diagram of Derived Categories of Spaces, Remark 08GH,

```
X₀,Zar <--ε-- X_étale
  |             |
  f₀            f
  v             v
Y₀,Zar <--ε-- Y_étale
```

and the proof of Stacks 08VF reads off from it a canonical map
`ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` compatible with `ε♯ : ε⁻¹𝒪_{X₀} ⟶ 𝒪_X`.  This file constructs
that map and proves the compatibility.

## Main definitions

* `AlgebraicGeometry.Space.chartComparisonCommRing`: for a representable morphism, the direct
  image of sheaves of commutative rings along `f_small` is restriction along chart base change.
* `AlgebraicGeometry.Space.representedOpensBaseChangeIso`: the geometric half of the square —
  taking the preimage of an open of `Y₀` and viewing it as an étale chart of `X` is viewing the
  open as an étale chart of `Y` and base-changing along `f`.
* `AlgebraicGeometry.Space.representedBaseChangeRestriction`: restriction of sheaves along that
  isomorphism.
* `AlgebraicGeometry.Space.representedOpensStructureMap`: the structure map of `ε` with
  sections in `u`, whose lift is `AlgebraicGeometry.Space.representedZariskiSharp`.
* `AlgebraicGeometry.Space.representedBaseSharp`: the composite
  `𝒪_{Y₀} ⟶ ε_{Y,*}𝒪_Y ⟶ ε_{Y,*}f_{small,*}f_small⁻¹𝒪_Y ⟶ f₀,*ε_{X,*}f_small⁻¹𝒪_Y` of `ε_Y♯`,
  the unit of `f_small` and the square.
* `AlgebraicGeometry.Space.representedBaseMapU` and
  `AlgebraicGeometry.Space.representedBaseMap`: its transposes
  `f₀⁻¹𝒪_{Y₀} ⟶ ε_{X,*}f_small⁻¹𝒪_Y` (sections in `u`) and
  `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` (sections lifted to `u + 1`), the latter being the canonical
  map of the proof of Stacks 08VF.

## Main results

* `AlgebraicGeometry.Space.fSharp_comp_chartComparisonCommRing`: Stacks 03G8 (2) through the
  ring-level chart comparison: `f_small♯` is pullback along the cartesian projections.
* `AlgebraicGeometry.Space.representedBaseSharp_comp_fSharpInverseImage_eq`: the square on the
  Zariski site of `Y₀`, before transposing along `f₀`.
* `AlgebraicGeometry.Space.representedBaseMapU_square`: the square on the Zariski site of `X₀`,
  with sections in `u`.
* `AlgebraicGeometry.Space.representedBaseMap_square`: **the square of the proof of
  Stacks 08VF** —
  `ε⁻¹(f₀♯) ≫ ε♯ = baseMap ≫ f_small♯` as maps `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_X`, all sections lifted to
  `u + 1`; the structure map on the left is the lift of the inverse-image form of the structure
  map of `AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom`, the one Definition 08T2 forms
  `L_{X₀/Y₀}` from, and the one on the right is the base map of
  `AlgebraicGeometry.Space.cotangentComplex`.

## Implementation notes

`representedBaseMap` is canonical: it is built only from adjunction units, the structure maps
`ε♯` and `f_small♯`, and the isomorphisms identifying the two composite site functors and the
direct image along `f_small` with chart base change.  Those isomorphisms involve no choice:
morphisms of étale charts into the base change of an open are unique, and the comparison of the
direct image with chart base change is the projection of a limit to an initial object.

The proof of the square is by transposing twice, along `ε_X⁻¹ ⊣ ε_{X,*}` and
`f₀⁻¹ ⊣ f₀,*`; after that it is the identity of sections
`Γ(V) ⟶ Γ(X ×_Y V) ⟶ Γ(f₀⁻¹V)` with `f₀♯` restricted to `f₀⁻¹V`, which is
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`, together with the chart formula
`AlgebraicGeometry.Space.chartComparison_structureSharp` for `f_small♯`.

## References

* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Transposing the identity along an adjunction `L ⊣ R`, carrying it along natural
transformations `c : R ⟶ Q` and `ρ : Q ⋙ P ⟶ Φ`, and following it by `Φ` applied to the transpose
of `φ` is the same as carrying `φ` itself along `c` and `ρ`. -/
theorem map_homEquiv_id_comp_map_homEquiv_symm {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {Q : D ⥤ C} (c : R ⟶ Q) {P : C ⥤ E} {Φ : D ⥤ E} (ρ : Q ⋙ P ⟶ Φ) {e : E} {O : C} {X : D}
    (x : e ⟶ P.obj O) (φ : O ⟶ R.obj X) :
    (x ≫ P.map (adj.homEquiv O (L.obj O) (𝟙 _) ≫ c.app (L.obj O)) ≫ ρ.app (L.obj O)) ≫
        Φ.map ((adj.homEquiv O X).symm φ) =
      x ≫ P.map (φ ≫ c.app X) ≫ ρ.app X := by
  rw [Category.assoc, Category.assoc, ← ρ.naturality, Functor.comp_map, ← Category.assoc
    (P.map _), ← P.map_comp, Category.assoc, ← c.naturality,
    ← Category.assoc (adj.homEquiv O (L.obj O) (𝟙 _)), ← adj.homEquiv_naturality_right,
    Category.id_comp, Equiv.apply_symm_apply]

/-- Two transposes along an adjunction `L ⊣ R`, with `R` identified with a functor `M`, compose
equally with two maps as soon as the untransposed maps do after `M`. -/
theorem homEquiv_symm_comp_eq_homEquiv_symm_comp {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {M : D ⥤ C} (e : R ≅ M) {A : C} {B B' B'' : D} {z : A ⟶ M.obj B} {γ : A ⟶ M.obj B'}
    {b : B ⟶ B''} {c : B' ⟶ B''} (hyp : z ≫ M.map b = γ ≫ M.map c) :
    (adj.homEquiv A B).symm (z ≫ e.inv.app B) ≫ b =
      (adj.homEquiv A B').symm (γ ≫ e.inv.app B') ≫ c := by
  apply (adj.homEquiv A B'').injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Category.assoc, Category.assoc, ← e.inv.naturality,
    ← e.inv.naturality, ← Category.assoc, ← Category.assoc, hyp]

/-- Precomposing a transpose along an adjunction `L ⊣ R` with `L` applied to a map, with `R`
identified with a functor `M`: the composite is the transpose of another map followed by a map
as soon as the untransposed maps agree after `M`. -/
theorem map_comp_homEquiv_symm_eq_homEquiv_symm_comp {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {M : D ⥤ C} (e : R ≅ M) {A₀ A : C} {B B' : D} {p : A₀ ⟶ A} {z : A ⟶ M.obj B}
    {γ : A₀ ⟶ M.obj B'} {c : B' ⟶ B} (hyp : p ≫ z = γ ≫ M.map c) :
    L.map p ≫ (adj.homEquiv A B).symm (z ≫ e.inv.app B) =
      (adj.homEquiv A₀ B').symm (γ ≫ e.inv.app B') ≫ c := by
  apply (adj.homEquiv A₀ B).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Category.assoc, ← e.inv.naturality, ← Category.assoc,
    ← Category.assoc, hyp]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Direct image along a representable morphism, on sheaves of commutative rings -/

section ChartComparison

variable {X Y : AlgebraicSpaces B S hS}

/-- For a representable morphism `f : X ⟶ Y`, the direct image of sheaves of commutative rings
along `f_small` is restriction along chart base change.  On underlying sheaves of sets this is
`AlgebraicGeometry.Space.chartComparison`, the comparison computable on sections. -/
noncomputable def chartComparisonCommRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1)
      (chartComparison B S hS f hf) ≪≫
    restrictionCommRingNatIso.{u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)

/-- On sections, the ring-level chart comparison is the chart comparison of the underlying
sheaves of sets. -/
theorem chartComparisonCommRing_hom_app_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) (V : SmallEtale B S hS Y.1)
    (x : ((pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom).obj O).obj.obj (op V)) :
    ((chartComparisonCommRing B S hS f hf).hom.app O).hom.app (op V) x =
      ((chartComparison B S hS f hf).hom.app
        ((sheafCompose _ (forget CommRingCat.{u})).obj O)).hom.app (op V) x :=
  rfl

/-- **Stacks 03G8, part (2), through the ring-level chart comparison.**  For a representable
morphism `f`, the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` followed by
`AlgebraicGeometry.Space.chartComparisonCommRing` is pullback of regular functions along the
cartesian projections `X ×_Y V ⟶ V`. -/
theorem fSharp_comp_chartComparisonCommRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (smallEtaleRingedToposHom B S hS f).fSharp ≫
        (chartComparisonCommRing B S hS f hf).hom.app (smallEtaleRingedTopos B S hS X).O =
      cartesianProjectionSharpCommRing B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  ext V s
  exact chartComparison_structureSharp B S hS f hf V.unop s

end ChartComparison

/-! ### The geometric half of the square -/

section Square

variable {T₁ T₂ : BigFppfOver B S hS} (h : T₁ ⟶ T₂)

/-- Chart base change along the morphism of algebraic spaces represented by a morphism of the big
fppf site is continuous. -/
instance isContinuous_smallBaseChange_representedSpaceMap :
    (smallBaseChange B S hS (representedSpaceMap B S hS h)
      (relativelyRepresentable_yoneda_map B S hS h)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T₂)) (SmallEtale.topology B S hS (yoneda.obj T₁)) :=
  isContinuous_smallBaseChange B S hS _ _

/-- Taking preimages of opens along the morphism of schemes underlying `h` and viewing them as
étale charts of `yoneda.obj T₁` is continuous. -/
instance isContinuous_opensMap_comp_representedOpensToSmallEtale :
    (Opens.map ((BigFppfOver.toScheme B S hS).map h).base ⋙
        representedOpensToSmallEtale B S hS T₁).IsContinuous
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (SmallEtale.topology B S hS (yoneda.obj T₁)) :=
  haveI := (Opens.isMorphismOfSites_map ((BigFppfOver.toScheme B S hS).map h).base).isContinuous
  Functor.isContinuous_comp _ _ _
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁)) _

/-- Viewing an open of `Y₀` as an étale chart of `yoneda.obj T₂` and base-changing it along the
represented morphism is continuous. -/
instance isContinuous_representedOpensToSmallEtale_comp_smallBaseChange :
    (representedOpensToSmallEtale B S hS T₂ ⋙ smallBaseChange B S hS
        (representedSpaceMap B S hS h) (relativelyRepresentable_yoneda_map B S hS h)).IsContinuous
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (SmallEtale.topology B S hS (yoneda.obj T₁)) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS (yoneda.obj T₂)) _

/-- **The geometric half of the square of Remark 08GH.**  For `h : T₁ ⟶ T₂` with underlying
morphism of schemes `f₀ : X₀ ⟶ Y₀`, taking the preimage `f₀⁻¹V` of an open `V ⊆ Y₀` and viewing
it as an étale chart of `yoneda.obj T₁` is viewing `V` as an étale chart of `yoneda.obj T₂` and
base-changing it along the represented morphism.

It is assembled from the scheme statement `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` (the
base change of an open is the preimage open) and the compatibility
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` of the equivalences of small étale
sites with chart base change. -/
noncomputable def representedOpensBaseChangeIso :
    Opens.map ((BigFppfOver.toScheme B S hS).map h).base ⋙
        representedOpensToSmallEtale B S hS T₁ ≅
      representedOpensToSmallEtale B S hS T₂ ⋙ smallBaseChange B S hS
        (representedSpaceMap B S hS h) (relativelyRepresentable_yoneda_map B S hS h) :=
  Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left)
      (representedSmallEtaleEquivalence B S hS T₁).inverse ≪≫
    Functor.isoWhiskerLeft
      (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property)
      (Iso.inverseCompIso (Iso.isoCompInverse
        (representedSmallEtaleBaseChangeIso B S hS h
          (relativelyRepresentable_yoneda_map B S hS h)) ≪≫ Functor.associator _ _ _)).symm

/-- The étale chart of `yoneda.obj T` given by an open `W` of `X₀` lies over `X₀` by the open
immersion of `W`. -/
theorem toScheme_map_yonedaEquiv_representedOpensToSmallEtale {T : BigFppfOver B S hS}
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    ((BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((representedOpensToSmallEtale B S hS T).obj W).1.hom) :
        W.toScheme ⟶ (BigFppfOver.toScheme B S hS).obj T) = W.ι :=
  Category.id_comp _

/-- **A morphism of étale charts from a preimage open to the base change of an open lies over
`f₀`.**  For an open `V ⊆ Y₀` and any morphism of étale charts of `yoneda.obj T₁` from the
preimage `f₀⁻¹V` to the base change of `V`, the underlying morphism of schemes followed by the
cartesian projection to `V` is the restriction of `f₀`: both lie over `f₀` and `V ⟶ Y₀` is a
monomorphism. -/
theorem toScheme_map_hom_snd_comp_ι (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (k : (representedOpensToSmallEtale B S hS T₁).obj
        ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).obj V) ⟶
      (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).obj
          ((representedOpensToSmallEtale B S hS T₂).obj V)) :
    ((BigFppfOver.toScheme B S hS).map (k.hom.left ≫
        (relativelyRepresentable_yoneda_map B S hS h).snd
          ((representedOpensToSmallEtale B S hS T₂).obj V).1.hom) :
        (((BigFppfOver.toScheme B S hS).map h) ⁻¹ᵁ V).toScheme ⟶ V.toScheme) ≫ V.ι =
      (((BigFppfOver.toScheme B S hS).map h) ⁻¹ᵁ V).ι ≫ (BigFppfOver.toScheme B S hS).map h := by
  let hf := relativelyRepresentable_yoneda_map B S hS h
  let P := (representedOpensToSmallEtale B S hS T₂).obj V
  let Q := (representedOpensToSmallEtale B S hS T₁).obj
    ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).obj V)
  have hk : yoneda.map k.hom.left ≫ hf.fst P.1.hom = Q.1.hom := CostructuredArrow.w k.hom
  have hpb : hf.fst P.1.hom ≫ yoneda.map h = yoneda.map (hf.snd P.1.hom) ≫ P.1.hom :=
    (hf.isPullback P.1.hom).w
  have hy : yoneda.map (k.hom.left ≫ hf.snd P.1.hom) ≫ P.1.hom = Q.1.hom ≫ yoneda.map h :=
    (congrArg (· ≫ P.1.hom) (yoneda.map_comp k.hom.left (hf.snd P.1.hom))).trans
      ((Category.assoc _ _ _).trans ((congrArg (yoneda.map k.hom.left ≫ ·) hpb.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map h) hk))))
  have he : (k.hom.left ≫ hf.snd P.1.hom) ≫ yonedaEquiv P.1.hom = yonedaEquiv Q.1.hom ≫ h := by
    have := congrArg yonedaEquiv hy
    rwa [← yonedaEquiv_naturality, yonedaEquiv_comp] at this
  have hs := congrArg (BigFppfOver.toScheme B S hS).map he
  rwa [Functor.map_comp, Functor.map_comp, toScheme_map_yonedaEquiv_representedOpensToSmallEtale,
    toScheme_map_yonedaEquiv_representedOpensToSmallEtale] at hs

/-! ### The structure maps -/

/-- The structure map of `ε` in restriction form, with the sections of the structure sheaves in
the universe `u` of the scheme: over an open `W ⊆ X₀` it is the canonical identification
`𝒪_{X₀}(W) = Γ(W, 𝒪_W)`.  `AlgebraicGeometry.Space.representedZariskiSharp` is its lift. -/
noncomputable def representedOpensStructureMap (T : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.O ⟶
      ((representedOpensToSmallEtale B S hS T).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
          (SmallEtale.topology B S hS (yoneda.obj T))).obj
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O :=
  ObjectProperty.homMk
    (_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).hom

/-- Over an open `W ⊆ X₀`, `AlgebraicGeometry.Space.representedOpensStructureMap` is the
identification `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`. -/
@[simp]
theorem representedOpensStructureMap_hom_app (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (representedOpensStructureMap B S hS T).hom.app (op W) = (Scheme.Opens.topIso W).inv :=
  rfl

/-- `ε♯` in restriction form is the lift of the structure map with sections in `u`. -/
theorem representedZariskiSharp_eq (T : BigFppfOver B S hS) :
    representedZariskiSharp B S hS T =
      (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
        SheafOfModules.commRingCatULift.{u, u + 1}).map (representedOpensStructureMap B S hS T) :=
  rfl

/-- **Restriction along the geometric half of the square**: for a sheaf `G` of commutative rings
on `X_étale`, the map from its restriction along `V ↦ (ε_Y V) ×_Y X` (base change of the chart of
an open of `Y₀`) to its restriction along `V ↦ ε_X(f₀⁻¹V)` induced by
`AlgebraicGeometry.Space.representedOpensBaseChangeIso`, naturally in `G`. -/
noncomputable def representedBaseChangeRestriction :
    (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS (yoneda.obj T₂))
        (SmallEtale.topology B S hS (yoneda.obj T₁)) ⋙
      (representedOpensToSmallEtale B S hS T₂).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
        (SmallEtale.topology B S hS (yoneda.obj T₂)) ⟶
    (representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        (SmallEtale.topology B S hS (yoneda.obj T₁)) ⋙
      (Opens.map ((BigFppfOver.toScheme B S hS).map h).base).sheafPushforwardContinuous
        CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁)) :=
  (Functor.sheafPushforwardContinuousComp (representedOpensToSmallEtale B S hS T₂)
      (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)) CommRingCat.{u}
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (SmallEtale.topology B S hS (yoneda.obj T₂))
      (SmallEtale.topology B S hS (yoneda.obj T₁))).hom ≫
    Functor.sheafPushforwardContinuousNatTrans (representedOpensBaseChangeIso B S hS h).hom
      CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (SmallEtale.topology B S hS (yoneda.obj T₁)) ≫
    (Functor.sheafPushforwardContinuousComp
      (Opens.map ((BigFppfOver.toScheme B S hS).map h).base)
      (representedOpensToSmallEtale B S hS T₁) CommRingCat.{u}
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      (SmallEtale.topology B S hS (yoneda.obj T₁))).inv

/-- **The composite
`𝒪_{Y₀} ⟶ ε_{Y,*}𝒪_Y ⟶ ε_{Y,*}f_{small,*}f_small⁻¹𝒪_Y ⟶ f₀,*ε_{X,*}f_small⁻¹𝒪_Y`** of the
structure map of `ε_Y`, the unit of the adjunction `f_small⁻¹ ⊣ f_{small,*}`, the
identification of `f_{small,*}` with chart base change, and the geometric half
`AlgebraicGeometry.Space.representedOpensBaseChangeIso` of the square of Remark 08GH.  All
sections are in the universe `u`. -/
noncomputable def representedBaseSharp :
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedSite.O ⟶
      ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).sheafPushforwardContinuous
          CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))).obj
        (((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)) :=
  representedOpensStructureMap B S hS T₂ ≫
    ((representedOpensToSmallEtale B S hS T₂).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
        (SmallEtale.topology B S hS (yoneda.obj T₂))).map
      (((commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toToposHom).homEquiv
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O))
          (𝟙 _) ≫
        (chartComparisonCommRing B S hS (representedSpaceMap B S hS h)
          (relativelyRepresentable_yoneda_map B S hS h)).hom.app
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)) ≫
    (representedBaseChangeRestriction B S hS h).app
      ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O)

/-- **`representedBaseSharp` followed by `f_small♯`.**  The unit of
`f_small⁻¹ ⊣ f_{small,*}` followed by the direct image of the inverse-image form of `f_small♯`
is `f_small♯`; so `representedBaseSharp` followed by `f_small♯` is the structure map of `ε_Y`,
then `f_small♯` read through the chart comparison (which by Stacks 03G8 (2),
`AlgebraicGeometry.Space.fSharp_comp_chartComparisonCommRing`, is pullback of functions along
the cartesian projections `X ×_Y V ⟶ V`), then the geometric half of the square. -/
theorem representedBaseSharp_comp_fSharpInverseImage :
    representedBaseSharp B S hS h ≫
        ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).sheafPushforwardContinuous
          CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))).map
        (((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage) =
      representedOpensStructureMap B S hS T₂ ≫
        ((representedOpensToSmallEtale B S hS T₂).sheafPushforwardContinuous CommRingCat.{u}
            (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
            (SmallEtale.topology B S hS (yoneda.obj T₂))).map
          ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharp ≫
            (chartComparisonCommRing B S hS (representedSpaceMap B S hS h)
              (relativelyRepresentable_yoneda_map B S hS h)).hom.app
              (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩).O) ≫
        (representedBaseChangeRestriction B S hS h).app
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩).O :=
  Adjunction.map_homEquiv_id_comp_map_homEquiv_symm
    (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toToposHom)
    (chartComparisonCommRing B S hS (representedSpaceMap B S hS h)
      (relativelyRepresentable_yoneda_map B S hS h)).hom
    (representedBaseChangeRestriction B S hS h) (representedOpensStructureMap B S hS T₂)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharp

/-- **The section identity of the square.**  Over an open `V ⊆ Y₀`, pulling a section of
`𝒪_{Y₀}` back to `Γ(V, 𝒪_V)`, then along the cartesian projection of the base change of the
chart `V`, then along the comparison with the chart `f₀⁻¹V`, is pulling it back along `f₀` and
viewing it in `Γ(f₀⁻¹V, 𝒪)`. -/
theorem topIso_inv_comp_representedOpensBaseChange
    (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens) :
    (Scheme.Opens.topIso V).inv ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS h).snd
            ((representedOpensToSmallEtale B S hS T₂).obj V).1.hom)).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((representedOpensBaseChangeIso B S hS h).hom.app V).hom.left).op =
      ((BigFppfOver.toScheme B S hS).map h).app V ≫
        (Scheme.Opens.topIso (((BigFppfOver.toScheme B S hS).map h) ⁻¹ᵁ V)).inv := by
  rw [← Scheme.Opens.topIso_inv_appTop_of_comp _ V _
    (toScheme_map_hom_snd_comp_ι B S hS h V ((representedOpensBaseChangeIso B S hS h).hom.app V))]
  exact congrArg ((Scheme.Opens.topIso V).inv ≫ ·)
    ((congrArg Scheme.Hom.appTop (Functor.map_comp (BigFppfOver.toScheme B S hS)
      ((representedOpensBaseChangeIso B S hS h).hom.app V).hom.left
      ((relativelyRepresentable_yoneda_map B S hS h).snd
        ((representedOpensToSmallEtale B S hS T₂).obj V).1.hom))).trans
      (Scheme.Hom.comp_appTop _ _)).symm

/-- **The square of Remark 08GH on the Zariski site of `Y₀`, before transposing along `f₀`.**
`AlgebraicGeometry.Space.representedBaseSharp` followed by `f_small♯` is the structure map of
`f₀` followed by the structure map of `ε_X`: over an open `V ⊆ Y₀` both send a section of
`𝒪_{Y₀}` to its pullback along `f₀`, viewed in `Γ(f₀⁻¹V, 𝒪)`. -/
theorem representedBaseSharp_comp_fSharpInverseImage_eq :
    representedBaseSharp B S hS h ≫
        ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).sheafPushforwardContinuous
          CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))).map
        (((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage) =
      Scheme.Hom.zariskiSharp ((BigFppfOver.toScheme B S hS).map h) ≫
        ((Opens.map ((BigFppfOver.toScheme B S hS).map h).base).sheafPushforwardContinuous
          CommRingCat.{u} (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))).map
        (representedOpensStructureMap B S hS T₁) := by
  rw [representedBaseSharp_comp_fSharpInverseImage]
  ext ⟨V⟩ s
  exact (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((representedOpensBaseChangeIso B S hS h).hom.app V).hom.left).op)
      (chartComparison_structureSharp B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)
        ((representedOpensToSmallEtale B S hS T₂).obj V) ((Scheme.Opens.topIso V).inv s))).trans
    (ConcreteCategory.congr_hom (topIso_inv_comp_representedOpensBaseChange B S hS h V) s)

/-- **The canonical map `f₀⁻¹𝒪_{Y₀} ⟶ ε_{X,*}f_small⁻¹𝒪_Y`**, with sections in the universe `u`:
the transpose of `AlgebraicGeometry.Space.representedBaseSharp` under `f₀⁻¹ ⊣ f₀,*`, the inverse
image being that of the Zariski morphism of ringed topoi of Definition 08T2. -/
noncomputable def representedBaseMapU :
    (inverseImageCommRingFunctor
        (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O ⟶
      ((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
        ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O) :=
  ((commRingImageAdjunction
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).homEquiv
      _ _).symm
    (representedBaseSharp B S hS h ≫
      (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        (Opens.map ((BigFppfOver.toScheme B S hS).map h).base)
        (((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
        ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O))).inv)

/-- **The square of Remark 08GH on the Zariski site of `X₀`, with sections in `u`**: the
structure map `f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_{X₀}` of Definition 08T2 followed by the structure map of
`ε_X` is `AlgebraicGeometry.Space.representedBaseMapU` followed by `f_small♯`. -/
theorem representedBaseMapU_square :
    (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage ≫
        representedOpensStructureMap B S hS T₁ =
      representedBaseMapU B S hS h ≫
        ((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage :=
  Adjunction.homEquiv_symm_comp_eq_homEquiv_symm_comp
    (commRingImageAdjunction
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom)
    (restrictionCommRingNatIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₂))
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      (Opens.map ((BigFppfOver.toScheme B S hS).map h).base))
    (representedBaseSharp_comp_fSharpInverseImage_eq B S hS h).symm

/-! ### The square with sections lifted to `u + 1` -/

/-- **The canonical map `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` of the proof of Stacks 08VF**, all
sections lifted to `CommRingCat.{u + 1}`: the transpose under `ε_X⁻¹ ⊣ ε_{X,*}` of the lift of
`AlgebraicGeometry.Space.representedBaseMapU`.  The source is `ε_X⁻¹` of the lift of the base
sheaf `f₀⁻¹𝒪_{Y₀}` of Definition 08T2 (`AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom`),
the target is the base sheaf of `AlgebraicGeometry.Space.cotangentComplex`; it is built from
adjunction units and structure maps only, see the module docstring. -/
noncomputable def representedBaseMap :
    (representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor
            (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O)) ⟶
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
        ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toToposHom.inverseImageRing.obj
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O) :=
  ((commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T₁)).homEquiv _ _).symm
    ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        SheafOfModules.commRingCatULift.{u, u + 1}).map (representedBaseMapU B S hS h) ≫
      (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedOpensToSmallEtale B S hS T₁)
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS (yoneda.obj T₁))).obj
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toToposHom).obj
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj T₂, isAlgebraicSpace_yoneda B S hS T₂⟩).O))).inv)

/-- The square of `AlgebraicGeometry.Space.representedBaseMapU_square` with sections lifted to
`u + 1`, in restriction form. -/
theorem representedBaseMapU_square_lift :
    (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        SheafOfModules.commRingCatULift.{u, u + 1}).map
        (Scheme.Hom.zariskiRingedToposHom
          ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage ≫
      representedZariskiSharp B S hS T₁ =
    (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        SheafOfModules.commRingCatULift.{u, u + 1}).map (representedBaseMapU B S hS h) ≫
      ((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
        (SmallEtale.topology B S hS (yoneda.obj T₁))).map
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage) :=
  ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map_comp
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage
      (representedOpensStructureMap B S hS T₁)).symm.trans
    ((congrArg (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map (representedBaseMapU_square B S hS h)).trans
    ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map_comp (representedBaseMapU B S hS h)
      (((representedOpensToSmallEtale B S hS T₁).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage)))

/-- **The square of the proof of Stacks 08VF.**  The canonical map
`AlgebraicGeometry.Space.representedBaseMap : ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ f_small⁻¹𝒪_Y` is compatible with
`ε♯ : ε⁻¹𝒪_{X₀} ⟶ 𝒪_X`: `ε⁻¹` of the structure map `f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_{X₀}` of Definition 08T2
followed by `ε♯` is `representedBaseMap` followed by the structure map
`f_small⁻¹𝒪_Y ⟶ 𝒪_X` of `AlgebraicGeometry.Space.cotangentComplex`, all sections lifted to
`CommRingCat.{u + 1}`.  This is the commutative diagram of Remark 08GH read on structure
sheaves. -/
theorem representedBaseMap_square :
    (representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.map
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).map
          (Scheme.Hom.zariskiRingedToposHom
            ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage) ≫
        (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage =
      representedBaseMap B S hS h ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS (yoneda.obj T₁))).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).fSharpInverseImage :=
  Adjunction.map_comp_homEquiv_symm_eq_homEquiv_symm_comp
    (commRingImageAdjunction.{u + 1, u + 1, u, u + 1, u, u}
      (representedToZariskiMorphismOfTopoi B S hS T₁))
    (restrictionCommRingNatIso.{u + 1, u, u, u, u + 1}
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedOpensToSmallEtale B S hS T₁))
    (representedBaseMapU_square_lift B S hS h)

end Square

end AlgebraicGeometry.Space

end
