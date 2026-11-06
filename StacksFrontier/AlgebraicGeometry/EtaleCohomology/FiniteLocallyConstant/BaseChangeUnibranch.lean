module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageTrivializationSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback compatibility of the unibranch dictionary

Stacks Tag 0DV6 asserts that the equivalences of Tags 0DV5 and 0GIY are compatible with
pullbacks: for a morphism `f : Y → X` and a geometric point `y` of `Y` with image `x = f(y)`, the
square

```
  finite type loc. const. Λ-module sheaves on X_étale  ──→  finite Λ-π₁(X, x)-modules
                      │                                               │
                   f^{-1}                                        restriction
                      ↓                                               ↓
  finite type loc. const. Λ-module sheaves on Y_étale  ──→  finite Λ-π₁(Y, y)-modules
```

commutes, the right-hand vertical arrow restricting the action along the homomorphism
`π₁(Y, y) → π₁(X, x)` induced by `f` (Tag 0BND (3)). The squares belonging to Tag 0DV5 are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite`; this
file supplies the square belonging to Tag 0GIY, for irreducible geometrically unibranch `X` and
`Y`, an arbitrary morphism `f` and an arbitrary ring `Λ`.

Tag 0GIY is `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleUniv`, whose functor
sends a sheaf `F` to its monodromy module `colim_{(A, a)} F(A)` over the pointed Galois covers of
the base (`AlgebraicGeometry.monodromyModule`). The square is proved for that functor directly.

## Main definitions

* `AlgebraicGeometry.monodromyBaseChangeMap` — for presheaves `F` on `X_étale` and `G` on
  `Y_étale` and a map `θ : F ⟶ f_* G`, the comparison `colim_A F(A) ⟶ colim_B G(B)` of monodromy
  objects. A section over a pointed Galois cover `A` of `X` is carried by `θ` to the base change
  `A ×_X Y` and restricted to a pointed Galois cover of `Y` dominating it; the choice of that cover
  does not matter (`AlgebraicGeometry.map_comp_colimit_ι_monodromyDiagram_eq`).
* `AlgebraicGeometry.etaleFiniteTypeLocallyConstantModulePullback` — inverse image on the finite
  type locally constant sheaves of `Λ`-modules on Mathlib's small étale sites.
* `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleUnivPullbackIso` — **Stacks
  Tag 0DV6 for the equivalence of Tag 0GIY**.

## Main results

* `AlgebraicGeometry.comp_finiteEtaleBaseChange_map_galoisAutHom` — the automorphisms `τ_A(σ)` of
  pointed Galois covers are compatible with base change along `f` and the homomorphism of
  fundamental groups; this is the commutative diagram of Tag 0BND which the source cites.
* `AlgebraicGeometry.monodromyBaseChangeMap_comm` and
  `AlgebraicGeometry.monodromyBaseChangeMap_naturality` — the comparison is equivariant and
  natural.
* `AlgebraicGeometry.bijective_monodromyBaseChangeMap_unit` — for `θ` the unit of
  `f^{-1} ⊣ f_*` and `F` trivialized by a pointed Galois cover `A`, the comparison is bijective.
  The trivialization of `F` over `A` is carried to one of `f^{-1}F` over `A ×_X Y` compatibly with
  sections (`Stacks.ConstantSheaf.toSheafify_comp_constantIsoOverPullbackSheafPullback_hom_app`),
  and sections of a sheaf constant on an irreducible étale scheme are the constants.
* `AlgebraicGeometry.isFiniteTypeLocallyConstant_etaleModuleInverseImage` — Tag 093R on Mathlib's
  small étale site for module coefficients.

## Implementation notes

The source proves Tag 0DV6 for sheaves of sets from the commutative diagram of Tag 0BND relating
the fibre functors, and says "a similar result holds for the other cases". For Tag 0GIY the
equivalence is the monodromy functor, so the square is a statement about sections over pointed
Galois covers; the diagram of Tag 0BND enters through
`AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection`.

The component of `θ` at a finite étale cover is named
(`AlgebraicGeometry.baseChangeSectionsMap`) so that its codomain is syntactically the sections of
`G` over the base change; the base change of finite étale covers and of étale schemes agree only
definitionally, and rewriting fails across that.

## References

* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r

namespace AlgebraicGeometry

section Comparison

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] (f : Y ⟶ X)
  (y : GeometricPoint Y)

/-- A pointed Galois cover of `X` at `f(y)` is dominated, after base change to `Y`, by a pointed
Galois cover of `Y` at `y`. -/
public theorem exists_pointedGaloisCover_hom_finiteEtaleBaseChange
    (A : PointedGaloisCover (y.map f)) :
    ∃ (B : PointedGaloisCover y) (g : B.obj ⟶ (finiteEtaleBaseChange f).obj A.obj),
      (finiteEtaleFiberFunctor y).map g B.basePt =
        (finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt := by
  obtain ⟨B, g, b, hB, hg⟩ := exists_hom_from_galois_of_fiber (finiteEtaleFiberFintypeFunctor Y y)
    ((finiteEtaleBaseChange f).obj A.obj)
    ((finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt)
  exact ⟨⟨B, b, hB⟩, g, hg⟩

/-- The pointed Galois cover of `Y` chosen to dominate the base change of a pointed Galois cover
of `X`. -/
public def baseChangePointedGaloisCover (A : PointedGaloisCover (y.map f)) :
    PointedGaloisCover y :=
  (exists_pointedGaloisCover_hom_finiteEtaleBaseChange f y A).choose

/-- The morphism from `baseChangePointedGaloisCover f y A` to the base change of `A`. -/
public def baseChangePointedGaloisCoverHom (A : PointedGaloisCover (y.map f)) :
    (baseChangePointedGaloisCover f y A).obj ⟶ (finiteEtaleBaseChange f).obj A.obj :=
  (exists_pointedGaloisCover_hom_finiteEtaleBaseChange f y A).choose_spec.choose

/-- The morphism `baseChangePointedGaloisCoverHom f y A` is pointed. -/
public theorem baseChangePointedGaloisCoverHom_basePt (A : PointedGaloisCover (y.map f)) :
    (finiteEtaleFiberFunctor y).map (baseChangePointedGaloisCoverHom f y A)
        (baseChangePointedGaloisCover f y A).basePt =
      (finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt :=
  (exists_pointedGaloisCover_hom_finiteEtaleBaseChange f y A).choose_spec.choose_spec

variable {y} in
/-- **Two pointed morphisms from pointed Galois covers to a finite étale cover induce the same map
into the monodromy object.** They agree on a pointed Galois cover dominating both, the source
being connected. -/
public theorem map_comp_colimit_ι_monodromyDiagram_eq {C : Type*} [Category* C]
    [HasColimitsOfShape (PointedGaloisCover y)ᵒᵖ C] (G : (Y.Etale)ᵒᵖ ⥤ C)
    {Z : FiniteEtaleOver Y} {B₁ B₂ : PointedGaloisCover y} (k₁ : B₁.obj ⟶ Z) (k₂ : B₂.obj ⟶ Z)
    (h : (finiteEtaleFiberFunctor y).map k₁ B₁.basePt =
      (finiteEtaleFiberFunctor y).map k₂ B₂.basePt) :
    G.map ((finiteEtaleToEtale Y).map k₁).op ≫ colimit.ι ((monodromyDiagram y).obj G) (op B₁) =
      G.map ((finiteEtaleToEtale Y).map k₂).op ≫
        colimit.ι ((monodromyDiagram y).obj G) (op B₂) := by
  let m₁ := IsCofiltered.minToLeft B₁ B₂
  let m₂ := IsCofiltered.minToRight B₁ B₂
  have hm : m₁.val ≫ k₁ = m₂.val ≫ k₂ := by
    apply evaluation_injective_of_isConnected (finiteEtaleFiberFintypeFunctor Y y)
      (IsCofiltered.min B₁ B₂).obj Z (IsCofiltered.min B₁ B₂).pt
    have h₁ := m₁.comp
    have h₂ := m₂.comp
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, h₁, h₂]
    exact h
  rw [← colimit.w ((monodromyDiagram y).obj G) m₁.op,
    ← colimit.w ((monodromyDiagram y).obj G) m₂.op]
  show G.map _ ≫ G.map ((finiteEtaleToEtale Y).map m₁.val).op ≫ _ =
    G.map _ ≫ G.map ((finiteEtaleToEtale Y).map m₂.val).op ≫ _
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, ← op_comp, ← op_comp, ← Functor.map_comp,
    ← Functor.map_comp, hm]

omit [ConnectedSpace X] [ConnectedSpace Y] in
/-- The inverse of the fibre projection is natural: base change of a morphism of finite étale
covers of `X` acts on the lifts of `y` as the morphism acts on the lifts of `f(y)`. -/
public theorem finiteEtaleFiberFunctor_map_finiteEtaleBaseChange_projectionEquiv_symm
    {V W : FiniteEtaleOver X} (φ : V ⟶ W) (p : (finiteEtaleFiberFunctor (y.map f)).obj V) :
    (finiteEtaleFiberFunctor y).map ((finiteEtaleBaseChange f).map φ)
        ((finiteEtaleFiberProjectionEquiv f y V).symm p) =
      (finiteEtaleFiberProjectionEquiv f y W).symm
        ((finiteEtaleFiberFunctor (y.map f)).map φ p) := by
  apply (finiteEtaleFiberProjectionEquiv f y W).injective
  rw [Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom ((finiteEtaleFiberProjectionIso f y).hom.naturality φ)
    ((finiteEtaleFiberProjectionEquiv f y V).symm p)
  refine h.trans ?_
  show (finiteEtaleFiberFunctor (y.map f)).map φ
    ((finiteEtaleFiberProjectionEquiv f y V) ((finiteEtaleFiberProjectionEquiv f y V).symm p)) = _
  rw [Equiv.apply_symm_apply]

/-- **The automorphisms `τ(σ)` are compatible with base change**: a pointed morphism from a
pointed Galois cover `B` of `Y` to the base change of a pointed Galois cover `A` of `X`
intertwines `τ_B(σ)` with the base change of `τ_A(f_*σ)`, where `f_*` is the homomorphism of
Tag 0BND (3). -/
public theorem comp_finiteEtaleBaseChange_map_galoisAutHom (A : PointedGaloisCover (y.map f))
    (B : PointedGaloisCover y) (g : B.obj ⟶ (finiteEtaleBaseChange f).obj A.obj)
    (hg : (finiteEtaleFiberFunctor y).map g B.basePt =
      (finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt)
    (σ : EtaleFundamentalGroup Y y) :
    g ≫ (finiteEtaleBaseChange f).map
        (galoisAutHom (y.map f) (etaleFundamentalGroupMap f y σ) A) =
      galoisAutHom y σ B ≫ g := by
  apply evaluation_injective_of_isConnected (finiteEtaleFiberFintypeFunctor Y y) B.obj _ B.pt
  show (finiteEtaleFiberFunctor y).map (g ≫ (finiteEtaleBaseChange f).map
      (galoisAutHom (y.map f) (etaleFundamentalGroupMap f y σ) A)) B.basePt =
    (finiteEtaleFiberFunctor y).map (galoisAutHom y σ B ≫ g) B.basePt
  have h1 : (finiteEtaleFiberFunctor y).map (galoisAutHom y σ B) B.basePt = σ • B.basePt :=
    galoisAutHom_pt y σ B
  have h2 : (finiteEtaleFiberFunctor (y.map f)).map
      (galoisAutHom (y.map f) (etaleFundamentalGroupMap f y σ) A) A.basePt =
        etaleFundamentalGroupMap f y σ • A.basePt :=
    galoisAutHom_pt (y.map f) (etaleFundamentalGroupMap f y σ) A
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [hg, h1, finiteEtaleFiberFunctor_map_finiteEtaleBaseChange_projectionEquiv_symm, h2]
  have hnat : (finiteEtaleFiberFunctor y).map g (σ • B.basePt) =
      σ • (finiteEtaleFiberFunctor y).map g B.basePt :=
    (ConcreteCategory.congr_hom (σ.asIso.hom.naturality g) B.basePt).symm
  rw [hnat, hg]
  apply (finiteEtaleFiberProjectionEquiv f y A.obj).injective
  rw [Equiv.apply_symm_apply]
  refine ((etaleFundamentalGroupMap_finiteEtaleFiberProjection f y A.obj σ
    ((finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt)).trans ?_).symm
  show ((etaleFundamentalGroupMap f y σ).asIso.app A.obj).hom
    ((finiteEtaleFiberProjectionEquiv f y A.obj) ((finiteEtaleFiberProjectionEquiv f y A.obj).symm
      A.basePt)) = _
  rw [Equiv.apply_symm_apply]
  rfl

section Map

variable {C : Type*} [Category* C] [HasColimitsOfShape (PointedGaloisCover y)ᵒᵖ C]
  (F : (X.Etale)ᵒᵖ ⥤ C) (G : (Y.Etale)ᵒᵖ ⥤ C)
  (θ : F ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange f).op ⋙ G)

/-- The component of `θ : F ⟶ f_* G` at a finite étale cover `V` of `X`, read as a map to the
sections of `G` over the base change of `V`. -/
public def baseChangeSectionsMap (V : FiniteEtaleOver X) :
    F.obj (op ((finiteEtaleToEtale X).obj V)) ⟶
      G.obj (op ((finiteEtaleToEtale Y).obj ((finiteEtaleBaseChange f).obj V))) :=
  θ.app (op ((finiteEtaleToEtale X).obj V))

omit [ConnectedSpace X] [ConnectedSpace Y] in
/-- The naturality of `θ : F ⟶ f_* G` along a morphism of finite étale covers of `X`, read with
the base change of finite étale covers. -/
@[reassoc]
public theorem map_comp_baseChangeSectionsMap {V W : FiniteEtaleOver X} (φ : V ⟶ W) :
    F.map ((finiteEtaleToEtale X).map φ).op ≫ baseChangeSectionsMap f F G θ V =
      baseChangeSectionsMap f F G θ W ≫
        G.map ((finiteEtaleToEtale Y).map ((finiteEtaleBaseChange f).map φ)).op :=
  θ.naturality _

omit [ConnectedSpace Y] in
/-- Restriction along two composable morphisms of finite étale covers of `Y`. -/
@[reassoc]
public theorem map_finiteEtaleToEtale_comp {V W Z : FiniteEtaleOver Y} (a : V ⟶ W) (b : W ⟶ Z) :
    G.map ((finiteEtaleToEtale Y).map b).op ≫ G.map ((finiteEtaleToEtale Y).map a).op =
      G.map ((finiteEtaleToEtale Y).map (a ≫ b)).op := by
  rw [Functor.map_comp, op_comp, G.map_comp]

/-- The compatibility of the legs of `AlgebraicGeometry.monodromyBaseChangeCocone` with a morphism
of pointed Galois covers of `X`. -/
public theorem monodromyBaseChangeCocone_naturality_aux (A₁ A₂ : PointedGaloisCover (y.map f))
    (h : A₂ ⟶ A₁) :
    F.map ((finiteEtaleToEtale X).map h.val).op ≫
        baseChangeSectionsMap f F G θ A₂.obj ≫
          G.map ((finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A₂)).op ≫
            colimit.ι ((monodromyDiagram y).obj G) (op (baseChangePointedGaloisCover f y A₂)) =
      baseChangeSectionsMap f F G θ A₁.obj ≫
        G.map ((finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A₁)).op ≫
          colimit.ι ((monodromyDiagram y).obj G) (op (baseChangePointedGaloisCover f y A₁)) := by
  rw [map_comp_baseChangeSectionsMap_assoc f F G θ h.val,
    map_finiteEtaleToEtale_comp_assoc G (baseChangePointedGaloisCoverHom f y A₂)
      ((finiteEtaleBaseChange f).map h.val)]
  congr 1
  apply map_comp_colimit_ι_monodromyDiagram_eq
  have hh : (finiteEtaleFiberFunctor (y.map f)).map h.val A₂.basePt = A₁.basePt := h.comp
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [baseChangePointedGaloisCoverHom_basePt, baseChangePointedGaloisCoverHom_basePt,
    finiteEtaleFiberFunctor_map_finiteEtaleBaseChange_projectionEquiv_symm, hh]

/-- **The comparison of monodromy objects along `f`**, as a cocone: a section of `F` over a pointed
Galois cover `A` of `X` is carried by `θ` to a section of `G` over the base change of `A`, which is
restricted to the chosen pointed Galois cover of `Y` dominating it. -/
public def monodromyBaseChangeCocone : Cocone ((monodromyDiagram (y.map f)).obj F) where
  pt := colimit ((monodromyDiagram y).obj G)
  ι :=
    { app A := baseChangeSectionsMap f F G θ A.unop.obj ≫
        G.map ((finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A.unop)).op ≫
          colimit.ι ((monodromyDiagram y).obj G) (op (baseChangePointedGaloisCover f y A.unop))
      naturality {A₁ A₂} h :=
        (monodromyBaseChangeCocone_naturality_aux f y F G θ A₁.unop A₂.unop h.unop).trans
          (Category.comp_id _).symm }

variable [HasColimitsOfShape (PointedGaloisCover (y.map f))ᵒᵖ C]

/-- **The comparison map of monodromy objects along `f`**, from the monodromy object of `F` at
`f(y)` to that of `G` at `y`, induced by `θ : F ⟶ f_* G`. -/
public def monodromyBaseChangeMap :
    colimit ((monodromyDiagram (y.map f)).obj F) ⟶ colimit ((monodromyDiagram y).obj G) :=
  colimit.desc _ (monodromyBaseChangeCocone f y F G θ)

/-- On the image of a section over a pointed Galois cover `A`, the comparison map is `θ` followed
by restriction along any pointed morphism from a pointed Galois cover of `Y` to the base change
of `A`. -/
@[reassoc]
public theorem ι_monodromyBaseChangeMap (A : PointedGaloisCover (y.map f))
    (B : PointedGaloisCover y) (g : B.obj ⟶ (finiteEtaleBaseChange f).obj A.obj)
    (hg : (finiteEtaleFiberFunctor y).map g B.basePt =
      (finiteEtaleFiberProjectionEquiv f y A.obj).symm A.basePt) :
    colimit.ι ((monodromyDiagram (y.map f)).obj F) (op A) ≫ monodromyBaseChangeMap f y F G θ =
      baseChangeSectionsMap f F G θ A.obj ≫
        G.map ((finiteEtaleToEtale Y).map g).op ≫
          colimit.ι ((monodromyDiagram y).obj G) (op B) := by
  refine (colimit.ι_desc (monodromyBaseChangeCocone f y F G θ) (op A)).trans ?_
  show baseChangeSectionsMap f F G θ A.obj ≫ _ = _
  congr 1
  apply map_comp_colimit_ι_monodromyDiagram_eq
  rw [baseChangePointedGaloisCoverHom_basePt, hg]

/-- `AlgebraicGeometry.ι_monodromyBaseChangeMap` for the chosen pointed Galois cover of `Y`. -/
private theorem ι_monodromyBaseChangeMap_baseChangePointedGaloisCover
    (A : PointedGaloisCover (y.map f)) :
    colimit.ι ((monodromyDiagram (y.map f)).obj F) (op A) ≫ monodromyBaseChangeMap f y F G θ =
      baseChangeSectionsMap f F G θ A.obj ≫
        G.map ((finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A)).op ≫
          colimit.ι ((monodromyDiagram y).obj G) (op (baseChangePointedGaloisCover f y A)) :=
  ι_monodromyBaseChangeMap f y F G θ A _ _ (baseChangePointedGaloisCoverHom_basePt f y A)

/-- **The comparison map intertwines the actions**, the action of `π₁(Y, y)` on the target with
that of `π₁(X, f(y))` on the source through the homomorphism of Tag 0BND (3). The actions are
written as the maps of colimits underlying `AlgebraicGeometry.monodromyAction`. -/
public theorem monodromyBaseChangeMap_comm (σ : EtaleFundamentalGroup Y y) :
    colimMap ((monodromyDiagramAut (y.map f) (etaleFundamentalGroupMap f y σ)).app F) ≫
        monodromyBaseChangeMap f y F G θ =
      monodromyBaseChangeMap f y F G θ ≫ colimMap ((monodromyDiagramAut y σ).app G) := by
  refine colimit.hom_ext fun A => ?_
  rw [ι_colimMap_assoc, ι_monodromyBaseChangeMap_baseChangePointedGaloisCover,
    reassoc_of% (ι_monodromyBaseChangeMap_baseChangePointedGaloisCover f y F G θ A.unop),
    ι_colimMap, monodromyDiagramAut_app_app, monodromyDiagramAut_app_app]
  show F.map ((finiteEtaleToEtale X).map _).op ≫ baseChangeSectionsMap f F G θ A.unop.obj ≫ _ = _
  rw [map_comp_baseChangeSectionsMap_assoc, map_finiteEtaleToEtale_comp_assoc,
    comp_finiteEtaleBaseChange_map_galoisAutHom f y A.unop _ _
      (baseChangePointedGaloisCoverHom_basePt f y A.unop) σ,
    ← map_finiteEtaleToEtale_comp_assoc]

variable {F G θ} in
/-- **The comparison map is natural** in the presheaves and the map `θ`. -/
public theorem monodromyBaseChangeMap_naturality {F' : (X.Etale)ᵒᵖ ⥤ C} {G' : (Y.Etale)ᵒᵖ ⥤ C}
    {θ' : F' ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange f).op ⋙ G'} (α : F ⟶ F')
    (β : G ⟶ G') (h : θ ≫ Functor.whiskerLeft _ β = α ≫ θ') :
    colimMap ((monodromyDiagram (y.map f)).map α) ≫ monodromyBaseChangeMap f y F' G' θ' =
      monodromyBaseChangeMap f y F G θ ≫ colimMap ((monodromyDiagram y).map β) := by
  refine colimit.hom_ext fun A => ?_
  rw [ι_colimMap_assoc, ι_monodromyBaseChangeMap f y F' G' θ' A.unop _ _
    (baseChangePointedGaloisCoverHom_basePt f y A.unop),
    ι_monodromyBaseChangeMap_assoc f y F G θ A.unop _ _
      (baseChangePointedGaloisCoverHom_basePt f y A.unop), ι_colimMap]
  have h1 : baseChangeSectionsMap f F G θ A.unop.obj ≫
      β.app (op ((finiteEtaleToEtale Y).obj ((finiteEtaleBaseChange f).obj A.unop.obj))) =
      α.app _ ≫ baseChangeSectionsMap f F' G' θ' A.unop.obj :=
    congrArg (fun φ => φ.app (op ((finiteEtaleToEtale X).obj A.unop.obj))) h
  show α.app _ ≫ baseChangeSectionsMap f F' G' θ' A.unop.obj ≫ _ =
    baseChangeSectionsMap f F G θ A.unop.obj ≫ G.map _ ≫ β.app _ ≫ _
  rw [← reassoc_of% h1, β.naturality_assoc]

end Map

end Comparison

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- The slice of small étale base change at an étale scheme is continuous: base change is left
exact and carries coverings to coverings. -/
public instance isContinuous_overPost_smallEtaleBaseChange {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X)
    (U : X.Etale) :
    (Over.post (X := U) (smallEtaleBaseChange f)).IsContinuous (X.smallEtaleTopology.over U)
      (Y.smallEtaleTopology.over ((smallEtaleBaseChange f).obj U)) :=
  Stacks.ConstantSheaf.isContinuous_overPost _ _ _ (CoverPreserving.of_isContinuous _ _ _) U

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

section Bijective

open Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
  (hX : IsGeometricallyUnibranch X) (hY : IsGeometricallyUnibranch Y) (f : Y ⟶ X)
  (y : GeometricPoint Y) {Λ : Type r} [Ring Λ]

include hX hY in
/-- For a sheaf trivialized by a pointed Galois cover `A`, the unit of the inverse image followed
by restriction to the base-changed pointed Galois cover is bijective on sections. -/
private theorem bijective_unit_app_comp_map_baseChangePointedGaloisCoverHom
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    {A : PointedGaloisCover (y.map f)} {M : ModuleCat.{max (u + 1) r} Λ}
    (e : GaloisTrivialization A F M) :
    Function.Bijective (((etaleModuleInverseImageAdj Λ f).unit.app F).hom.app
        (op ((finiteEtaleToEtale X).obj A.obj)) ≫
      ((etaleModuleInverseImage Λ f).obj F).obj.map
        ((finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A)).op) := by
  let G := (etaleModuleInverseImage Λ f).obj F
  let B := baseChangePointedGaloisCover f y A
  let U := (finiteEtaleToEtale X).obj A.obj
  let c' := Stacks.ConstantSheaf.constantIsoOverPullbackSheafPullback X.smallEtaleTopology
    Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (Stacks.EtaleCohomology.smallEtaleBaseChange f) U F M e
  have hU3 := Stacks.ConstantSheaf.toSheafify_comp_constantIsoOverPullbackSheafPullback_hom_app
    X.smallEtaleTopology Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (Stacks.EtaleCohomology.smallEtaleBaseChange f) U F M e
  let g' : (finiteEtaleToEtale Y).obj B.obj ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange f).obj U :=
    (finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A)
  let V : Over ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj U) := Over.mk g'
  let m : V ⟶ Over.mk (𝟙 _) := Over.homMk g' (Category.comp_id _)
  have : IrreducibleSpace V.left.left := B.irreducibleSpace hY
  let K' := Y.smallEtaleTopology.over ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj U)
  have h1 : Function.Bijective ((toSheafify K' ((Functor.const _).obj M)).app (op V) ≫
      c'.hom.hom.app (op V)) :=
    ((ConcreteCategory.isIso_iff_bijective (c'.hom.hom.app (op V))).1 inferInstance).comp
      (bijective_toSheafify_over_const_app Λ M V)
  have n1 : (toSheafify K' ((Functor.const _).obj M)).app (op (Over.mk (𝟙 _))) ≫
      ((constantSheaf K' (ModuleCat.{max (u + 1) r} Λ)).obj M).obj.map m.op =
      (toSheafify K' ((Functor.const _).obj M)).app (op V) :=
    ((toSheafify K' ((Functor.const _).obj M)).naturality m.op).symm.trans (Category.id_comp _)
  have n2 : ((constantSheaf K' (ModuleCat.{max (u + 1) r} Λ)).obj M).obj.map m.op ≫
      c'.hom.hom.app (op V) =
      c'.hom.hom.app (op (Over.mk (𝟙 _))) ≫ G.obj.map g'.op :=
    c'.hom.hom.naturality m.op
  have hψ' : (toSheafify K' ((Functor.const _).obj M)).app (op V) ≫ c'.hom.hom.app (op V) =
      ((toSheafify (X.smallEtaleTopology.over U) ((Functor.const _).obj M)).app
          (op (Over.mk (𝟙 U))) ≫ e.hom.hom.app (op (Over.mk (𝟙 U)))) ≫
        (((etaleModuleInverseImageAdj Λ f).unit.app F).hom.app (op U) ≫ G.obj.map g'.op) := by
    refine (congrArg (· ≫ c'.hom.hom.app (op V)) n1.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) n2).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ G.obj.map g'.op) hU3).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans
      (Category.assoc _ _ _).symm
  rw [hψ'] at h1
  exact (Function.Bijective.of_comp_iff _ (e.bijective_sections hX)).1 h1

include hX hY in
/-- **For a sheaf trivialized by a pointed Galois cover, the comparison of monodromy modules along
`f` is bijective.** -/
public theorem bijective_monodromyBaseChangeMap_unit
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    {A : PointedGaloisCover (y.map f)} {M : ModuleCat.{max (u + 1) r} Λ}
    (e : GaloisTrivialization A F M) :
    Function.Bijective (monodromyBaseChangeMap f y F.obj ((etaleModuleInverseImage Λ f).obj F).obj
      ((etaleModuleInverseImageAdj Λ f).unit.app F).hom) := by
  let G := (etaleModuleInverseImage Λ f).obj F
  let B := baseChangePointedGaloisCover f y A
  let U := (finiteEtaleToEtale X).obj A.obj
  let g' : (finiteEtaleToEtale Y).obj B.obj ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange f).obj U :=
    (finiteEtaleToEtale Y).map (baseChangePointedGaloisCoverHom f y A)
  let eB : GaloisTrivialization B G M :=
    Stacks.ConstantSheaf.constantIsoOverPullbackOfMap Y.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) g' G M
      (Stacks.ConstantSheaf.constantIsoOverPullbackSheafPullback X.smallEtaleTopology
        Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
        (Stacks.EtaleCohomology.smallEtaleBaseChange f) U F M e)
  have hfun : ⇑(ConcreteCategory.hom (monodromyBaseChangeMap f y F.obj G.obj
        ((etaleModuleInverseImageAdj Λ f).unit.app F).hom)) ∘
      ⇑(ConcreteCategory.hom (colimit.ι ((monodromyDiagram (y.map f)).obj F.obj) (op A))) =
      ⇑(ConcreteCategory.hom (colimit.ι ((monodromyDiagram y).obj G.obj) (op B))) ∘
        ⇑(ConcreteCategory.hom (((etaleModuleInverseImageAdj Λ f).unit.app F).hom.app (op U) ≫
          G.obj.map g'.op)) :=
    funext (ConcreteCategory.congr_hom (ι_monodromyBaseChangeMap_baseChangePointedGaloisCover f y
      F.obj G.obj ((etaleModuleInverseImageAdj Λ f).unit.app F).hom A))
  refine (Function.Bijective.of_comp_iff _ (bijective_colimit_ι_monodromyDiagram hX e)).1 ?_
  rw [hfun]
  exact (bijective_colimit_ι_monodromyDiagram hY eB).comp
    (bijective_unit_app_comp_map_baseChangePointedGaloisCoverHom hX hY f y e)

end Bijective

section Square

open Stacks.EtaleCohomology Stacks.ConstantSheaf Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (Λ : Type r) [Ring Λ]

/-- **Tag 093R for sheaves of `Λ`-modules on Mathlib's small étale site.** The inverse image of a
finite type locally constant sheaf of `Λ`-modules along a morphism of schemes is finite type
locally constant. -/
public theorem isFiniteTypeLocallyConstant_etaleModuleInverseImage
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F) :
    IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology ((etaleModuleInverseImage Λ f).obj F) :=
  isFiniteTypeLocallyConstant_sheafPullback X.smallEtaleTopology Y.smallEtaleTopology Λ
    (Stacks.EtaleCohomology.smallEtaleBaseChange f) (CoverPreserving.of_isContinuous _ _ _) F hF

/-- **Inverse image on the finite type locally constant sheaves of `Λ`-modules** on Mathlib's
small étale sites, for an arbitrary ring `Λ`: the left-hand vertical arrow of the square of
Tag 0DV6 for Tag 0GIY. -/
public def etaleFiniteTypeLocallyConstantModulePullback :
    FiniteTypeLocallyConstantModuleCategory.{max (u + 1) r, u + 1, u, r} Λ X.smallEtaleTopology ⥤
      FiniteTypeLocallyConstantModuleCategory.{max (u + 1) r, u + 1, u, r} Λ
        Y.smallEtaleTopology :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ etaleModuleInverseImage Λ f)
    fun F ↦ isFiniteTypeLocallyConstant_etaleModuleInverseImage f Λ F.obj F.property

/-- Inverse image on the finite type locally constant sheaves is inverse image of sheaves of
`Λ`-modules. -/
public theorem etaleFiniteTypeLocallyConstantModulePullback_comp_ι :
    etaleFiniteTypeLocallyConstantModulePullback f Λ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ etaleModuleInverseImage Λ f := rfl

variable [IrreducibleSpace X] [IrreducibleSpace Y] (hX : IsGeometricallyUnibranch X)
  (hY : IsGeometricallyUnibranch Y) (y : GeometricPoint Y)

include hX hY in
/-- The comparison of monodromy modules along `f` is an isomorphism on the finite type locally
constant sheaves. -/
public theorem isIso_monodromyBaseChangeMap_unit
    (F : FiniteTypeLocallyConstantModuleCategory.{max (u + 1) r, u + 1, u, r} Λ
      X.smallEtaleTopology) :
    IsIso (monodromyBaseChangeMap f y F.obj.obj ((etaleModuleInverseImage Λ f).obj F.obj).obj
      ((etaleModuleInverseImageAdj Λ f).unit.app F.obj).hom) := by
  obtain ⟨A, M, -, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hX (y.map f) Λ F.obj F.property
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_monodromyBaseChangeMap_unit hX hY f y e)

include hX hY in
/-- **Stacks Project, Tag 0DV6, for the equivalence of Tag 0GIY.** Let `f : Y ⟶ X` be a morphism
of irreducible, geometrically unibranch schemes, let `y` be a geometric point of `Y` and let `Λ`
be a ring. The equivalences of Tag 0GIY for `X` at `f(y)` and for `Y` at `y` are compatible with
pullback: the square

```
  finite type loc. const. Λ-module sheaves on X_étale  ──→  finite Λ-π₁(X, f(y))-modules
                      │                                               │
                   f^{-1}                                        restriction
                      ↓                                               ↓
  finite type loc. const. Λ-module sheaves on Y_étale  ──→  finite Λ-π₁(Y, y)-modules
```

commutes up to the natural isomorphism given here, the right-hand vertical arrow restricting the
action along the homomorphism `π₁(Y, y) ⟶ π₁(X, f(y))` of Tag 0BND (3).

The comparison sends the image of a section `s` over a pointed Galois cover `A` of `X` to the
image of the restriction of `f^{-1}s` to a pointed Galois cover of `Y` dominating `A ×_X Y`; it is
bijective because `f^{-1}` carries a trivialization of `F` over `A` to one of `f^{-1}F` over
`A ×_X Y`, compatibly with the sections. -/
@[stacks 0DV6 "the square for the equivalence of Stacks 0GIY; the squares for the equivalences of \
Stacks 0DV5 are in BaseChangeRepresentable and BaseChangeEtaleSite"]
public def finiteTypeLocallyConstantEquivContinuousModuleUnivPullbackIso :
    (finiteTypeLocallyConstantEquivContinuousModuleUniv X hX (y.map f) Λ).functor ⋙
        finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f y) ≅
      etaleFiniteTypeLocallyConstantModulePullback f Λ ⋙
        (finiteTypeLocallyConstantEquivContinuousModuleUniv Y hY y Λ).functor :=
  NatIso.ofComponents
    (fun F ↦
      ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
        (Action.mkIso (@asIso _ _ _ _ (monodromyBaseChangeMap f y F.obj.obj
          ((etaleModuleInverseImage Λ f).obj F.obj).obj
          ((etaleModuleInverseImageAdj Λ f).unit.app F.obj).hom)
            (isIso_monodromyBaseChangeMap_unit f Λ hX hY y F))
          (fun σ ↦ monodromyBaseChangeMap_comm f y _ _ _ σ)))))
    (fun {F F'} α ↦ by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact monodromyBaseChangeMap_naturality f y α.hom.hom
        ((etaleModuleInverseImage Λ f).map α.hom).hom
        (congrArg (fun φ => φ.hom) ((etaleModuleInverseImageAdj Λ f).unit.naturality α.hom)).symm)

end Square

end AlgebraicGeometry
