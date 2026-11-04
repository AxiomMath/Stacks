module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Homology.DerivedIndexing.CompositeUnitSingle
public import StacksFrontier.Homology.DerivedIndexing.CoEdgeDelta
public import StacksFrontier.Homology.DerivedIndexing.BaseChangeDelta
public import StacksFrontier.Homology.DerivedIndexing.NatTransCommShift
public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift
public import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle

/-!
# The base change map on higher direct images

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes. For an `𝒪_X`-module `F` there is a canonical base change map
`g^* R^q f_* F ⟶ R^q f'_* (g')^* F`, adjoint to

`R^q f_* F ⟶ R^q f_*(g'_* g'^* F) ⟶ R^q (f ∘ g')_* (g'^* F) = R^q (g ∘ f')_* (g'^* F)`,

the first map induced by the unit of `g'^* ⊣ g'_*`, the second the edge map of the composite
`f ∘ g'` (an isomorphism of right derived functors on `D⁺`, as `g'_*` carries injective modules
to flasque, hence `f_*`-acyclic, modules), followed by the canonical map to
`R g_* (R f'_* (g'^* F))`.

## Main definitions

* `derivedBaseChange`: the map `Rf_*(F[0]) ⟶ Rg_* Rf'_*(g'^* F[0])` on `D⁺`, natural in `F`.
* `higherBaseChangeAdj`: the adjoint base change map `R^q f_* F ⟶ g_* R^q f'_*(g'^* F)`.
* `higherBaseChange`: the base change map `g^* R^q f_* F ⟶ R^q f'_*(g'^* F)`.

## Main results

* `rightAcyclic_pushforward_obj_injective`: the direct image of an injective module is acyclic
  for every direct image.
* `rightDerivedPlusUnitSingle_comp_derivedBaseChange`: on the canonical maps out of `(f_* F)[0]`
  the base change map on `D⁺` is `f_*` of the unit.
* `higherBaseChange_naturality`: the base change map is natural in the module.
* `isIso_rightDerivedPlusCompTrans`: `R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` on `D⁺`, for every pair of
  composable morphisms of schemes.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.HigherDirectImageBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The direct image of an injective module is acyclic for every direct image**: it is flasque
([Stacks, Tag 09T0]). -/
public theorem rightAcyclic_pushforward_obj_injective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : X.Modules) [hI : Injective I] :
    (Scheme.Modules.pushforward g).rightAcyclic ((Scheme.Modules.pushforward f).obj I) :=
  @Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective _ _ _ f.toLRSHom.toShHom
    g.toLRSHom.toShHom I hI

/-- **`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*`** on bounded below derived categories of modules, for any
composable morphisms of schemes ([Stacks, Tag 015M]). -/
public instance isIso_rightDerivedPlusCompTrans {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (Stacks.DerivedIndexing.rightDerivedPlusCompTrans (Scheme.Modules.pushforward f)
      (Scheme.Modules.pushforward g)) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective _ _ _
    (Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac _ _)).2 fun I hI =>
    haveI : Injective I := hI
    rightAcyclic_pushforward_obj_injective f g I

section Square

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- The two composite direct images of a commutative square agree. -/
public def pushforwardSquareIso :
    Scheme.Modules.pushforward g' ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp g' f ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
    (Scheme.Modules.pushforwardComp f' g).symm

/-- On sections, the identification of the two composite direct images is a restriction map
between equal opens. -/
public theorem pushforwardSquareIso_hom_app_app (M : X'.Modules) (U : S.Opens) :
    ((pushforwardSquareIso f g f' g' w).hom.app M).app U =
      M.presheaf.map (eqToHom (show (f' ≫ g) ⁻¹ᵁ U = (g' ≫ f) ⁻¹ᵁ U by rw [w])).op := by
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  rfl

/-- The comparison `Rg'_* ⋙ Rf_* ⟶ R(f ∘ g')_* = R(g ∘ f')_*` of right derived functors on `D⁺`:
the inverse of the composition isomorphism, followed by the identification of the two composite
direct images of the square. -/
public def squareDerivedTrans :
    (Scheme.Modules.pushforward g').rightDerivedFunctorPlus ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⟶
      (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlus :=
  (asIso (Stacks.DerivedIndexing.rightDerivedPlusCompTrans (Scheme.Modules.pushforward g')
      (Scheme.Modules.pushforward f))).inv ≫
    Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans (pushforwardSquareIso f g f' g' w).hom

section CommShift

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit

/-- The comparison of right derived functors of the square commutes with the shift. -/
public instance natTransCommShift_squareDerivedTrans :
    NatTrans.CommShift (squareDerivedTrans f g f' g' w) ℤ :=
  haveI : NatTrans.CommShift (asIso (Stacks.DerivedIndexing.rightDerivedPlusCompTrans
      (Scheme.Modules.pushforward g') (Scheme.Modules.pushforward f))).hom ℤ :=
    Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans _ _
  haveI := Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusNatTrans
    (pushforwardSquareIso f g f' g' w).hom
  NatTrans.CommShift.comp _ _ _

end CommShift

/-- **The base change map on `D⁺`**: for an `𝒪_X`-module `F`, the map
`Rf_*(F[0]) ⟶ Rf_* Rg'_*(g'^* F[0]) ⟶ R(f ∘ g')_*(g'^* F[0]) = R(g ∘ f')_*(g'^* F[0])` induced
by the unit `F ⟶ g'_* g'^* F`. -/
public def derivedBaseChange (F : X.Modules) :
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ⟶
      (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pullback g').obj F)) :=
  Stacks.DerivedIndexing.derivedPairMap (Scheme.Modules.pushforward g')
    (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
    (squareDerivedTrans f g f' g' w) ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F)

/-- The base change map on `D⁺` is natural in the module. -/
public theorem derivedBaseChange_naturality {F₁ F₂ : X.Modules} (φ : F₁ ⟶ F₂) :
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ) ≫
          derivedBaseChange f g f' g' w F₂ =
      derivedBaseChange f g f' g' w F₁ ≫
        (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X'.Modules 0).map
            ((Scheme.Modules.pullback g').map φ)) :=
  Stacks.DerivedIndexing.derivedPairMap_naturality _ _ _ _ _ _ φ _
    ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.naturality φ)

/-- **The map on `D⁺` attached to a pair, on the canonical maps**: for `φ : M ⟶ g'_* M'`, composed
with the canonical map `(f_* M)[0] ⟶ Rf_*(M[0])`, the map `Rf_*(M[0]) ⟶ R(g ∘ f')_*(M'[0])` is
`f_* φ` read as `f_* M ⟶ g_* f'_* M'`, followed by the canonical map of `(g ∘ f')_*`. -/
public theorem rightDerivedPlusUnitSingle_comp_derivedPairMap {M : X.Modules} {M' : X'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward g').obj M') :
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app M ≫
        Stacks.DerivedIndexing.derivedPairMap (Scheme.Modules.pushforward g')
          (Scheme.Modules.pushforward f)
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
          (squareDerivedTrans f g f' g' w) φ =
      (DerivedCategory.Plus.singleFunctor S.Modules 0).map
          ((Scheme.Modules.pushforward f).map φ ≫ (pushforwardSquareIso f g f' g' w).hom.app M') ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).app M' := by
  have ha := (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
    (Scheme.Modules.pushforward f)).naturality φ
  have hb := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_compTrans
    (Scheme.Modules.pushforward g') (Scheme.Modules.pushforward f) M'
  have hc := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_natTrans
    (pushforwardSquareIso f g f' g' w).hom M'
  have hb' : (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app
        ((Scheme.Modules.pushforward g').obj M') ≫
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map
        ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Scheme.Modules.pushforward g')).app M') ≫
      (asIso (Stacks.DerivedIndexing.rightDerivedPlusCompTrans (Scheme.Modules.pushforward g')
        (Scheme.Modules.pushforward f))).inv.app
          ((DerivedCategory.Plus.singleFunctor X'.Modules 0).obj M') =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
        (Scheme.Modules.pushforward g' ⋙ Scheme.Modules.pushforward f)).app M' := by
    rw [← Category.assoc, ← hb, Category.assoc, ← NatTrans.comp_app, asIso_inv, IsIso.hom_inv_id,
      NatTrans.id_app]
    exact Category.comp_id _
  simp only [Functor.comp_map, Functor.comp_obj] at ha
  dsimp only [Stacks.DerivedIndexing.derivedPairMap, squareDerivedTrans]
  rw [NatTrans.comp_app, Functor.map_comp, Category.assoc,
    ← Category.assoc
      ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app M),
    ← ha,
    Category.assoc, ← Category.assoc ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map _),
    ← Category.assoc
      ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app _),
    hb', hc,
    ← Category.assoc, ← Functor.map_comp]

/-- **The base change map on `D⁺` on the canonical maps**: composed with the canonical map
`(f_* F)[0] ⟶ Rf_*(F[0])`, the base change map is `f_*` of the unit `F ⟶ g'_* g'^* F` read as
`f_* F ⟶ g_* f'_* g'^* F`, followed by the canonical map of `(g ∘ f')_*`. -/
public theorem rightDerivedPlusUnitSingle_comp_derivedBaseChange (F : X.Modules) :
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app F ≫
        derivedBaseChange f g f' g' w F =
      (DerivedCategory.Plus.singleFunctor S.Modules 0).map
          ((Scheme.Modules.pushforward f).map
              ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
            (pushforwardSquareIso f g f' g' w).hom.app ((Scheme.Modules.pullback g').obj F)) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).app
            ((Scheme.Modules.pullback g').obj F) :=
  rightDerivedPlusUnitSingle_comp_derivedPairMap f g f' g' w _

/-- **The base change map attached to a pair**: for `φ : M ⟶ g'_* M'`, the map
`R^q f_* M ⟶ g_* R^q f'_* M'`, the degree-`q` cohomology of the map on `D⁺` attached to `φ`
followed by the co-edge morphism `R^q(g ∘ f')_* ⟶ g_* ∘ R^q f'_*`. -/
public def pairBaseChange {M : X.Modules} {M' : X'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward g').obj M') (q : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj M ⟶
      (Scheme.Modules.pushforward g).obj
        (((Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ)).obj M') :=
  (DerivedCategory.Plus.homologyFunctor S.Modules (q : ℤ)).map
      (Stacks.DerivedIndexing.derivedPairMap (Scheme.Modules.pushforward g')
        (Scheme.Modules.pushforward f)
        (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
        (squareDerivedTrans f g f' g' w) φ) ≫
    (Stacks.DerivedIndexing.coEdge (Scheme.Modules.pushforward f') (Scheme.Modules.pushforward g)
      q).app M'

/-- **The base change map attached to a pair is natural in the second module.** -/
public theorem pairBaseChange_comp_map {M : X.Modules} {M₁ M₂ : X'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward g').obj M₁) (ψ : M₁ ⟶ M₂) (q : ℕ) :
    pairBaseChange f g f' g' w (φ ≫ (Scheme.Modules.pushforward g').map ψ) q =
      pairBaseChange f g f' g' w φ q ≫
        (Scheme.Modules.pushforward g).map
          (((Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ)).map ψ) := by
  have h := Stacks.DerivedIndexing.derivedPairMap_naturality (Scheme.Modules.pushforward g')
    (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
    (squareDerivedTrans f g f' g' w) φ (φ ≫ (Scheme.Modules.pushforward g').map ψ) (𝟙 M) ψ
    (Category.id_comp _)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h' := (Stacks.DerivedIndexing.coEdge (Scheme.Modules.pushforward f')
    (Scheme.Modules.pushforward g) q).naturality ψ
  dsimp only [pairBaseChange]
  refine Eq.trans
    (congrArg (fun t => (DerivedCategory.Plus.homologyFunctor S.Modules (q : ℤ)).map t ≫ _) h) ?_
  refine Eq.trans
    (congrArg (· ≫ _) ((DerivedCategory.Plus.homologyFunctor S.Modules (q : ℤ)).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) h') ?_
  exact (Category.assoc _ _ _).symm

/-- **The base change map attached to a pair commutes with the connecting morphisms**: for short
exact sequences `S` of `𝒪_X`-modules and `S'` of `𝒪_{X'}`-modules and `μ : S ⟶ g'_* S'`, the
connecting morphism of `R^q f_*` along `S` followed by the map of `μ.τ₁` is the map of `μ.τ₃`
followed by `g_*` of the connecting morphism of `R^q f'_*` along `S'`. -/
public theorem canonicalδ_comp_pairBaseChange {T : ShortComplex X.Modules} (hT : T.ShortExact)
    {T' : ShortComplex X'.Modules} (hT' : T'.ShortExact)
    (μ : T ⟶ T'.map (Scheme.Modules.pushforward g')) (q : ℕ) :
    Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f) hT q ≫
        pairBaseChange f g f' g' w μ.τ₁ (q + 1) =
      pairBaseChange f g f' g' w μ.τ₃ q ≫
        (Scheme.Modules.pushforward g).map
          (Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f') hT' q) := by
  dsimp only [pairBaseChange]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) (Stacks.DerivedIndexing.canonicalδ_comp_derivedPairMap _ _ _
    (squareDerivedTrans f g f' g' w) hT hT' μ q)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) (Stacks.DerivedIndexing.canonicalδ_comp_coEdge _ _ hT' q)) ?_
  exact (Category.assoc _ _ _).symm

/-- A composite rearranged along three commuting relations. -/
public theorem paste_zero {C : Type*} [Category C] {a b c d f₀ x y : C} (s : a ⟶ b)
    (u : b ⟶ c) (dp : c ⟶ d) (al : d ⟶ x) (be : x ⟶ f₀) (m : a ⟶ x) (s' : x ⟶ y)
    (u' : y ⟶ d) (sm : b ⟶ y) (hu : u ≫ dp = sm ≫ u') (hs : m ≫ s' = s ≫ sm)
    (h1 : (s' ≫ u') ≫ al = 𝟙 _) :
    (s ≫ u) ≫ dp ≫ (al ≫ be) = m ≫ be := by
  rw [Category.assoc, ← Category.assoc u, hu, Category.assoc, ← Category.assoc s, ← hs,
    Category.assoc, ← Category.assoc s', ← Category.assoc (s' ≫ u'), h1, Category.id_comp]

/-- **The base change map attached to a pair in degree zero** is, under `R⁰ = id`, the map
`f_* M ⟶ f_* g'_* M' = g_* f'_* M'` induced by `φ`. -/
public theorem rightDerivedPlusZeroIso_inv_comp_pairBaseChange {M : X.Modules} {M' : X'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward g').obj M') :
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward f)).inv.app M ≫
        pairBaseChange f g f' g' w φ 0 =
      (Scheme.Modules.pushforward f).map φ ≫ (pushforwardSquareIso f g f' g' w).hom.app M' ≫
        (Scheme.Modules.pushforward g).map
          ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
            (Scheme.Modules.pushforward f')).inv.app M') := by
  have h0 := Stacks.DerivedIndexing.rightDerivedPlusZeroIso_inv_app (Scheme.Modules.pushforward f) M
  have h1 := Stacks.DerivedIndexing.rightDerivedPlusZeroIso_inv_app
    (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g) M'
  have hu := rightDerivedPlusUnitSingle_comp_derivedPairMap f g f' g' w φ
  have hs :=
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := S.Modules) 0).inv.naturality
      ((Scheme.Modules.pushforward f).map φ ≫ (pushforwardSquareIso f g f' g' w).hom.app M')
  have hu' : (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
        ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app M) ≫
      (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
        (Stacks.DerivedIndexing.derivedPairMap (Scheme.Modules.pushforward g')
          (Scheme.Modules.pushforward f)
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
          (squareDerivedTrans f g f' g' w) φ) =
      (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
          ((DerivedCategory.Plus.singleFunctor S.Modules 0).map
            ((Scheme.Modules.pushforward f).map φ ≫
              (pushforwardSquareIso f g f' g' w).hom.app M')) ≫
        (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
            (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).app M') := by
    rw [← Functor.map_comp, hu, Functor.map_comp]
  have h1' : ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := S.Modules) 0).inv.app
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj M')) ≫
      (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
        ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).app M')) ≫
      (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).hom.app M' = 𝟙 _ :=
    (congrArg (· ≫ _) h1.symm).trans (Iso.inv_hom_id_app _ _)
  rw [h0]
  exact paste_zero
    (s := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := S.Modules) 0).inv.app
      ((Scheme.Modules.pushforward f).obj M))
    (u := (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
        ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (Scheme.Modules.pushforward f)).app M))
    (dp := (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
        (Stacks.DerivedIndexing.derivedPairMap (Scheme.Modules.pushforward g')
          (Scheme.Modules.pushforward f)
          (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)
          (squareDerivedTrans f g f' g' w) φ))
    (al := (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).hom.app M')
    (be := (Scheme.Modules.pushforward g).map
          ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
            (Scheme.Modules.pushforward f')).inv.app M'))
    (m := (Scheme.Modules.pushforward f).map φ ≫ (pushforwardSquareIso f g f' g' w).hom.app M')
    (s' := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := S.Modules) 0).inv.app
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj M')))
    (u' := (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
            (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g)).app M'))
    (sm := (DerivedCategory.Plus.homologyFunctor S.Modules 0).map
          ((DerivedCategory.Plus.singleFunctor S.Modules 0).map
            ((Scheme.Modules.pushforward f).map φ ≫ (pushforwardSquareIso f g f' g' w).hom.app M')))
    hu' hs h1'

/-- **The base change map on higher direct images, in adjoint form**:
`R^q f_* F ⟶ g_* R^q f'_*(g'^* F)`, the degree-`q` cohomology of `derivedBaseChange`, followed by
the co-edge morphism `R^q(g ∘ f')_* ⟶ g_* ∘ R^q f'_*`. -/
public def higherBaseChangeAdj (q : ℕ) :
    (Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ) ⟶
      Scheme.Modules.pullback g' ⋙ (Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ) ⋙
        Scheme.Modules.pushforward g where
  app F := pairBaseChange f g f' g' w
    ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) q
  naturality F₁ F₂ φ := by
    have h := congrArg (DerivedCategory.Plus.homologyFunctor S.Modules (q : ℤ)).map
      (derivedBaseChange_naturality f g f' g' w φ)
    simp only [Functor.map_comp] at h
    have h' := (Stacks.DerivedIndexing.coEdge (Scheme.Modules.pushforward f')
      (Scheme.Modules.pushforward g) q).naturality ((Scheme.Modules.pullback g').map φ)
    dsimp only [Functor.comp_map, Functor.comp_obj] at h' ⊢
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ _) h) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (_ ≫ ·) h') ?_
    exact (Category.assoc _ _ _).symm

/-- **The base change map on higher direct images** `g^* R^q f_* F ⟶ R^q f'_*(g'^* F)` of a
commutative square of schemes, adjoint to `higherBaseChangeAdj`. -/
public def higherBaseChange (q : ℕ) (F : X.Modules) :
    (Scheme.Modules.pullback g).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F) ⟶
      ((Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ)).obj
        ((Scheme.Modules.pullback g').obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((higherBaseChangeAdj f g f' g' w q).app F)

/-- **The base change map on higher direct images is natural in the module.** -/
public theorem higherBaseChange_naturality (q : ℕ) {F₁ F₂ : X.Modules} (φ : F₁ ⟶ F₂) :
    (Scheme.Modules.pullback g).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).map φ) ≫
        higherBaseChange f g f' g' w q F₂ =
      higherBaseChange f g f' g' w q F₁ ≫
        ((Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ)).map
          ((Scheme.Modules.pullback g').map φ) := by
  exact (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right_square _ _ _ _
    ((higherBaseChangeAdj f g f' g' w q).naturality φ)

/-- The unit `T ⟶ g'_* g'^* T` of a short complex of `𝒪_X`-modules. -/
public def unitShortComplexHom (T : ShortComplex X.Modules) :
    T ⟶ (T.map (Scheme.Modules.pullback g')).map (Scheme.Modules.pushforward g') where
  τ₁ := (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app T.X₁
  τ₂ := (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app T.X₂
  τ₃ := (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app T.X₃
  comm₁₂ := ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.naturality T.f).symm
  comm₂₃ := ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.naturality T.g).symm

/-- **The base change map commutes with the connecting morphisms**, in adjoint form, for a short
exact sequence `T` of `𝒪_X`-modules whose pullback along `g'` is short exact. -/
public theorem canonicalδ_comp_higherBaseChangeAdj {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (hT' : (T.map (Scheme.Modules.pullback g')).ShortExact) (q : ℕ) :
    Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f) hT q ≫
        (higherBaseChangeAdj f g f' g' w (q + 1)).app T.X₁ =
      (higherBaseChangeAdj f g f' g' w q).app T.X₃ ≫
        (Scheme.Modules.pushforward g).map
          (Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f') hT' q) :=
  canonicalδ_comp_pairBaseChange f g f' g' w hT hT' (unitShortComplexHom g' T) q

/-- **The base change map commutes with the connecting morphisms**: for a short exact sequence `T`
of `𝒪_X`-modules whose pullback along `g'` is short exact,
`g^* δ ≫ β_{q+1} = β_q ≫ δ'` as maps `g^* R^q f_* T₃ ⟶ R^{q+1} f'_* g'^* T₁`. -/
public theorem canonicalδ_comp_higherBaseChange {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (hT' : (T.map (Scheme.Modules.pullback g')).ShortExact) (q : ℕ) :
    (Scheme.Modules.pullback g).map
        (Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f) hT q) ≫
        higherBaseChange f g f' g' w (q + 1) T.X₁ =
      higherBaseChange f g f' g' w q T.X₃ ≫
        Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f') hT' q := by
  exact (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right_square _ _ _ _
    (canonicalδ_comp_higherBaseChangeAdj f g f' g' w hT hT' q)

/-- **The ordinary base change map** `g^* f_* F ⟶ f'_* g'^* F` of a commutative square, adjoint to
`f_* F ⟶ f_* g'_* g'^* F = g_* f'_* g'^* F`. -/
public def baseChangeMap (F : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
      (pushforwardSquareIso f g f' g' w).hom.app ((Scheme.Modules.pullback g').obj F))

/-- **The base change map on higher direct images in degree zero is the ordinary base change
map**, under `R⁰f_* = f_*` and `R⁰f'_* = f'_*`. -/
public theorem higherBaseChange_zero (F : X.Modules) :
    (Scheme.Modules.pullback g).map
        ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
          (Scheme.Modules.pushforward f)).inv.app F) ≫
        higherBaseChange f g f' g' w 0 F ≫
        (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward f')).hom.app
          ((Scheme.Modules.pullback g').obj F) =
      baseChangeMap f g f' g' w F := by
  have h := rightDerivedPlusZeroIso_inv_comp_pairBaseChange f g f' g' w
    ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F)
  have h' : (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward f)).inv.app F ≫
      (higherBaseChangeAdj f g f' g' w 0).app F ≫
        (Scheme.Modules.pushforward g).map
          ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward f')).hom.app
            ((Scheme.Modules.pullback g').obj F)) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
        (pushforwardSquareIso f g f' g' w).hom.app ((Scheme.Modules.pullback g').obj F) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ _) h) ?_
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  unfold higherBaseChange baseChangeMap
  refine Eq.trans (congrArg (_ ≫ ·) (Adjunction.homEquiv_naturality_right_symm _ _ _).symm) ?_
  exact ((Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans (congrArg _ h'))

/-- **The base change map in the indexing by injective resolutions**:
`g^* R^q f_* F ⟶ R^q f'_*(g'^* F)`. -/
public def higherBaseChangeNat (q : ℕ) (F : X.Modules) :
    (Scheme.Modules.pullback g).obj (((Scheme.Modules.pushforward f).rightDerived q).obj F) ⟶
      ((Scheme.Modules.pushforward f').rightDerived q).obj ((Scheme.Modules.pullback g').obj F) :=
  (Scheme.Modules.pullback g).map ((Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app F) ≫
    higherBaseChange f g f' g' w q F ≫ (Stacks.DerivedIndexing.rightDerivedIso _ q).inv.app _

/-- The base change map in the indexing by injective resolutions is natural in the module. -/
public theorem higherBaseChangeNat_naturality (q : ℕ) {F₁ F₂ : X.Modules} (φ : F₁ ⟶ F₂) :
    (Scheme.Modules.pullback g).map (((Scheme.Modules.pushforward f).rightDerived q).map φ) ≫
        higherBaseChangeNat f g f' g' w q F₂ =
      higherBaseChangeNat f g f' g' w q F₁ ≫
        ((Scheme.Modules.pushforward f').rightDerived q).map
          ((Scheme.Modules.pullback g').map φ) := by
  unfold higherBaseChangeNat
  rw [← Functor.map_comp_assoc, (Stacks.DerivedIndexing.rightDerivedIso _ q).hom.naturality φ,
    Functor.map_comp_assoc, reassoc_of% (higherBaseChange_naturality f g f' g' w q φ)]
  simp only [Category.assoc, NatTrans.naturality]

/-- **The base change map commutes with the connecting morphisms of the long exact sequences of
higher direct images**, in the indexing by injective resolutions. -/
public theorem δ_comp_higherBaseChangeNat {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (hT' : (T.map (Scheme.Modules.pullback g')).ShortExact) (q : ℕ) :
    (Scheme.Modules.pullback g).map
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (Scheme.Modules.pushforward f)).δ hT q) ≫
        higherBaseChangeNat f g f' g' w (q + 1) T.X₁ =
      higherBaseChangeNat f g f' g' w q T.X₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (Scheme.Modules.pushforward f')).δ hT' q := by
  show (Scheme.Modules.pullback g).map
      ((Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app T.X₃ ≫
        Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f) hT q ≫
        (Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).inv.app T.X₁) ≫ _ =
    _ ≫ (Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app _ ≫
      Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f') hT' q ≫
      (Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).inv.app _
  unfold higherBaseChangeNat
  simp only [Functor.map_comp, Category.assoc]
  have hc := Iso.map_inv_hom_id_assoc ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward f) (q + 1)).app T.X₁) (Scheme.Modules.pullback g)
    (higherBaseChange f g f' g' w (q + 1) T.X₁ ≫
      (Stacks.DerivedIndexing.rightDerivedIso _ (q + 1)).inv.app _)
  simp only [Iso.app_inv, Iso.app_hom] at hc
  rw [hc]
  refine congrArg (_ ≫ ·)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (canonicalδ_comp_higherBaseChange f g f' g' w hT hT' q))).trans
      ((Category.assoc _ _ _).trans ?_))
  exact congrArg (_ ≫ ·) (Iso.inv_hom_id_app_assoc _ _ _).symm

end Square

end Stacks.AlgebraicGeometry.HigherDirectImageBaseChange

end
