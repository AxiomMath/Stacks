module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonCanonicalBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonProperFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardReflectsIsomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensorRight
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangeProjection

/-!
# Base change of the relative dualizing complex over an affine base (Stacks 0E5I (1) at `𝒪`)

Consider a cartesian square of algebraic spaces

```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```

with `Y`, `Y'` affine and `f` proper, flat and of finite presentation. The base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an isomorphism at `K = 𝒪_Y` (Stacks 0E5I, case (1),
at the structure sheaf). Hence `L(g')^* ω^•_{X/Y} ≅ ω^•_{X'/Y'}` for the relative dualizing
complexes `a(𝒪_Y)`, `a'(𝒪_{Y'})` over the affine bases.

## Proof

`g` is affine, so `g'` is affine and `Rg'_*` reflects isomorphisms (Stacks 08II). After `Rg'_*`,
the base change map is identified
(`CategoryTheory.RightAdjointBaseChange.rightUnitProjection_comp_map_comp_rightAdjointMate`) with
the two-variable map `Lf^*J ⊗ a(𝒪_Y) ⟶ a(J ⊗ 𝒪_Y)` of Stacks 0E5P at `J = Rg_*𝒪_{Y'}`, up to the
projection formulas along `g` and `g'` at the unit (Stacks 08IN), the transposed base change map
`Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*L(f')^*𝒪_{Y'} ≅ Rg'_*𝒪_{X'}` (invertible by Stacks 08IR, `f` being flat)
and the braidings of `⊗^L`. The two-variable map is invertible by Stacks 0E5U. The inputs of the
identification on `D_QCoh` are the hexagon of Stacks 0E48
(`AlgebraicGeometry.Space.quasicoherentDualityData_projectionFormulaMap_baseChange`), Stacks 07A4
with the unitors and with the braidings, and the adjoint transpose of the transposed base change
map.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedBraiding`: the commutativity constraint of `⊗^L`
  on `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedModulePullback_map_braiding_comp`: Stacks 07A4 on
  `D_QCoh` is compatible with the braidings.
* `quasicoherentDerivedModulePullback_map_transposedBaseChange_comp_counit`:
  the adjoint transpose of the transposed base change map.
* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_structureSheaf`:
  the base change map of Stacks 0E5D is invertible at `𝒪_Y`.
* `nonempty_quasicoherentDerivedModulePullback_affineRelativeDualizingComplex_iso`:
  `L(g')^* a(𝒪_Y) ≅ a'(𝒪_{Y'})`.

## Implementation notes

The identification `Lf^* ⋙ L(g')^* ≅ L(f' ≫ g)^*` around the square contains an `eqToIso` along
`g' ≫ f = f' ≫ g`. Its components at the two spellings `(Rg_* K).obj` (on `D_QCoh`) and
`Rg_*(K.obj)` (on `D(𝒪)`) of the same object are compared through a heterogeneous equality
(`AlgebraicGeometry.Space.heq_app_comp_app`), so the kernel never unfolds that `eqToIso`.

## References

* [Stacks Project, Tag 0E5I](https://stacks.math.columbia.edu/tag/0E5I)
* [Stacks Project, Tag 0E5U](https://stacks.math.columbia.edu/tag/0E5U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Generic

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The composite of the components of two natural transformations at two equal objects. -/
theorem heq_app_comp_app {E : Type*} [Category E] {F₁ F₂ F₃ : E ⥤ D} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃) {Z Z' : E} (h : Z = Z') : HEq (α.app Z ≫ β.app Z) (α.app Z' ≫ β.app Z') := by
  subst h
  rfl

/-- An adjoint transpose followed by `R` of a map: if `L(x)` followed by the counit is
`a ≫ α₁_Z ≫ α₂_Z ≫ e` and `α₁ ≫ α₂ = α₃ ≫ α₄`, then `L(x ≫ R v)` followed by the counit is
`a ≫ c ≫ e ≫ v` for any `c` heterogeneously equal to `α₃_Z ≫ α₄_Z`. -/
theorem map_comp_map_comp_counit_eq_of_heq {E : Type*} [Category E] {F₁ F₂ F₃ F₄ : E ⥤ D}
    {α₁ : F₁ ⟶ F₂} {α₂ : F₂ ⟶ F₃} {α₃ : F₁ ⟶ F₄} {α₄ : F₄ ⟶ F₃} (hα : α₁ ≫ α₂ = α₃ ≫ α₄)
    {Z : E} {X : C} {P : D} {x : X ⟶ R.obj P} {a : L.obj X ⟶ F₁.obj Z} {e : F₃.obj Z ⟶ P}
    (h : L.map x ≫ adj.counit.app P = a ≫ α₁.app Z ≫ α₂.app Z ≫ e) {M : D} (v : P ⟶ M)
    (c : F₁.obj Z ⟶ F₃.obj Z) (hc : HEq (α₃.app Z ≫ α₄.app Z) c) :
    L.map (x ≫ R.map v) ≫ adj.counit.app M = a ≫ c ≫ e ≫ v := by
  have hn : L.map (R.map v) ≫ adj.counit.app M = adj.counit.app P ≫ v := adj.counit.naturality v
  have hZ : α₁.app Z ≫ α₂.app Z = α₃.app Z ≫ α₄.app Z := by
    simpa only [NatTrans.comp_app] using NatTrans.congr_app hα Z
  rw [L.map_comp, Category.assoc, hn, reassoc_of% h, reassoc_of% hZ, ← eq_of_heq hc]
  simp only [Category.assoc]

end Generic



/-! ### The braiding of `⊗^L` on `D_QCoh` -/

variable (B S hS) in
/-- **The commutativity constraint `P ⊗^L Q ≅ Q ⊗^L P` of `D_QCoh(𝒪_X)`**, as a morphism of
bifunctors: the commutativity constraint of the derived tensor product (Stacks 0FPT). -/
def quasicoherentDerivedBraiding (X : AlgebraicSpaces B S hS) :
    quasicoherentDerivedTensor B S hS X ⟶ (quasicoherentDerivedTensor B S hS X).flip where
  app P :=
    { app := fun Q => ObjectProperty.homMk
        ((smallEtaleDerivedTensorProduct B S hS X).braiding P.obj Q.obj).hom
      naturality := fun _ _ ψ => ObjectProperty.hom_ext _
        ((smallEtaleDerivedTensorProduct B S hS X).braiding_hom_naturality_right P.obj ψ.hom) }
  naturality P P' φ := by
    refine NatTrans.ext (funext fun Q => ObjectProperty.hom_ext _ ?_)
    have h := (smallEtaleDerivedTensorProduct B S hS X).braiding_hom_naturality φ.hom (𝟙 Q.obj)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, NatTrans.id_app] at h
    exact h

/-- The component of `quasicoherentDerivedBraiding` at `P` and `Q` is the commutativity
constraint `P ⊗^L Q ≅ Q ⊗^L P` of the derived tensor product of the underlying complexes. -/
theorem quasicoherentDerivedBraiding_app_app_hom (X : AlgebraicSpaces B S hS)
    (P Q : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (((quasicoherentDerivedBraiding B S hS X).app P).app Q).hom =
      ((smallEtaleDerivedTensorProduct B S hS X).braiding P.obj Q.obj).hom :=
  rfl

/-- The components of `quasicoherentDerivedBraiding` are isomorphisms. -/
instance isIso_quasicoherentDerivedBraiding_app_app (X : AlgebraicSpaces B S hS)
    (P Q : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsIso (((quasicoherentDerivedBraiding B S hS X).app P).app Q) :=
  (ObjectProperty.isIso_hom_iff _).1
    (inferInstanceAs (IsIso ((smallEtaleDerivedTensorProduct B S hS X).braiding P.obj Q.obj).hom))

/-- **Stacks 07A4 on `D_QCoh` is compatible with the braidings.** -/
theorem quasicoherentDerivedModulePullback_map_braiding_comp {X X' : AlgebraicSpaces B S hS}
    (h : X' ⟶ X) (P Q : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (quasicoherentDerivedModulePullback h).map
        (((quasicoherentDerivedBraiding B S hS X).app P).app Q) ≫
        (quasicoherentDerivedPullbackTensorComparison h).app (P, Q) =
      (quasicoherentDerivedPullbackTensorComparison h).app (Q, P) ≫
        ((quasicoherentDerivedBraiding B S hS X').app
          ((quasicoherentDerivedModulePullback h).obj P)).app
          ((quasicoherentDerivedModulePullback h).obj Q) :=
  ObjectProperty.hom_ext _ (smallEtaleDerivedPullbackTensorIso_braiding h P.obj Q.obj)

section SquareIso

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- The iterated derived pullbacks around the square, read through the common composite. -/
theorem smallEtaleDerivedModulePullbackSquareIso_eq_trans (w : g' ≫ f = f' ≫ g) :
    smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w =
      smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS w :=
  rfl

/-- The two identifications of the derived pullbacks along the two equal composites agree. -/
theorem smallEtaleDerivedModulePullbackCongr_symm_inv (w : g' ≫ f = f' ≫ g)
    (w' : f' ≫ g = g' ≫ f) :
    (smallEtaleDerivedModulePullbackCongr B S hS w').inv =
      (smallEtaleDerivedModulePullbackCongr B S hS w).hom :=
  rfl

/-- The composite identification followed by the inverse of the identification around the
transposed square is the identification around the square followed by the inverse composite
identification. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_comp_squareIso_flip_inv
    (sq : IsPullback g' f' f g) :
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f).hom ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS g f g' f' sq.flip.w).inv =
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv := by
  rw [smallEtaleDerivedModulePullbackSquareIso_eq_trans sq.flip.w,
    smallEtaleDerivedModulePullbackSquareIso_eq_trans sq.w, Iso.trans_inv, Iso.trans_hom,
    smallEtaleDerivedModulePullbackCongr_symm_inv sq.w sq.flip.w, Category.assoc]

end SquareIso

variable (hZ : B.Contains (⊤_ Scheme.{u}))

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)

include hYqs hY'qc hY'qs in
/-- **The transposed base change map**, `Lf^*Rg_*K ⟶ Rg'_*L(f')^*K ⟶ Rg'_*M`, has the adjoint
transpose under `L(g')^* ⊣ Rg'_*` given by the identification of the iterated pullbacks around the
square (at `Rg_*K`), `L(f')^*` of the counit of `Lg^* ⊣ Rg_*` and the given map. -/
theorem quasicoherentDerivedModulePullback_map_transposedBaseChange_comp_counit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y'.1 Y'.2)
    {M : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2}
    (v : (quasicoherentDualityData hZ f' (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).pullback.obj K ⟶ M) :
    (quasicoherentDerivedModulePullback g').map
        ((squareBaseChange hZ sq.flip hY'qc hY'qs hYqs hXqc hXqs).app K ≫
          (quasicoherentDerivedPushforward B S hS g'
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
              (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
              (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom)).map v) ≫
        (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs).counit.app M =
      (ObjectProperty.homMk
          ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app
              ((quasicoherentDerivedPushforward B S hS g
                (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
                (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
                  g.hom)).obj K).obj ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app
              ((quasicoherentDerivedPushforward B S hS g
                (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
                (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
                  g.hom)).obj K).obj) :
          (quasicoherentDerivedModulePullback g').obj
              ((quasicoherentDerivedModulePullback f).obj
                ((quasicoherentDerivedPushforward B S hS g
                  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
                  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
                    g.hom)).obj K)) ⟶
            (quasicoherentDerivedModulePullback f').obj
              ((quasicoherentDerivedModulePullback g).obj
                ((quasicoherentDerivedPushforward B S hS g
                  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
                  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
                    g.hom)).obj K))) ≫
        (quasicoherentDualityData hZ f' (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).pullback.map
          ((squareAdjG hZ hYqs hY'qc hY'qs).counit.app K) ≫ v := by
  refine ObjectProperty.hom_ext _ ?_
  have e1 := ι_map_quasicoherentDerivedModuleAdjunction_counit_app B S hS g'
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom) M
  have e2 := ι_map_quasicoherentDerivedModuleAdjunction_counit_app B S hS g
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom) K
  have h0 := ((Adjunction.homEquiv_counit _ _ _ _).symm.trans
    (smallEtaleDerivedModuleBaseChangeMap_adjoint B S hS g f g' f' sq.flip.w K.obj)).trans
      (Category.id_comp _).symm
  have key := map_comp_map_comp_counit_eq_of_heq (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackCompIso_hom_comp_squareIso_flip_inv sq) h0 v.hom
    ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app
        ((quasicoherentDerivedPushforward B S hS g
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
            g.hom)).obj K).obj ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app
        ((quasicoherentDerivedPushforward B S hS g
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs
            g.hom)).obj K).obj)
    (heq_app_comp_app _ _ rfl)
  exact (congrArg (fun t => _ ≫ t) e1).trans ((key.trans (Category.id_comp _)).trans
    (congrArg (fun t => _ ≫ (smallEtaleDerivedModulePullback B S hS f').map t ≫ v.hom) e2.symm))


/-- **Stacks 0E5I (1) at the structure sheaf.** For a cartesian square of algebraic spaces with
`Y`, `Y'` affine and `f` proper, flat and of finite presentation, the base change map
`L(g')^* a(𝒪_Y) ⟶ a'(Lg^*𝒪_Y)` of Stacks 0E5D is an isomorphism. -/
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_structureSheaf
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
      (torIndependent_of_isFlat_left f g hfl)).app (derivedStructureSheaf B S hS Y.1 Y.2)) := by
  have hYqc : IsQuasiCompactSpace B S hS Y.1 := hY.isQuasiCompactSpace
  have hTor := torIndependent_of_isFlat_left f g hfl
  have hg : IsAffineHom B S hS g.hom := isAffineHom_of_isAffineSpace B S hS g.hom hY' hY
  have hg' : IsAffineHom B S hS g'.hom :=
    isAffineHom_hom_of_isPullback sq.flip hg
  let : IsIso (RightAdjointBaseChange.rightAdjointMate (squareAdjF hZ hXqc hXqs hYqs)
      (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs) (squareAdjG hZ hYqs hY'qc hY'qs)
      (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)) :=
    isIso_quasicoherentDerivedRightAdjointBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  -- the transposed base change map at the unit is invertible (Stacks 08IR)
  have := isIso_squareBaseChange hZ sq.flip hY'qc hY'qs hYqs hXqc hXqs hTor.symm
  have hυ : IsIso (ObjectProperty.homMk
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f').hom :
      (quasicoherentDerivedModulePullback f').obj (derivedStructureSheaf B S hS Y'.1 Y'.2) ⟶
        derivedStructureSheaf B S hS X'.1 X'.2) :=
    (ObjectProperty.isIso_hom_iff _).1
      (inferInstanceAs (IsIso (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS)
        f').hom))
  -- the projection formulas (Stacks 08IN)
  have hp := isIso_quasicoherentPullbackComparisonData_projectionFormulaMap f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
      (derivedStructureSheaf B S hS Y.1 Y.2))
    ((quasicoherentDerivedPushforward B S hS g
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom)).obj
        (derivedStructureSheaf B S hS Y'.1 Y'.2))
  have : IsIso (adjunctionTensorMap (squareAdjG hZ hYqs hY'qc hY'qs)
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasicoherentDerivedTensor B S hS Y))
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasicoherentDerivedTensor B S hS Y'))
      (quasicoherentDerivedPullbackTensorComparison g) (derivedStructureSheaf B S hS Y'.1 Y'.2)
      (derivedStructureSheaf B S hS Y.1 Y.2)) :=
    isIso_quasicoherentPullbackComparisonData_projectionFormulaMap g _ _ _ _
  have : IsIso (adjunctionTensorMap (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasicoherentDerivedTensor B S hS X))
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasicoherentDerivedTensor B S hS X'))
      (quasicoherentDerivedPullbackTensorComparison g') (derivedStructureSheaf B S hS X'.1 X'.2)
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2))) :=
    isIso_quasicoherentPullbackComparisonData_projectionFormulaMap g' _ _ _ _
  -- the two-variable map of Stacks 0E5P is invertible (Stacks 0E5U)
  have h0 := isIso_quasicoherentDerivedCompareWithPullback_app_of_isProper hZ f hYqc hYqs hf hfl
    hfp ((quasicoherentDerivedPushforward B S hS g
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom)).obj
        (derivedStructureSheaf B S hS Y'.1 Y'.2))
  rw [quasicoherentDerivedCompareWithPullback_app] at h0
  have hc : IsIso ((quasicoherentDualityData hZ f hXqc hXqs hYqs).compareWithPullbackTensor
      (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs)
      ((quasicoherentDerivedPushforward B S hS g
        (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
        (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom)).obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2))
      (derivedStructureSheaf B S hS Y.1 Y.2)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).map
        ((quasicoherentDerivedTensorRightUnitor B S hS Y).hom.app _)) _ h0
  have key := RightAdjointBaseChange.isIso_map_map_app_of_isIso (squareAdjF hZ hXqc hXqs hYqs)
    (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs) (squareAdjG hZ hYqs hY'qc hY'qs)
    (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
    (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)
    (quasicoherentDerivedTensor B S hS Y) (quasicoherentDerivedTensor B S hS X)
    (quasicoherentDerivedTensor B S hS Y') (quasicoherentDerivedTensor B S hS X')
    (quasicoherentDualityData hZ f' (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).adj
    (quasicoherentDerivedPullbackTensorComparison g)
    (quasicoherentDerivedPullbackTensorComparison g')
    (quasicoherentDerivedPullbackTensorComparison f')
    (quasicoherentDerivedBraiding B S hS Y) (quasicoherentDerivedBraiding B S hS X)
    (quasicoherentDerivedBraiding B S hS Y') (quasicoherentDerivedBraiding B S hS X')
    (derivedStructureSheaf B S hS Y'.1 Y'.2) (derivedStructureSheaf B S hS X'.1 X'.2)
    (quasicoherentDerivedTensorRightUnitor B S hS Y').hom
    (quasicoherentDerivedTensorRightUnitor B S hS X').hom
    (ObjectProperty.homMk
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f').hom :
      (quasicoherentDerivedModulePullback f').obj (derivedStructureSheaf B S hS Y'.1 Y'.2) ⟶
        derivedStructureSheaf B S hS X'.1 X'.2)
    _ _ (derivedStructureSheaf B S hS Y.1 Y.2) _ _
    ((quasicoherentDualityData hZ f hXqc hXqs hYqs)
      |>.projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit
        (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs) _ _)
    (quasicoherentDualityData_projectionFormulaMap_baseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs _ _)
    (quasicoherentDerivedModulePullback_map_transposedBaseChange_comp_counit hZ sq hXqc hXqs hYqs
      hY'qc hY'qs _ _)
    (fun Q => quasicoherentDerivedPullbackTensorComparison_unit (g := f') Q)
    (fun P Q => quasicoherentDerivedModulePullback_map_braiding_comp g P Q)
    (fun P Q => quasicoherentDerivedModulePullback_map_braiding_comp g' P Q)
    (fun P Q => quasicoherentDerivedModulePullback_map_braiding_comp f' P Q)
  -- `Rg'_*` reflects isomorphisms (Stacks 08II)
  have h1 : IsIso ((derivedModulePushforward B S hS g').map
      ((RightAdjointBaseChange.map (squareAdjF hZ hXqc hXqs hYqs)
        (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs) (squareAdjG hZ hYqs hY'qc hY'qs)
        (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
        (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)).app
          (derivedStructureSheaf B S hS Y.1 Y.2)).hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map ((quasicoherentDerivedPushforward B S hS g'
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
        (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
        (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom)).map
      ((RightAdjointBaseChange.map (squareAdjF hZ hXqc hXqs hYqs)
        (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs) (squareAdjG hZ hYqs hY'qc hY'qs)
        (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
        (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)).app
          (derivedStructureSheaf B S hS Y.1 Y.2)))))
  have h2 := isIso_of_isIso_derivedModulePushforward_map_of_isAffineHom B S hS g' hg'
    (derivedModulePushforward B S hS g') (derivedModulePushforwardUnit B S hS g')
    (((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs ⋙
      quasicoherentDerivedModulePullback g').obj (derivedStructureSheaf B S hS Y.1 Y.2)).property)
    (((quasicoherentDerivedModulePullback g ⋙ quasicoherentDerivedRightAdjoint hZ f'
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).property) _ h1
  exact (ObjectProperty.isIso_hom_iff _).1 h2

end Square

/-- **Base change of the relative dualizing complex over an affine base** (Stacks 0E5I (1) at
`𝒪_Y`): for a cartesian square of algebraic spaces with `Y`, `Y'` affine and `f` proper, flat
and of finite presentation, `L(g')^* ω^•_{X/Y} ≅ ω^•_{X'/Y'}`, where `ω^•_{X/Y} = a(𝒪_Y)` and
`ω^•_{X'/Y'} = a'(𝒪_{Y'})`. The isomorphism is the base change map of Stacks 0E5D at `𝒪_Y`
followed by `a'` of `Lg^*𝒪_Y ≅ 𝒪_{Y'}`. -/
theorem nonempty_quasicoherentDerivedModulePullback_affineRelativeDualizingComplex_iso
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfp' : IsFinitePresentation B S hS f'.hom) :
    Nonempty ((quasicoherentDerivedModulePullback g').obj
        (affineRelativeDualizingComplex hZ f hfp hY) ≅
      affineRelativeDualizingComplex hZ f' hfp' hY') := by
  have hXqc := isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom hY hfp.2.1
  have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ f.hom
    X.2 hY hfp.2.2
  have hYqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY
  have hY'qc : IsQuasiCompactSpace B S hS Y'.1 := hY'.isQuasiCompactSpace
  have hY'qs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY'
  have h := isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_structureSheaf hZ sq hXqc hXqs
    hYqs hY'qc hY'qs hY hY' hf hfl hfp
  exact ⟨@asIso _ _ _ _ _ h ≪≫
    (quasicoherentDerivedRightAdjoint hZ f'
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).mapIso
      (ObjectProperty.isoMk _
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g))⟩

end AlgebraicGeometry.Space

end
