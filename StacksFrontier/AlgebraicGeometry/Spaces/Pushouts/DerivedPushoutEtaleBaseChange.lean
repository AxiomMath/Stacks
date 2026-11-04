module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeAffineBaseCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomExactPullback

/-!
# The canonical form of Stacks 08GE

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of algebraic spaces over a scheme `S` with `g` étale. Stacks 08GE says that
restriction to `Y'` commutes with the unbounded derived direct image. The library registers it as
an abstract isomorphism `(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})`
(`AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso`), built from Stacks 03LX by
the universal property of right derived functors, and not identified with any canonical map. This
file proves the canonical form: **the base change map** `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` — the mate, under the derived
adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ Rf'_*`, of the identification of the two iterated derived
pullbacks around the square by the compositors of Stacks 0D6D — is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap`: the canonical form of
  Stacks 08GE.
* `AlgebraicGeometry.RingedToposHom.isIso_derivedBaseChange_of_isIso_compositionSquare`: the same
  for a square of morphisms of ringed topoi whose derived 2-cell is built from the compositors of
  Stacks 0D6D and a renaming along an equality of morphisms, when the two horizontal pullbacks are
  exact, `(g')^*` keeps K-injective complexes K-injective and the module base change map of the
  underived square is invertible. It is the counterpart of
  `AlgebraicGeometry.RingedToposHom.TwoIso.isIso_derivedBaseChange_of_isIso_moduleBaseChange` for a
  2-cell which is not the one of a 2-isomorphism of morphisms of ringed topoi.
* `Stacks.CategoryTheory.BaseChange.map_fac_of_counit_fac`: for a square of adjunctions sitting
  over a square of underived adjunctions through comparison maps, the base change map at the image
  of an object is computed by an underived map with the adjoint property of a base change map.
  Nothing in it mentions sheaves or derived categories.

## The argument

It is the source's. Compute `Rf_*` on a K-injective complex `I`. The pullbacks along the étale
morphisms `g` and `g'` are exact (they are étale restriction, Stacks 03LW), so `Lg^*` and
`L(g')^*` are computed termwise; `(g')^* I` is again K-injective (Stacks 08FI,
`AlgebraicGeometry.Space.isKInjective_etaleModulePullback`) and so computes `Rf'_*`. What is left
is the module base change map `g^* f_* ⟶ f'_* (g')^*`, applied termwise to `I`; that it is
invertible is Stacks 03LX in its canonical form,
`AlgebraicGeometry.Space.isIso_mateEquiv_smallEtaleToposPullbackCompIso_square`. The bookkeeping
is that the derived 2-cell of `smallEtaleDerivedModuleBaseChangeMap` is compatible with the
comparisons `L(-)^* ⟶ (-)^*` of Stacks 06YY and the underived compositors of Stacks 03D6
(`AlgebraicGeometry.RingedToposHom.compositionSquare_comparison`).

## Implementation notes

The argument is carried out for arbitrary morphisms of ringed topoi and only then instantiated at
the small étale ringed topoi of algebraic spaces. At the concrete topoi the elaborator and the
kernel unfold the pullback of modules when they compare the composite
`(F ⋙ G).mapHomologicalComplex` with `F.mapHomologicalComplex ⋙ G.mapHomologicalComplex`, which is
out of budget; over variables the comparison is cheap. For the same reason the renaming along the
commutativity of the square enters the generic statement as an equality of morphisms of ringed
topoi.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is erased in this file:
its universe `max u v r w` cannot be unified with the universe of the modules on the small étale
site of an algebraic space and leaves the elaborator stuck rather than failing.

## References

* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {KY : Type u₁} {KX : Type u₂} {KY' : Type u₃} {KX' : Type u₄}
  {DY : Type u₅} {DX : Type u₆} {DY' : Type u₇} {DX' : Type u₈}
  {_ : Category.{v₁} KY} {_ : Category.{v₂} KX} {_ : Category.{v₃} KY'} {_ : Category.{v₄} KX'}
  {_ : Category.{v₅} DY} {_ : Category.{v₆} DX} {_ : Category.{v₇} DY'} {_ : Category.{v₈} DX'}
  {QY : KY ⥤ DY} {QX : KX ⥤ DX} {QY' : KY' ⥤ DY'} {QX' : KX' ⥤ DX'}
  {pf : KY ⥤ KX} {qf : KX ⥤ KY} {pf' : KY' ⥤ KX'} {qf' : KX' ⥤ KY'}
  {pg : KY ⥤ KY'} {pg' : KX ⥤ KX'}
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'} {Lc : DY ⥤ DX'}

/-- **The base change map computed by an underived one.** Let `Lf ⊣ Rf` and `Lf' ⊣ Rf'` sit over
underived adjunctions `pf ⊣ qf` and `pf' ⊣ qf'` through localization functors `Q`, comparison
maps `c : Q ⋙ L ⟶ p ⋙ Q` for the four left adjoints and comparison maps `u : q ⋙ Q ⟶ Q ⋙ R` for
the two right adjoints, compatible with the counits (`hf`, `hf'`: the shape of Stacks 0FPI). Let
`m` be an underived comparison of the two composites around the square at `qf I`, compatible with
the derived one through the comparisons (`hsq`), and let `t : pg (qf I) ⟶ qf' (pg' I)` have the
adjoint property of a base change map for `m` (`ht`). Then the derived base change map at `Q I`,
preceded by `Lg` of `u` and followed by `Rf'` of `c`, is `c`, followed by `Q t` and `u`. -/
theorem map_fac_of_counit_fac (adjUf : pf ⊣ qf) (adjUf' : pf' ⊣ qf')
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (cf : QY ⋙ Lf ⟶ pf ⋙ QX) (cf' : QY' ⋙ Lf' ⟶ pf' ⋙ QX')
    (cg : QY ⋙ Lg ⟶ pg ⋙ QY') (cg' : QX ⋙ Lg' ⟶ pg' ⋙ QX')
    (uf : qf ⋙ QY ⟶ QX ⋙ Rf) (uf' : qf' ⋙ QY' ⟶ QX' ⋙ Rf')
    (hf : ∀ I, Lf.map (uf.app I) ≫ adjf.counit.app (QX.obj I) =
      cf.app (qf.obj I) ≫ QX.map (adjUf.counit.app I))
    (hf' : ∀ J, Lf'.map (uf'.app J) ≫ adjf'.counit.app (QX'.obj J) =
      cf'.app (qf'.obj J) ≫ QX'.map (adjUf'.counit.app J))
    (I : KX) (m : pf'.obj (pg.obj (qf.obj I)) ⟶ pg'.obj (pf.obj (qf.obj I)))
    (hsq : eg.hom.app (QY.obj (qf.obj I)) ≫ ef.inv.app (QY.obj (qf.obj I)) ≫
        Lg'.map (cf.app (qf.obj I)) ≫ cg'.app (pf.obj (qf.obj I)) =
      Lf'.map (cg.app (qf.obj I)) ≫ cf'.app (pg.obj (qf.obj I)) ≫ QX'.map m)
    (t : pg.obj (qf.obj I) ⟶ qf'.obj (pg'.obj I))
    (ht : pf'.map t ≫ adjUf'.counit.app (pg'.obj I) = m ≫ pg'.map (adjUf.counit.app I)) :
    Lg.map (uf.app I) ≫ map adjf adjf' eg ef (QX.obj I) ≫ Rf'.map (cg'.app I) =
      cg.app (qf.obj I) ≫ QY'.map t ≫ uf'.app (pg'.obj I) := by
  apply (adjf'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have h1 := homEquiv_symm_map adjf adjf' eg ef (QX.obj I)
  rw [Adjunction.homEquiv_counit] at h1
  have h2 : Lf'.map (Rf'.map (cg'.app I)) ≫ adjf'.counit.app (QX'.obj (pg'.obj I)) =
      adjf'.counit.app (Lg'.obj (QX.obj I)) ≫ cg'.app I :=
    adjf'.counit_naturality (cg'.app I)
  have h3 := (eg.hom ≫ ef.inv).naturality (uf.app I)
  have h5 := cg'.naturality (adjUf.counit.app I)
  have h6 := cf'.naturality t
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
    Category.assoc] at h3 h5 h6
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [h2, reassoc_of% h1, reassoc_of% h3, ← Functor.map_comp_assoc, hf I, Functor.map_comp,
    Category.assoc, h5, reassoc_of% hsq, hf', reassoc_of% h6, ← QX'.map_comp (pf'.map t), ht,
    QX'.map_comp]

/-- **Three comparison squares paste.** In the shape of the derived 2-cell of a base change map:
if the comparison `a₁ ≫ a₂` of one composite is compatible with `c₁` through `μ₁` (`hA`), the
comparison `b₁ ≫ b₂` of the other with `c₂` through `μ₂` (`hB`), and a renaming `γ` with `c₁` and
`c₂` through `ν` (`hC`), then `(a₁ ≫ a₂) ≫ γ ≫ (b₁ ≫ b₂)⁻¹` is compatible with the comparisons
through `μ₁ ≫ ν ≫ μ₂⁻¹`. -/
theorem comp_comp_eq_of_comparisons {D : Type u₁} {K : Type u₂} {_ : Category.{v₁} D}
    {_ : Category.{v₂} K} (Q : K ⥤ D) {P M₁ N₁ P' M₂ N₂ U V : D} {k₀ k₁ k₂ k₃ : K}
    {a₁ : P ⟶ M₁} {a₂ : M₁ ⟶ N₁} {b₁ : P' ⟶ M₂} {b₂ : M₂ ⟶ N₂} {b₁' : M₂ ⟶ P'}
    {b₂' : N₂ ⟶ M₂} {γ : N₁ ⟶ N₂} {c₁ : N₁ ⟶ Q.obj k₁} {c₂ : N₂ ⟶ Q.obj k₂} {L₁ : P ⟶ U}
    {L₂ : U ⟶ Q.obj k₀} {R₁ : P' ⟶ V} {R₂ : V ⟶ Q.obj k₃} {μ₁ : k₀ ⟶ k₁} {ν : k₁ ⟶ k₂}
    {μ₂ : k₃ ⟶ k₂} {μ₂' : k₂ ⟶ k₃}
    (hA : a₁ ≫ a₂ ≫ c₁ = L₁ ≫ L₂ ≫ Q.map μ₁)
    (hB : b₁ ≫ b₂ ≫ c₂ = R₁ ≫ R₂ ≫ Q.map μ₂)
    (hC : γ ≫ c₂ = c₁ ≫ Q.map ν) (hb₁ : b₁' ≫ b₁ = 𝟙 _) (hb₂ : b₂' ≫ b₂ = 𝟙 _)
    (hμ : μ₂ ≫ μ₂' = 𝟙 _) :
    (a₁ ≫ a₂) ≫ (γ ≫ b₂' ≫ b₁') ≫ R₁ ≫ R₂ = L₁ ≫ L₂ ≫ Q.map (μ₁ ≫ ν ≫ μ₂') := by
  have hB' : b₂' ≫ b₁' ≫ R₁ ≫ R₂ = c₂ ≫ Q.map μ₂' := by
    have h : R₁ ≫ R₂ = b₁ ≫ b₂ ≫ c₂ ≫ Q.map μ₂' := by
      rw [reassoc_of% hB, ← Q.map_comp, hμ, Q.map_id, Category.comp_id]
    rw [h, reassoc_of% hb₁, reassoc_of% hb₂]
  simp only [Category.assoc, Q.map_comp]
  rw [hB', reassoc_of% hC, reassoc_of% hA]

/-- A morphism `x` with `a ≫ x ≫ b = c` for isomorphisms `a`, `b`, `c` is an isomorphism. -/
theorem isIso_of_comp_comp_eq {C : Type u₁} {_ : Category.{v₁} C} {A B C' D : C} {a : A ⟶ B}
    {x : B ⟶ C'} {b : C' ⟶ D} {c : A ⟶ D} (h : a ≫ x ≫ b = c) [IsIso a] [IsIso b] [IsIso c] :
    IsIso x := by
  have : x = inv a ≫ c ≫ inv b := by
    rw [← h]
    simp
  rw [this]
  infer_instance

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  pushforwardMapHomotopy pullbackMapHomotopy pullbackAdjPushforwardMapHomotopy sourceQuasiIso)

universe v u w

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{v, u, w}}
  [X'.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y'.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y'.J AddCommGrpCat.{w}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} {h₁ h₂ : RingedToposHom X' Y}

/-- The module base change map `f_* ⋙ g^* ⟶ (g')^* ⋙ f'_*` of a square `m` of pullbacks of
modules, the mate of `m` for the adjunctions of Stacks 03D7, applied termwise to a complex. -/
def moduleSquareBaseChangeComplex
    (m : g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ⟶
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules)
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      ((pushforwardModules f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f n := (mateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules f')
    (TwoSquare.mk _ _ _ _ m)).natTrans.app (I.X n)
  comm' i j _ := ((mateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules f')
    (TwoSquare.mk _ _ _ _ m)).natTrans.naturality (I.d i j)).symm

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The component in degree `n` of `moduleSquareBaseChangeComplex m I` is the mate of `m` at the
term `I.X n`. -/
@[simp]
theorem moduleSquareBaseChangeComplex_f
    (m : g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ⟶
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules)
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (moduleSquareBaseChangeComplex m I).f n =
      (mateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules f')
        (TwoSquare.mk _ _ _ _ m)).natTrans.app (I.X n) :=
  rfl

/-- A square `m` of pullbacks of modules, applied termwise to a complex of `𝒪_Y`-modules. -/
def moduleSquareComplex
    (m : g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ⟶
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules)
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (f'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      (g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f n := m.app (P.X n)
  comm' i j _ := (m.naturality (P.d i j)).symm

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The component in degree `n` of `moduleSquareComplex m P` is `m` at the term `P.X n`. -/
@[simp]
theorem moduleSquareComplex_f
    (m : g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ⟶
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules)
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) : (moduleSquareComplex m P).f n = m.app (P.X n) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The termwise module base change map has the adjoint property of a base change map: `(f')^*`
of it, followed by the counit of `(f')^* ⊣ f'_*`, is `m` followed by `(g')^*` of the counit of
`f^* ⊣ f_*`. -/
theorem moduleSquareBaseChangeComplex_comp_counit
    (m : g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ⟶
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules)
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (f'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (moduleSquareBaseChangeComplex m I) ≫
      (NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f').counit
        (ComplexShape.up ℤ)).app
          ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) =
      moduleSquareComplex m
          (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f).counit
            (ComplexShape.up ℤ)).app I) := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, moduleSquareBaseChangeComplex_f, moduleSquareComplex_f]
  exact mateEquiv_counit _ _ _ (I.X n)

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The square of homotopy categories built from the compositors and `e₁`, `ν`, `e₂`, at the class
of a complex, is the class of the termwise square of pullbacks of modules. -/
theorem compositionSquareHomotopy_app_quotient
    (e₁ : (g.comp f').toModulesHom.pullbackModules ≅ h₁.toModulesHom.pullbackModules)
    (e₂ : (f.comp g').toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (ν : h₁.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackMapHomotopyCompIso f' g ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e₁ (ComplexShape.up ℤ)).hom.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (Stacks.Homology.mapHomotopyCategoryIso ν (ComplexShape.up ℤ)).hom.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (pullbackMapHomotopyCompIso g' f ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e₂ (ComplexShape.up ℤ)).inv.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) =
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (moduleSquareComplex (((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫ ν.hom ≫
        ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv)
          (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The counit of the adjunction `f^* ⊣ f_*` on unbounded homotopy categories, at the class of a
complex, is the class of the termwise counit. -/
theorem counit_pullbackAdjPushforwardMapHomotopy_app_quotient
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackAdjPushforwardMapHomotopy f).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f).counit
          (ComplexShape.up ℤ)).app I) := by
  unfold pullbackAdjPushforwardMapHomotopy
  rfl

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y'.J AddCommGrpCat.{w}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)] [HasSheafify Y'.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The counit of the adjunction `(f')^* ⊣ f'_*` on unbounded homotopy categories, at the
pullback along `g'` of the class of a complex, is the class of the termwise counit. -/
theorem counit_pullbackAdjPushforwardMapHomotopy_app_pullbackMapHomotopy_quotient
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackAdjPushforwardMapHomotopy f').counit.app
        ((pullbackMapHomotopy g').obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f').counit
          (ComplexShape.up ℤ)).app
            ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
  counit_pullbackAdjPushforwardMapHomotopy_app_quotient (f := f') _

omit [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J (Type w)] [HasSheafify X.J (Type w)]
  [HasSheafify Y'.J (Type w)] [HasSheafify Y.J (Type w)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The termwise module base change map, on homotopy categories, has the adjoint property of a
base change map for the square of homotopy categories of
`compositionSquareHomotopy_app_quotient`. -/
theorem moduleSquareBaseChangeComplex_quotient_comp_counit
    (e₁ : (g.comp f').toModulesHom.pullbackModules ≅ h₁.toModulesHom.pullbackModules)
    (e₂ : (f.comp g').toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (ν : h₁.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackMapHomotopy f').map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (moduleSquareBaseChangeComplex (((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫ ν.hom ≫
          ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv) I)) ≫
      (pullbackAdjPushforwardMapHomotopy f').counit.app
        ((pullbackMapHomotopy g').obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) =
    ((pullbackMapHomotopyCompIso f' g ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e₁ (ComplexShape.up ℤ)).hom.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (Stacks.Homology.mapHomotopyCategoryIso ν (ComplexShape.up ℤ)).hom.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (pullbackMapHomotopyCompIso g' f ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e₂ (ComplexShape.up ℤ)).inv.app
          ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      (pullbackMapHomotopy g').map ((pullbackAdjPushforwardMapHomotopy f).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  rw [counit_pullbackAdjPushforwardMapHomotopy_app_pullbackMapHomotopy_quotient,
    counit_pullbackAdjPushforwardMapHomotopy_app_quotient,
    compositionSquareHomotopy_app_quotient]
  simp only [Functor.mapHomotopyCategory_map]
  exact congrArg _ (moduleSquareBaseChangeComplex_comp_counit _ I)

omit [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **The derived 2-cell of the square is compatible with the comparisons** of Stacks 06YY, through
the square of homotopy categories of `compositionSquareHomotopy_app_quotient`. -/
theorem compositionSquare_comparison
    (e₁ : (g.comp f').toModulesHom.pullbackModules ≅ h₁.toModulesHom.pullbackModules)
    (e₂ : (f.comp g').toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (ν : h₁.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (C : derivedPullback h₂ ≅ derivedPullback h₁)
    (hC :
      letI := HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
      letI := HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ∀ K, C.inv.app (DerivedCategory.Qh.obj K) ≫ (derivedPullbackComparison h₂).app K =
        (derivedPullbackComparison h₁).app K ≫
          DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso ν
            (ComplexShape.up ℤ)).hom.app K))
    (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (derivedPullbackCompIso f' g ≪≫ derivedPullbackIsoOfPullbackModulesIso e₁).hom.app
        (DerivedCategory.Qh.obj K) ≫
      ((derivedPullbackCompIso g' f ≪≫ derivedPullbackIsoOfPullbackModulesIso e₂) ≪≫ C).inv.app
        (DerivedCategory.Qh.obj K) ≫
      (derivedPullback g').map ((derivedPullbackComparison f).app K) ≫
      (derivedPullbackComparison g').app ((pullbackMapHomotopy f).obj K) =
    (derivedPullback f').map ((derivedPullbackComparison g).app K) ≫
      (derivedPullbackComparison f').app ((pullbackMapHomotopy g).obj K) ≫
      DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f' g ≪≫
          Stacks.Homology.mapHomotopyCategoryIso e₁ (ComplexShape.up ℤ)).hom.app K ≫
        (Stacks.Homology.mapHomotopyCategoryIso ν (ComplexShape.up ℤ)).hom.app K ≫
        (pullbackMapHomotopyCompIso g' f ≪≫
          Stacks.Homology.mapHomotopyCategoryIso e₂ (ComplexShape.up ℤ)).inv.app K) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  have hA := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app f' g e₁ K
  have hB := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app g' f e₂ K
  exact Stacks.CategoryTheory.BaseChange.comp_comp_eq_of_comparisons DerivedCategory.Qh hA hB
    (hC K) (Iso.inv_hom_id_app (derivedPullbackCompIso g' f) _) (Iso.inv_hom_id_app _ _)
    (Iso.hom_inv_id_app _ _)

/-- **The derived base change map of the square at a complex**, preceded by `Lg^*` of the unit
`f_* I ⟶ Rf_* I` and followed by `Rf'_*` of the comparison `L(g')^* I ⟶ (g')^* I`, is the
comparison `Lg^* f_* I ⟶ g^* f_* I`, followed by the termwise module base change map and the unit
`f'_* (g')^* I ⟶ Rf'_* (g')^* I`. -/
theorem compositionSquare_baseChange_fac
    (e₁ : (g.comp f').toModulesHom.pullbackModules ≅ h₁.toModulesHom.pullbackModules)
    (e₂ : (f.comp g').toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (ν : h₁.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (C : derivedPullback h₂ ≅ derivedPullback h₁)
    (hC :
      letI := HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
      letI := HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ∀ K, C.inv.app (DerivedCategory.Qh.obj K) ≫ (derivedPullbackComparison h₂).app K =
        (derivedPullbackComparison h₁).app K ≫
          DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso ν
            (ComplexShape.up ℤ)).hom.app K))
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (derivedPullback g).map (((pushforwardOnHomotopy f).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso X)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIso f' g ≪≫ derivedPullbackIsoOfPullbackModulesIso e₁)
        ((derivedPullbackCompIso g' f ≪≫ derivedPullbackIsoOfPullbackModulesIso e₂) ≪≫ C)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) =
    (derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (moduleSquareBaseChangeComplex (((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫ ν.hom ≫
          ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv) I)) ≫
      ((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X')).app ((pullbackMapHomotopy g').obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  exact Stacks.CategoryTheory.BaseChange.map_fac_of_counit_fac
    (pullbackAdjPushforwardMapHomotopy f) (pullbackAdjPushforwardMapHomotopy f')
    (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIso f' g ≪≫ derivedPullbackIsoOfPullbackModulesIso e₁)
    ((derivedPullbackCompIso g' f ≪≫ derivedPullbackIsoOfPullbackModulesIso e₂) ≪≫ C)
    (derivedPullbackComparison f) (derivedPullbackComparison f')
    (derivedPullbackComparison g) (derivedPullbackComparison g')
    ((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh (sourceQuasiIso X))
    ((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh (sourceQuasiIso X'))
    (derivedAdjunction_counit_fac f) (derivedAdjunction_counit_fac f')
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) _
    (compositionSquare_comparison e₁ e₂ ν C hC _)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleSquareBaseChangeComplex
      (((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫ ν.hom ≫
        ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv) I))
    (moduleSquareBaseChangeComplex_quotient_comp_counit e₁ e₂ ν I)

/-- **Unbounded base change for a square whose 2-cell is built from compositors.** Let the
derived 2-cell of a commutative square of ringed topoi be given as Stacks 0D6D along `g ∘ f'`,
followed by an identification `e₁` of pullbacks, on one side, and Stacks 0D6D along `f ∘ g'`,
followed by `e₂` and the renaming along an equality `h₂ = h₁` of morphisms, on the other. If the
pullbacks along `g` and `g'` are exact, `(g')^*` keeps K-injective complexes K-injective, and the
module base change map of the underived square is an isomorphism, then the derived base change
map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is an isomorphism for every `K`.

This is `AlgebraicGeometry.RingedToposHom.TwoIso.isIso_derivedBaseChange_of_isIso_moduleBaseChange`
for a 2-cell which is not the one of a 2-isomorphism of morphisms of ringed topoi. -/
theorem isIso_derivedBaseChange_of_isIso_compositionSquare
    [PreservesFiniteLimits g.toModulesHom.pullbackModules]
    [PreservesFiniteLimits g'.toModulesHom.pullbackModules]
    (hK : ∀ I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (e₁ : (g.comp f').toModulesHom.pullbackModules ≅ h₁.toModulesHom.pullbackModules)
    (e₂ : (f.comp g').toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)
    (hh : h₂ = h₁)
    (hb : IsIso (mateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules f')
      (TwoSquare.mk _ _ _ _ (((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫
        (eqToIso (congrArg (fun φ : RingedToposHom X' Y ↦ φ.toModulesHom.pullbackModules)
          hh.symm)).hom ≫ ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv))).natTrans)
    (K :
      letI := HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    @IsIso _ _ _ _ (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f)
      (derivedAdjunction f')
      (derivedPullbackCompIso f' g ≪≫ derivedPullbackIsoOfPullbackModulesIso e₁)
      ((derivedPullbackCompIso g' f ≪≫ derivedPullbackIsoOfPullbackModulesIso e₂) ≪≫
        eqToIso (congrArg (fun φ : RingedToposHom X' Y ↦ derivedPullback φ) hh)) K) := by
  subst hh
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh K
  refine Stacks.CategoryTheory.BaseChange.isIso_map_of_iso _ _ _ _ e.symm ?_
  let ν : h₂.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules :=
    eqToIso (congrArg (fun φ : RingedToposHom X' Y ↦ φ.toModulesHom.pullbackModules)
      (rfl : h₂ = h₂))
  let C : derivedPullback h₂ ≅ derivedPullback h₂ :=
    eqToIso (congrArg (fun φ : RingedToposHom X' Y ↦ derivedPullback φ) (rfl : h₂ = h₂))
  have hC : ∀ K, C.inv.app (DerivedCategory.Qh.obj K) ≫ (derivedPullbackComparison h₂).app K =
      (derivedPullbackComparison h₂).app K ≫
        DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso ν
          (ComplexShape.up ℤ)).hom.app K) := by
    intro K
    simp [C, ν, Stacks.Homology.mapHomotopyCategoryIso]
  have hfac := compositionSquare_baseChange_fac e₁ e₂ ν C hC I
  generalize hm : ((pullbackModulesCompIso f' g).symm ≪≫ e₁).hom ≫ ν.hom ≫
    ((pullbackModulesCompIso g' f).symm ≪≫ e₂).inv = m at hfac
  have h1 : IsIso (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ I hI
  have h2 : IsIso ((derivedPullbackComparison g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    isIso_derivedPullbackComparison_app g' ⊤ hasResolutions_top
      (pullbackInvertsQuasiIso_top g') _ trivial
  have h3 : IsIso ((derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
    isIso_derivedPullbackComparison_app g ⊤ hasResolutions_top
      (pullbackInvertsQuasiIso_top g) _ trivial
  have : IsIso (moduleSquareBaseChangeComplex m I) := by
    have : ∀ n, IsIso ((moduleSquareBaseChangeComplex m I).f n) := fun n ↦ by
      rw [moduleSquareBaseChangeComplex_f, ← hm]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have h4 : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (moduleSquareBaseChangeComplex m I))) :=
    Functor.map_isIso _ _
  have h5 : IsIso (((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X')).app ((pullbackMapHomotopy g').obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ _ (hK I hI)
  exact @Stacks.CategoryTheory.BaseChange.isIso_of_comp_comp_eq _ _ _ _ _ _ _ _ _ _ hfac
    (Functor.map_isIso _ _) (Functor.map_isIso _ _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h3 (@IsIso.comp_isIso _ _ _ _ _ _ _ h4 h5))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Canonical

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  pushforwardMapHomotopy pullbackMapHomotopy pullbackAdjPushforwardMapHomotopy sourceQuasiIso)

/-- The renaming of the pullback of modules along an equality of morphisms of algebraic spaces. -/
def smallEtalePullbackModulesCongr {X Y : AlgebraicSpaces B S hS} {a b : X ⟶ Y} (h : a = b) :
    (smallEtaleRingedToposHom B S hS a).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS b).toModulesHom.pullbackModules :=
  eqToIso (congrArg (fun c : X ⟶ Y ↦
    (smallEtaleRingedToposHom B S hS c).toModulesHom.pullbackModules) h)

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- The comparison of the two pullbacks of modules around a commutative square, built as the
derived 2-cell of `smallEtaleDerivedModuleBaseChangeMap` is: the compositors of Stacks 03D6 with
the transports of the compositor of algebraic spaces, and the renaming along the commutativity. -/
def smallEtalePullbackModulesSquare (w : g' ≫ f = f' ≫ g) :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS f').toModulesHom.pullbackModules ⟶
      (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules :=
  ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f')
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f' g).hom ≫
    (smallEtalePullbackModulesCongr w.symm).hom ≫
    ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g')
      (smallEtaleRingedToposHom B S hS f)).symm ≪≫ pullbackModulesCompTransport B S hS g' f).inv

/-- The square `smallEtalePullbackModulesSquare` is the square of the canonical form of
Stacks 03LX, `AlgebraicGeometry.Space.isIso_mateEquiv_smallEtaleToposPullbackCompIso_square`. -/
theorem smallEtalePullbackModulesSquare_eq (w : g' ≫ f = f' ≫ g) :
    smallEtalePullbackModulesSquare f g f' g' w =
      (smallEtaleToposPullbackCompIso f' g).hom ≫
        eqToHom (congrArg (fun m : X' ⟶ Y ↦
          (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) w.symm) ≫
        (smallEtaleToposPullbackCompIso g' f).inv := by
  simp only [smallEtalePullbackModulesSquare, smallEtaleToposPullbackCompIso,
    smallEtalePullbackModulesCongr, pullbackModulesCompTransport_eq_compTwoIso,
    eqToIso.hom]

/-- **The module base change map of the derived 2-cell is invertible** for a cartesian square
with `g` étale: Stacks 03LX in its canonical form,
`AlgebraicGeometry.Space.isIso_mateEquiv_smallEtaleToposPullbackCompIso_square`, read through
`smallEtalePullbackModulesSquare_eq`. -/
theorem isIso_mateEquiv_smallEtalePullbackModulesSquare {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hg : IsEtale B S hS g.hom) :
    IsIso (mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f'))
      (TwoSquare.mk _ _ _ _ (smallEtalePullbackModulesSquare f g f' g' sq.w))).natTrans := by
  simp only [smallEtalePullbackModulesSquare_eq]
  exact isIso_mateEquiv_smallEtaleToposPullbackCompIso_square g' f f' g sq hg

/-- Restriction along an étale morphism of algebraic spaces, read as the pullback of modules of
the morphism of small étale ringed topoi, carries K-injective complexes to K-injective complexes:
Stacks 08FI, `AlgebraicGeometry.Space.isKInjective_etaleModulePullback`, through Stacks 03LW. -/
theorem isKInjective_pullbackModules_mapHomologicalComplex_of_isEtale
    {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((smallEtaleRingedToposHom B S hS a).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have := etaleModulePullback_additive.{u, u} B S hS a ha
  have hE := isKInjective_etaleModulePullback B S hS a ha
    (etaleModuleLowerShriekAdjunction B S hS a ha) I hI
  refine (CochainComplex.isKInjective_iff_of_iso ?_).1 hE
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((pullbackModulesIsoModulePullback B S hS a ≪≫
      modulePullbackIsoEtaleModulePullback B S hS a ha).app (I.X n)).symm)
    (fun i j _ ↦ ((pullbackModulesIsoModulePullback B S hS a ≪≫
      modulePullbackIsoEtaleModulePullback B S hS a ha).inv.naturality (I.d i j)).symm)

/-- **The canonical form of Stacks 08GE.** For a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of algebraic spaces with `g` étale, the base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` — the mate, under the derived
adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ Rf'_*`, of the identification of the two iterated derived
pullbacks around the square — is an isomorphism for every `K` in `D(𝒪_X)`. -/
theorem isIso_smallEtaleDerivedModuleBaseChangeMap (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) :
    ∀ K, @IsIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w K) := by
  intro K
  have hg' : IsEtale B S hS g'.hom := isEtale_of_isPullback B S hS f' g' g f sq.flip hg
  have := preservesFiniteLimits_pullbackModules_of_isEtale B S hS g hg
  have := preservesFiniteLimits_pullbackModules_of_isEtale B S hS g' hg'
  exact RingedToposHom.isIso_derivedBaseChange_of_isIso_compositionSquare
    (isKInjective_pullbackModules_mapHomologicalComplex_of_isEtale g' hg')
    (pullbackModulesCompTransport B S hS f' g) (pullbackModulesCompTransport B S hS g' f)
    (congrArg (smallEtaleRingedToposHom B S hS) sq.w)
    (isIso_mateEquiv_smallEtalePullbackModulesSquare sq hg) K

end Canonical

end AlgebraicGeometry.Space

end
