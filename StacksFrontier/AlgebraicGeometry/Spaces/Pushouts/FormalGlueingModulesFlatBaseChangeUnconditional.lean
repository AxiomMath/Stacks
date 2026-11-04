module

public import Mathlib.CategoryTheory.CatCommSq
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesQCohEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Stacks 0AEZ: flat base change of formal glueing of quasi-coherent modules

Let `f : Y ⟶ X`, `Z ⊆ X` be the formal glueing situation of Stacks 0AEV, with `U = X ∖ Z`,
`V = Y ∖ f⁻¹(Z)`, `j : U ⟶ X`, `j' : V ⟶ Y`, and let `g : X' ⟶ X` be a flat morphism of
algebraic spaces, with `Z' = X' ×_X Z` and `Y' = X' ×_X Y`.  Stacks 0AEZ asserts that the
pullbacks `QCoh(𝒪_X) ⥤ QCoh(𝒪_{X'})` and `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` are compatible
with the functors of Stacks 0AEW and of Stacks 0AEX.  This file proves both compatibilities,
as natural isomorphisms of functors between the categories the source names, with no hypothesis
beyond the situation:

* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.glueingModulesFunctorPullbackIso`:
  `Φ_X ⋙ g^* ≅ g^* ⋙ Φ_{X'}` for the functors `Φ` of Stacks 0AEW, as functors
  `QCoh(𝒪_X) ⥤ QCoh(Y' → X', Z')`;
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.glueingKernelFunctorPullbackIso`:
  `Ψ_X ⋙ g^* ≅ g^* ⋙ Ψ_{X'}` for the functors `Ψ` of Stacks 0AEX, as functors
  `QCoh(Y → X, Z) ⥤ QCoh(𝒪_{X'})`;
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModulesFunctorBaseChangeIso` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelFunctorBaseChangeIso`: the same
  for the base change `AlgebraicGeometry.Space.FormalGlueingSituation.baseChange` of the
  situation along a flat morphism `k : X' ⟶ X`, constructed rather than given.

Here `g^*` on `QCoh(𝒪_X)` is `AlgebraicGeometry.Space.quasicoherentPullbackFunctor` (Stacks 03GA,
proved for every morphism), and `g^*` on glueing data is
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.glueingDataPullback`, the
restriction of `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.pullbackGlueingComma`
to glueing data, which is a glueing triple again by Stacks 03GA for `U' ⟶ U` and `Y' ⟶ Y`.
So no inverse-image factor of Stacks 03DO is used.

## The compatibility with Stacks 0AEW

On the two module components the isomorphism is the comparison of Stacks 03LU over the two faces
of the cube `V' ⟶ U', Y' ⟶ X'` over `V ⟶ U, Y ⟶ X` meeting `U'` and `Y'`.  That it is a
morphism of glueing triples — the overlap-isomorphism component — is a coherence between the
comparisons of the six faces of the cube: `CategoryTheory.cube_comparison_coherence`.  It is
proved for an abstract system of inverse images and comparisons: every face comparison is written
`T⁻¹ ≫ T` through the diagonal of its face
(`AlgebraicGeometry.Space.modulePullbackSquareComparison_eq`), and the six faces are linked
through the long diagonal `V' ⟶ X` by six instances of the
associativity coherence of Stacks 03LU,
`AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_assoc`.

## The compatibility with Stacks 0AEX

The functors of Stacks 0AEW are equivalences with quasi-inverses the functors of Stacks 0AEX, by
Stacks 0AF0 (`AlgebraicGeometry.Space.FormalGlueingSituation.isIso_glueingAdjunction_unit_counit`),
whose proof uses neither 0AEZ nor anything after it.  The compatibility with Stacks 0AEX is the
compatibility with Stacks 0AEW transported to the quasi-inverses, `CategoryTheory.CatCommSq.hInv`.
In particular flatness of `g` is used only as the hypothesis of the tag, as the field
`flat_g` of `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange`; the direct proof
the source indicates, through Stacks 073K, is not needed.

## Implementation notes

Every identity between morphisms of sheaves of modules is proved for abstract categories and
functors and then instantiated, and the hypotheses of the instantiation are collected in the
single theorem
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.cubeComparisonHyp`.  Stated or
checked directly at the concrete module categories, such identities reach the kernel as
comparisons of objects `(P ⋙ Q).obj M` and `Q.obj (P.obj M)` of inverse images, and the kernel
then unfolds `AlgebraicGeometry.Space.modulePullback` instead of the composite, which does not
finish; this is the measurement recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/FormalGlueingModulesFlatBaseChange.lean`.  For the
same reason the equivalence of Stacks 0AF0 is built by
`CategoryTheory.Adjunction.toEquivalenceOfIsIso` from the two invertibility statements, rather
than through instance search.

## References

* [Stacks Project, Tag 0AEZ](https://stacks.math.columbia.edu/tag/0AEZ)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type*} [Category* C] {C' : Type*} [Category* C'] (P : ObjectProperty C)
  (Q : ObjectProperty C')

/-- A functor carrying the objects with the property `P` to objects with the property `Q`,
restricted to the two full subcategories. -/
def mapFullSubcategory (F : C ⥤ C') (h : ∀ X, P X → Q (F.obj X)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) fun X => h X.obj X.property

/-- The restriction of `F` to the full subcategories, followed by the inclusion, is the inclusion
followed by `F`. -/
def mapFullSubcategoryCompιIso (F : C ⥤ C') (h : ∀ X, P X → Q (F.obj X)) :
    P.mapFullSubcategory Q F h ⋙ Q.ι ≅ P.ι ⋙ F :=
  Q.liftCompιIso _ _

end ObjectProperty

namespace Functor

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  {E : Type*} [Category* E] {E' : Type*} [Category* E']

/-- Precomposing a functor of the shape `CategoryTheory.Functor.toComma` with `H` is again of that
shape. -/
def compToCommaIso {L : A ⥤ T} {R : B ⥤ T} (H : E' ⥤ E) (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ≅ G ⋙ R) :
    H ⋙ toComma F G α.hom ≅ toComma (H ⋙ F) (H ⋙ G) (isoWhiskerLeft H α).hom :=
  Iso.refl _

variable {A' : Type*} [Category* A'] {B' : Type*} [Category* B'] {T' : Type*} [Category* T']

/-- An isomorphism from the image under `CategoryTheory.Comma.map` of a functor of the shape
`CategoryTheory.Functor.toComma` to a functor of that shape precomposed with `H`, from
isomorphisms of the two components compatible with the transformations. -/
def toCommaCompMapIsoMk {L : A ⥤ T} {R : B ⥤ T} {L' : A' ⥤ T'} {R' : B' ⥤ T'}
    {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {K : T ⥤ T'} (α : F₁ ⋙ L' ⟶ L ⋙ K) (β : R ⋙ K ⟶ F₂ ⋙ R')
    {F : E ⥤ A} {G : E ⥤ B} (γ : F ⋙ L ⟶ G ⋙ R) {H : E ⥤ E'} {F' : E' ⥤ A'}
    {G' : E' ⥤ B'} (γ' : F' ⋙ L' ⟶ G' ⋙ R') (e₁ : F ⋙ F₁ ≅ H ⋙ F') (e₂ : G ⋙ F₂ ≅ H ⋙ G')
    (h : ∀ X, L'.map (e₁.hom.app X) ≫ γ'.app (H.obj X) =
      α.app (F.obj X) ≫ K.map (γ.app X) ≫ β.app (G.obj X) ≫ R'.map (e₂.hom.app X)) :
    toComma F G γ ⋙ Comma.map α β ≅ H ⋙ toComma F' G' γ' :=
  NatIso.ofComponents
    (fun X => Comma.isoMk (e₁.app X) (e₂.app X) (by simpa using h X))
    (fun f => by
      ext
      · simpa [Comma.isoMk] using e₁.hom.naturality f
      · simpa [Comma.isoMk] using e₂.hom.naturality f)

end Functor

/-- The equivalence of categories given by an adjunction whose unit and counit are invertible,
with the invertibility given as hypotheses rather than as instances. -/
def Adjunction.toEquivalenceOfIsIso {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) (h₁ : IsIso adj.unit) (h₂ : IsIso adj.counit) : C ≌ D :=
  haveI := h₁
  haveI := h₂
  adj.toEquivalence

end CategoryTheory

namespace CategoryTheory

/-! ### The coherence of a cube of inverse images, for an abstract system of inverse images -/

section CubeCoherence

variable {CX CU CY CV CX' CU' CY' CV' : Type*} [Category* CX] [Category* CU] [Category* CY]
  [Category* CV] [Category* CX'] [Category* CU'] [Category* CY'] [Category* CV']
  {Pj : CX ⥤ CU} {Pf : CX ⥤ CY} {PjV : CY ⥤ CV} {PfV : CU ⥤ CV} {Pg : CX ⥤ CX'}
  {PgU : CU ⥤ CU'} {PgY : CY ⥤ CY'} {PgV : CV ⥤ CV'} {Pj' : CX' ⥤ CU'} {Pf' : CX' ⥤ CY'}
  {PjV' : CY' ⥤ CV'} {PfV' : CU' ⥤ CV'} {PkU : CX ⥤ CU'} {PkY : CX ⥤ CY'} {PkV : CY ⥤ CV'}
  {PkO : CU ⥤ CV'} {PkD : CX ⥤ CV} {PkD' : CX' ⥤ CV'} {Pr : CX ⥤ CV'}

/-- **The coherence of a cube of inverse images.**  Consider the inverse images along the twelve
edges of a commutative cube, along the diagonals of its six faces, and along its long diagonal,
together with the comparisons `T` of the inverse image along a diagonal of a face with the
composites along the two paths of that face, and the comparisons `R` of the inverse image along the
long diagonal with the composites through the six face diagonals.  If the `R` and the `T` satisfy
the six associativity coherences `e₁, …, e₆`, then the comparisons `T⁻¹ ≫ T` of the six faces
compose to the same comparison around the two halves of the cube. -/
theorem cube_comparison_coherence (TU₁ : PkU ≅ Pj ⋙ PgU) (TU₂ : PkU ≅ Pg ⋙ Pj')
    (TY₁ : PkY ≅ Pf ⋙ PgY) (TY₂ : PkY ≅ Pg ⋙ Pf') (TV₁ : PkV ≅ PjV ⋙ PgV)
    (TV₂ : PkV ≅ PgY ⋙ PjV') (TO₁ : PkO ≅ PgU ⋙ PfV') (TO₂ : PkO ≅ PfV ⋙ PgV)
    (TD₁ : PkD ≅ Pj ⋙ PfV) (TD₂ : PkD ≅ Pf ⋙ PjV) (TD'₁ : PkD' ≅ Pj' ⋙ PfV')
    (TD'₂ : PkD' ≅ Pf' ⋙ PjV') (R₁ : Pr ≅ PkY ⋙ PjV') (R₂ : Pr ≅ Pg ⋙ PkD')
    (R₃ : Pr ≅ PkU ⋙ PfV') (R₄ : Pr ≅ Pf ⋙ PkV) (R₅ : Pr ≅ PkD ⋙ PgV) (R₆ : Pr ≅ Pj ⋙ PkO)
    (e₁ : ∀ M, PjV'.map (TY₂.inv.app M) ≫ R₁.inv.app M =
      TD'₂.inv.app (Pg.obj M) ≫ R₂.inv.app M)
    (e₂ : ∀ M, PfV'.map (TU₂.inv.app M) ≫ R₃.inv.app M =
      TD'₁.inv.app (Pg.obj M) ≫ R₂.inv.app M)
    (e₃ : ∀ M, PjV'.map (TY₁.inv.app M) ≫ R₁.inv.app M =
      TV₂.inv.app (Pf.obj M) ≫ R₄.inv.app M)
    (e₄ : ∀ M, PgV.map (TD₂.inv.app M) ≫ R₅.inv.app M =
      TV₁.inv.app (Pf.obj M) ≫ R₄.inv.app M)
    (e₅ : ∀ M, PgV.map (TD₁.inv.app M) ≫ R₅.inv.app M =
      TO₂.inv.app (Pj.obj M) ≫ R₆.inv.app M)
    (e₆ : ∀ M, PfV'.map (TU₁.inv.app M) ≫ R₃.inv.app M =
      TO₁.inv.app (Pj.obj M) ≫ R₆.inv.app M) (M : CX) :
    PfV'.map (TU₁.inv.app M ≫ TU₂.hom.app M) ≫
        (TD'₁.inv.app (Pg.obj M) ≫ TD'₂.hom.app (Pg.obj M)) =
      (TO₁.inv.app (Pj.obj M) ≫ TO₂.hom.app (Pj.obj M)) ≫
        PgV.map (TD₁.inv.app M ≫ TD₂.hom.app M) ≫
          (TV₁.inv.app (Pf.obj M) ≫ TV₂.hom.app (Pf.obj M)) ≫
            PjV'.map (TY₁.inv.app M ≫ TY₂.hom.app M) := by
  rw [← cancel_mono (PjV'.map (TY₂.inv.app M) ≫ R₁.inv.app M)]
  simp only [Category.assoc]
  conv_lhs =>
    rw [e₁ M, Iso.hom_inv_id_app_assoc, ← e₂ M, ← Functor.map_comp_assoc PfV']
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  conv_rhs =>
    rw [← Functor.map_comp_assoc PjV']
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [e₃ M, Iso.hom_inv_id_app_assoc, ← e₄ M, ← Functor.map_comp_assoc PgV]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [e₅ M, Iso.hom_inv_id_app_assoc, ← e₆ M]

/-- The hypotheses of `CategoryTheory.cubeToCommaIso`: the six associativity coherences of the
comparisons `T` and `R` along the diagonals of the faces and the long diagonal of a cube of
inverse images, and the factorization of the six face comparisons `S` through the face
diagonals. -/
structure CubeComparisonHyp (SU : Pj ⋙ PgU ≅ Pg ⋙ Pj') (SY : Pf ⋙ PgY ≅ Pg ⋙ Pf')
    (SV : PjV ⋙ PgV ≅ PgY ⋙ PjV') (SO : PgU ⋙ PfV' ≅ PfV ⋙ PgV) (SD : Pj ⋙ PfV ≅ Pf ⋙ PjV)
    (SD' : Pj' ⋙ PfV' ≅ Pf' ⋙ PjV') (TU₁ : PkU ≅ Pj ⋙ PgU) (TU₂ : PkU ≅ Pg ⋙ Pj')
    (TY₁ : PkY ≅ Pf ⋙ PgY) (TY₂ : PkY ≅ Pg ⋙ Pf') (TV₁ : PkV ≅ PjV ⋙ PgV)
    (TV₂ : PkV ≅ PgY ⋙ PjV') (TO₁ : PkO ≅ PgU ⋙ PfV') (TO₂ : PkO ≅ PfV ⋙ PgV)
    (TD₁ : PkD ≅ Pj ⋙ PfV) (TD₂ : PkD ≅ Pf ⋙ PjV) (TD'₁ : PkD' ≅ Pj' ⋙ PfV')
    (TD'₂ : PkD' ≅ Pf' ⋙ PjV') (R₁ : Pr ≅ PkY ⋙ PjV') (R₂ : Pr ≅ Pg ⋙ PkD')
    (R₃ : Pr ≅ PkU ⋙ PfV') (R₄ : Pr ≅ Pf ⋙ PkV) (R₅ : Pr ≅ PkD ⋙ PgV)
    (R₆ : Pr ≅ Pj ⋙ PkO) : Prop where
  e₁ : ∀ M, PjV'.map (TY₂.inv.app M) ≫ R₁.inv.app M = TD'₂.inv.app (Pg.obj M) ≫ R₂.inv.app M
  e₂ : ∀ M, PfV'.map (TU₂.inv.app M) ≫ R₃.inv.app M = TD'₁.inv.app (Pg.obj M) ≫ R₂.inv.app M
  e₃ : ∀ M, PjV'.map (TY₁.inv.app M) ≫ R₁.inv.app M = TV₂.inv.app (Pf.obj M) ≫ R₄.inv.app M
  e₄ : ∀ M, PgV.map (TD₂.inv.app M) ≫ R₅.inv.app M = TV₁.inv.app (Pf.obj M) ≫ R₄.inv.app M
  e₅ : ∀ M, PgV.map (TD₁.inv.app M) ≫ R₅.inv.app M = TO₂.inv.app (Pj.obj M) ≫ R₆.inv.app M
  e₆ : ∀ M, PfV'.map (TU₁.inv.app M) ≫ R₃.inv.app M = TO₁.inv.app (Pj.obj M) ≫ R₆.inv.app M
  hU : SU = TU₁.symm ≪≫ TU₂
  hY : SY = TY₁.symm ≪≫ TY₂
  hV : SV = TV₁.symm ≪≫ TV₂
  hO : SO = TO₁.symm ≪≫ TO₂
  hD : SD = TD₁.symm ≪≫ TD₂
  hD' : SD' = TD'₁.symm ≪≫ TD'₂

/-- **The comparison of the two ways around a cube of inverse images, on triples.**  Under
`CategoryTheory.CubeComparisonHyp`, the triples `(Pj M, Pf M, S_D)` of the bottom face, pushed to
the top face by `Comma.map S_O S_V`, are isomorphic to the triples `(Pj' (Pg M), Pf' (Pg M), S_D')`
of the top face, by `S_U` and `S_Y` on the two components; that these form a morphism of
triples is `CategoryTheory.cube_comparison_coherence`. -/
def cubeToCommaIso (SU : Pj ⋙ PgU ≅ Pg ⋙ Pj') (SY : Pf ⋙ PgY ≅ Pg ⋙ Pf')
    (SV : PjV ⋙ PgV ≅ PgY ⋙ PjV') (SO : PgU ⋙ PfV' ≅ PfV ⋙ PgV) (SD : Pj ⋙ PfV ≅ Pf ⋙ PjV)
    (SD' : Pj' ⋙ PfV' ≅ Pf' ⋙ PjV') (TU₁ : PkU ≅ Pj ⋙ PgU) (TU₂ : PkU ≅ Pg ⋙ Pj')
    (TY₁ : PkY ≅ Pf ⋙ PgY) (TY₂ : PkY ≅ Pg ⋙ Pf') (TV₁ : PkV ≅ PjV ⋙ PgV)
    (TV₂ : PkV ≅ PgY ⋙ PjV') (TO₁ : PkO ≅ PgU ⋙ PfV') (TO₂ : PkO ≅ PfV ⋙ PgV)
    (TD₁ : PkD ≅ Pj ⋙ PfV) (TD₂ : PkD ≅ Pf ⋙ PjV) (TD'₁ : PkD' ≅ Pj' ⋙ PfV')
    (TD'₂ : PkD' ≅ Pf' ⋙ PjV') (R₁ : Pr ≅ PkY ⋙ PjV') (R₂ : Pr ≅ Pg ⋙ PkD')
    (R₃ : Pr ≅ PkU ⋙ PfV') (R₄ : Pr ≅ Pf ⋙ PkV) (R₅ : Pr ≅ PkD ⋙ PgV) (R₆ : Pr ≅ Pj ⋙ PkO)
    (H : CubeComparisonHyp SU SY SV SO SD SD' TU₁ TU₂ TY₁ TY₂ TV₁ TV₂ TO₁ TO₂ TD₁ TD₂ TD'₁ TD'₂
      R₁ R₂ R₃ R₄ R₅ R₆) :
    Functor.toComma Pj Pf SD.hom ⋙ Comma.map SO.hom SV.hom ≅
      Pg ⋙ Functor.toComma Pj' Pf' SD'.hom :=
  Functor.toCommaCompMapIsoMk _ _ _ _ SU SY fun M => by
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, hU, hY, hV, hO, hD, hD'⟩ := H
    subst hU hY hV hO hD hD'
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    exact cube_comparison_coherence TU₁ TU₂ TY₁ TY₂ TV₁ TV₂ TO₁ TO₂ TD₁ TD₂ TD'₁ TD'₂
      R₁ R₂ R₃ R₄ R₅ R₆ e₁ e₂ e₃ e₄ e₅ e₆ M

end CubeCoherence

section SquareComparison

variable {𝒞 : Type*} [Category* 𝒞] {Mod : 𝒞 → Type*} {instMod : ∀ X, Category* (Mod X)}
  (P : ∀ {X Y : 𝒞}, (X ⟶ Y) → (Mod Y ⥤ Mod X))
  (μ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z), P g ⋙ P f ≅ P (f ≫ g))

/-- For an abstract system of inverse images with composition comparisons `μ`, the comparison of
a commutative square obtained from `μ` along its two legs factors through any presentation of
its diagonal. -/
theorem squareComparison_eq {X Y X' Y' : 𝒞} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) {k : X' ⟶ Y} (h₁ : g' ≫ f = k)
    (h₂ : f' ≫ g = k) :
    μ g' f ≪≫ eqToIso (congrArg (fun m : X' ⟶ Y => P m) comm) ≪≫ (μ f' g).symm =
      (eqToIso (congrArg (fun m : X' ⟶ Y => P m) h₁.symm) ≪≫ (μ g' f).symm).symm ≪≫
        eqToIso (congrArg (fun m : X' ⟶ Y => P m) h₂.symm) ≪≫ (μ f' g).symm := by
  subst h₁
  ext N
  simp

end SquareComparison

end CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)

/-- The comparison of a commutative square is the inverse comparison along one leg followed by
the comparison along the other, through any presentation of the common diagonal. -/
theorem modulePullbackSquareComparison_eq {k : X' ⟶ Y} (h₁ : g' ≫ f = k) (h₂ : f' ≫ g = k) :
    modulePullbackSquareComparison f g f' g' comm =
      (modulePullbackTriangle B S hS h₁).symm ≪≫ modulePullbackTriangle B S hS h₂ :=
  squareComparison_eq (fun {_ _} m => modulePullback B S hS m)
    (fun a b => modulePullbackCompIso B S hS a b) f g f' g' comm h₁ h₂

end Square

namespace FormalGlueingSituation

/-- The glueing square of Stacks 0AEV commutes, read in the direction in which its two legs are
presented as factorizations of the composite `V ⟶ X`. -/
theorem cube_wD (D : FormalGlueingSituation B S hS) :
    D.openImmersionOver ≫ D.ambientMorphism = D.overlapRestriction ≫ D.openImmersion :=
  D.overlapRestriction_comp_openImmersion.symm

/-- **Stacks 0AF0**, as an equivalence: the functor of Stacks 0AEW is an equivalence
`QCoh(𝒪_X) ≌ QCoh(Y → X, Z)` with quasi-inverse the functor of Stacks 0AEX. -/
def glueingEquivalence (D : FormalGlueingSituation B S hS) :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ≌ D.moduleGlueingData :=
  D.glueingAdjunction.toEquivalenceOfIsIso D.isIso_glueingAdjunction_unit_counit.1
    D.isIso_glueingAdjunction_unit_counit.2

namespace FlatBaseChange

variable {D D' : FormalGlueingSituation B S hS} (c : FlatBaseChange D D')

/-- The face of the cube over `U`, as a factorization of `U' ⟶ X`. -/
theorem cube_wU : D'.openImmersion ≫ c.g = c.gU ≫ D.openImmersion := c.isPullback_U.w.symm

/-- The face of the cube over `Y`, as a factorization of `Y' ⟶ X`. -/
theorem cube_wY : D'.ambientMorphism ≫ c.g = c.gY ≫ D.ambientMorphism := c.isPullback_Y.w.symm

/-- The face of the cube over `V ⟶ Y`, as a factorization of `V' ⟶ Y`. -/
theorem cube_wV : D'.openImmersionOver ≫ c.gY = c.gV ≫ D.openImmersionOver :=
  c.isPullback_V.w.symm

/-- The face of the cube over `V ⟶ U`, as a factorization of `V' ⟶ U`. -/
theorem cube_wO : c.gV ≫ D.overlapRestriction = D'.overlapRestriction ≫ c.gU :=
  c.overlapRestriction_comm.symm

/-- The long diagonal `V' ⟶ X` of the cube through `V' ⟶ U`. -/
theorem cube_p5 : (D'.overlapRestriction ≫ c.gU) ≫ D.openImmersion =
    D'.overlapRestriction ≫ c.gU ≫ D.openImmersion := Category.assoc _ _ _

/-- The long diagonal `V' ⟶ X` of the cube through `V ⟶ X`. -/
theorem cube_p4 : c.gV ≫ D.overlapRestriction ≫ D.openImmersion =
    D'.overlapRestriction ≫ c.gU ≫ D.openImmersion := by
  rw [← Category.assoc, c.cube_wO, Category.assoc]

/-- The long diagonal `V' ⟶ X` of the cube through `V' ⟶ Y`. -/
theorem cube_p3 : (c.gV ≫ D.openImmersionOver) ≫ D.ambientMorphism =
    D'.overlapRestriction ≫ c.gU ≫ D.openImmersion := by
  rw [Category.assoc, cube_wD D, c.cube_p4]

/-- The long diagonal `V' ⟶ X` of the cube through `V' ⟶ X'`. -/
theorem cube_p1 : (D'.overlapRestriction ≫ D'.openImmersion) ≫ c.g =
    D'.overlapRestriction ≫ c.gU ≫ D.openImmersion := by
  rw [Category.assoc, c.cube_wU]

/-- The long diagonal `V' ⟶ X` of the cube through `Y' ⟶ X`. -/
theorem cube_r₁ : D'.openImmersionOver ≫ c.gY ≫ D.ambientMorphism =
    D'.overlapRestriction ≫ c.gU ≫ D.openImmersion := by
  rw [← c.cube_wY, ← Category.assoc, cube_wD D', c.cube_p1]

/-- The hypotheses of `CategoryTheory.cubeToCommaIso` for the cube of a flat base change of
formal glueing: the associativity coherence of Stacks 03LU and the factorization of the
comparisons of the six faces through their diagonals. -/
theorem cubeComparisonHyp :
    CubeComparisonHyp c.openImmersionComparison c.ambientMorphismComparison
    c.openImmersionOverComparison c.overlapRestrictionComparison D.overlapPullbackComparison
    D'.overlapPullbackComparison
    (modulePullbackTriangle B S hS (rfl : c.gU ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS c.cube_wU)
    (modulePullbackTriangle B S hS (rfl : c.gY ≫ D.ambientMorphism = _))
    (modulePullbackTriangle B S hS c.cube_wY)
    (modulePullbackTriangle B S hS (rfl : c.gV ≫ D.openImmersionOver = _))
    (modulePullbackTriangle B S hS c.cube_wV)
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ c.gU = _))
    (modulePullbackTriangle B S hS c.cube_wO)
    (modulePullbackTriangle B S hS (rfl : D.overlapRestriction ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS (cube_wD D))
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ D'.openImmersion = _))
    (modulePullbackTriangle B S hS (cube_wD D'))
    (modulePullbackTriangle B S hS c.cube_r₁) (modulePullbackTriangle B S hS c.cube_p1)
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ c.gU ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS c.cube_p3) (modulePullbackTriangle B S hS c.cube_p4)
    (modulePullbackTriangle B S hS c.cube_p5) :=
  ⟨(modulePullbackTriangle_inv_app_assoc B S hS (cube_wD D') c.cube_wY c.cube_r₁ c.cube_p1),
    (modulePullbackTriangle_inv_app_assoc B S hS rfl c.cube_wU rfl c.cube_p1),
    (modulePullbackTriangle_inv_app_assoc B S hS c.cube_wV rfl c.cube_r₁ c.cube_p3),
    (modulePullbackTriangle_inv_app_assoc B S hS rfl (cube_wD D) c.cube_p4 c.cube_p3),
    (modulePullbackTriangle_inv_app_assoc B S hS c.cube_wO rfl c.cube_p4 c.cube_p5),
    (modulePullbackTriangle_inv_app_assoc B S hS rfl rfl rfl c.cube_p5),
    (modulePullbackSquareComparison_eq _ _ _ _ _ rfl c.cube_wU),
    (modulePullbackSquareComparison_eq _ _ _ _ _ rfl c.cube_wY),
    (modulePullbackSquareComparison_eq _ _ _ _ _ rfl c.cube_wV),
    (modulePullbackSquareComparison_eq _ _ _ _ _ rfl c.cube_wO),
    (modulePullbackSquareComparison_eq D.openImmersion D.ambientMorphism
      D.openImmersionOver D.overlapRestriction D.overlapRestriction_comp_openImmersion rfl
      (cube_wD D)),
    (modulePullbackSquareComparison_eq D'.openImmersion D'.ambientMorphism
      D'.openImmersionOver D'.overlapRestriction D'.overlapRestriction_comp_openImmersion rfl
      (cube_wD D'))⟩

/-- **The compatibility of the pullback of glueing triples with the triple of Stacks 0AEW**, on
all `𝒪_X`-modules: the triple of a pulled-back module is the pullback of its triple, as functors
into the comma category of glueing triples over `X'`.  On the two module components it is the
comparison of Stacks 03LU over the two faces of the cube meeting `U'` and `Y'`; that it is a
morphism of triples is the coherence of the cube, `CategoryTheory.cube_comparison_coherence`,
for the inverse images of Stacks 03LU and the associativity coherence of their comparisons. -/
def glueingDiagramPullbackIso :
    D.glueingDiagram ⋙ c.pullbackGlueingComma ≅
      modulePullback B S hS c.g ⋙ D'.glueingDiagram :=
  cubeToCommaIso c.openImmersionComparison c.ambientMorphismComparison
    c.openImmersionOverComparison c.overlapRestrictionComparison D.overlapPullbackComparison
    D'.overlapPullbackComparison
    (modulePullbackTriangle B S hS (rfl : c.gU ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS c.cube_wU)
    (modulePullbackTriangle B S hS (rfl : c.gY ≫ D.ambientMorphism = _))
    (modulePullbackTriangle B S hS c.cube_wY)
    (modulePullbackTriangle B S hS (rfl : c.gV ≫ D.openImmersionOver = _))
    (modulePullbackTriangle B S hS c.cube_wV)
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ c.gU = _))
    (modulePullbackTriangle B S hS c.cube_wO)
    (modulePullbackTriangle B S hS (rfl : D.overlapRestriction ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS (cube_wD D))
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ D'.openImmersion = _))
    (modulePullbackTriangle B S hS (cube_wD D'))
    (modulePullbackTriangle B S hS c.cube_r₁) (modulePullbackTriangle B S hS c.cube_p1)
    (modulePullbackTriangle B S hS (rfl : D'.overlapRestriction ≫ c.gU ≫ D.openImmersion = _))
    (modulePullbackTriangle B S hS c.cube_p3) (modulePullbackTriangle B S hS c.cube_p4)
    (modulePullbackTriangle B S hS c.cube_p5)
    c.cubeComparisonHyp

/-- The compatibility of the pullback of glueing triples with the triple of Stacks 0AEW, on
quasi-coherent `𝒪_X`-modules and with values in the ambient comma category. -/
def quasicoherentGlueingDiagramPullbackIso :
    D.quasicoherentGlueingDiagram ⋙ c.pullbackGlueingComma ≅
      quasicoherentPullbackFunctor B S hS c.g ⋙ D'.quasicoherentGlueingDiagram :=
  Functor.isoWhiskerRight (Functor.compToCommaIso D.ambientInclusion _ _
      D.overlapPullbackComparison).symm c.pullbackGlueingComma ≪≫
    Functor.associator D.ambientInclusion D.glueingDiagram c.pullbackGlueingComma ≪≫
    Functor.isoWhiskerLeft D.ambientInclusion c.glueingDiagramPullbackIso ≪≫
    (Functor.associator D.ambientInclusion (modulePullback B S hS c.g)
      D'.glueingDiagram).symm ≪≫
    Functor.isoWhiskerRight
      (ObjectProperty.liftCompιIso _ _ _ :
        quasicoherentPullbackFunctor B S hS c.g ⋙ D'.ambientInclusion ≅
          D.ambientInclusion ⋙ modulePullback B S hS c.g).symm D'.glueingDiagram ≪≫
    Functor.associator (quasicoherentPullbackFunctor B S hS c.g) D'.ambientInclusion
      D'.glueingDiagram ≪≫
    Functor.isoWhiskerLeft (quasicoherentPullbackFunctor B S hS c.g)
      (Functor.compToCommaIso D'.ambientInclusion _ _ D'.overlapPullbackComparison)

/-- **The pullback `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` of Stacks 0AEZ**: a glueing triple
`(H, G, φ)` goes to `((g_U)^*H, (g_Y)^*G, ψ)`, where `ψ` is `(g_V)^*φ` read through the comparisons
of Stacks 03LU over the two faces of the cube meeting the overlap.  The two components are again
quasi-coherent by Stacks 03GA, which holds for every morphism of algebraic spaces. -/
def glueingDataPullback : D.moduleGlueingData ⥤ D'.moduleGlueingData :=
  ObjectProperty.mapFullSubcategory _ _ c.pullbackGlueingComma fun t ht =>
    ⟨c.isIso_pullbackGlueingComma_obj_hom t ht.1,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c.gU t.left ht.2.1,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c.gY t.right
        ht.2.2⟩

/-- **Stacks 0AEZ, compatibility with the functor of Stacks 0AEW.**  For the base change of the
formal glueing situation along a flat morphism `g : X' ⟶ X`, the pullback
`QCoh(𝒪_X) ⥤ QCoh(𝒪_{X'})` of Stacks 03GA and the pullback
`QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` of glueing triples commute with the functors
`QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` and `QCoh(𝒪_{X'}) ⥤ QCoh(Y' → X', Z')` of Stacks 0AEW. -/
@[stacks 0AEZ "compatibility with the functor of Tag 0AEW"]
def glueingModulesFunctorPullbackIso :
    D.glueingModulesFunctor ⋙ c.glueingDataPullback ≅
      quasicoherentPullbackFunctor B S hS c.g ⋙ D'.glueingModulesFunctor :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator D.glueingModulesFunctor c.glueingDataPullback (ObjectProperty.ι _) ≪≫
      Functor.isoWhiskerLeft D.glueingModulesFunctor
        (ObjectProperty.mapFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator D.glueingModulesFunctor (ObjectProperty.ι _)
        c.pullbackGlueingComma).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) c.pullbackGlueingComma ≪≫
      c.quasicoherentGlueingDiagramPullbackIso ≪≫
      Functor.isoWhiskerLeft (quasicoherentPullbackFunctor B S hS c.g)
        (ObjectProperty.liftCompιIso _ _ _).symm ≪≫
      (Functor.associator (quasicoherentPullbackFunctor B S hS c.g) D'.glueingModulesFunctor
        (ObjectProperty.ι _)).symm)

/-- **Stacks 0AEZ, compatibility with the functor of Stacks 0AEX.**  For the base change of the
formal glueing situation along a flat morphism `g : X' ⟶ X`, the pullback
`QCoh(𝒪_X) ⥤ QCoh(𝒪_{X'})` of Stacks 03GA and the pullback
`QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` of glueing triples commute with the functors
`QCoh(Y → X, Z) ⥤ QCoh(𝒪_X)` and `QCoh(Y' → X', Z') ⥤ QCoh(𝒪_{X'})` of Stacks 0AEX.

The isomorphism is the one transported from
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.glueingModulesFunctorPullbackIso`
along the two equivalences of Stacks 0AF0, whose quasi-inverses are the functors of
Stacks 0AEX. -/
@[stacks 0AEZ "compatibility with the functor of Tag 0AEX"]
def glueingKernelFunctorPullbackIso :
    D.glueingKernelFunctor ⋙ quasicoherentPullbackFunctor B S hS c.g ≅
      c.glueingDataPullback ⋙ D'.glueingKernelFunctor :=
  letI : CatCommSq D.glueingEquivalence.functor (quasicoherentPullbackFunctor B S hS c.g)
      c.glueingDataPullback D'.glueingEquivalence.functor :=
    ⟨c.glueingModulesFunctorPullbackIso⟩
  letI := CatCommSq.hInv _ _ _ _ this
  CatCommSq.iso D.glueingEquivalence.inverse c.glueingDataPullback
    (quasicoherentPullbackFunctor B S hS c.g) D'.glueingEquivalence.inverse

end FlatBaseChange

variable (D : FormalGlueingSituation B S hS) {X' : AlgebraicSpaces B S hS}
  (k : X' ⟶ D.spaceX) (hk : IsFlat B S hS k.hom)

/-- **Stacks 0AEZ, compatibility with the functor of Stacks 0AEW**, for the base change of the
situation along a flat morphism `k : X' ⟶ X`, with `Z' = X' ×_X Z` and `Y' = X' ×_X Y`. -/
@[stacks 0AEZ "compatibility with the functor of Tag 0AEW, for the constructed base change along \
a flat morphism"]
def glueingModulesFunctorBaseChangeIso :
    D.glueingModulesFunctor ⋙ (D.flatBaseChange k hk).glueingDataPullback ≅
      quasicoherentPullbackFunctor B S hS k ⋙ (D.baseChange k).glueingModulesFunctor :=
  (D.flatBaseChange k hk).glueingModulesFunctorPullbackIso

/-- **Stacks 0AEZ, compatibility with the functor of Stacks 0AEX**, for the base change of the
situation along a flat morphism `k : X' ⟶ X`, with `Z' = X' ×_X Z` and `Y' = X' ×_X Y`. -/
@[stacks 0AEZ "compatibility with the functor of Tag 0AEX, for the constructed base change along \
a flat morphism"]
def glueingKernelFunctorBaseChangeIso :
    D.glueingKernelFunctor ⋙ quasicoherentPullbackFunctor B S hS k ≅
      (D.flatBaseChange k hk).glueingDataPullback ⋙ (D.baseChange k).glueingKernelFunctor :=
  (D.flatBaseChange k hk).glueingKernelFunctorPullbackIso

end FormalGlueingSituation

end AlgebraicGeometry.Space
