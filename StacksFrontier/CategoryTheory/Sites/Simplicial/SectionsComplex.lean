module
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# The complex of global sections of an abelian sheaf on a simplicial site

Let `S` be a simplicial-site situation of Stacks 09WE, with total site `C_total` and component
sites `C_n`. For an abelian sheaf `F` on `C_total` with restrictions `F_n` to the components,
Stacks 0D77 produces a canonical complex

```
0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → Γ(C_2, F_2) → …
```

which is exact in degrees `-1` and `0`, and exact everywhere when `F` is injective.

The complex is `Hom(-, F)` applied to the resolution `… → g_{2!}Z → g_{1!}Z → g_{0!}Z → Z` of
the constant integer sheaf on the total site of Stacks 09WI: morphisms out of the constant integer
sheaf of a site are its global sections, and morphisms out of `g_{n!}Z` are the global sections
of the restriction of `F` to degree `n`. Global sections are `CategoryTheory.Sheaf.Γ`, the right
adjoint of the constant-sheaf functor.

## Main definitions

* `CategoryTheory.integerHomIsoGlobalSections`: `Hom(Z, -) ≅ Γ` on abelian sheaves over a site.
* `CategoryTheory.SimplicialSiteSituation.componentSectionsFunctor`: the functor
  `F ↦ Γ(C_n, F_n)`.
* `CategoryTheory.SimplicialSiteSituation.componentIntegerHomIsoSections`:
  `Hom(g_{n!}Z, -) ≅ Γ(C_n, (-)_n)`.
* `CategoryTheory.SimplicialSiteSituation.globalSectionsRestriction`: the canonical restriction
  `Γ(C_total, F) → Γ(C_n, F_n)` of global sections to a simplicial degree.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cechSectionsComplex`: **Stacks 0D77**, the canonical
  complex, as a functor in the sheaf; in degree `n` its term is `Γ(C_n, F_n)`
  (`cechSectionsComplex_obj_X`).
* `CategoryTheory.SimplicialSiteSituation.cechSectionsAugmentation`: **Stacks 0D77**, the
  augmentation `Γ(C_total, F) → Γ(C_0, F_0)` of that complex, natural in the sheaf. It is the
  canonical restriction to degree zero (`cechSectionsAugmentation_eq`).
* `CategoryTheory.SimplicialSiteSituation.cechSectionsAugmentation_app_mono` and
  `CategoryTheory.SimplicialSiteSituation.cechSectionsAugmentation_app_injective`:
  **Stacks 0D77**, exactness in degree `-1`.
* `CategoryTheory.SimplicialSiteSituation.cechSectionsComplex_shortComplexZero_exact`:
  **Stacks 0D77**, exactness in degree `0`.
* `CategoryTheory.SimplicialSiteSituation.cechSectionsComplex_exactAt_of_injective`:
  **Stacks 0D77**, exactness in every positive degree when the sheaf is injective. Together with
  the two previous results this is the source's "exact everywhere if `F` is injective".

## References

* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u₁ u₂ u

/-- For an adjunction `L ⊣ R` of additive functors, the additive hom-set bijection
`Hom(L X, -) ≅ Hom(X, R -)` as an isomorphism of functors to abelian groups. -/
def CategoryTheory.Adjunction.preadditiveCoyonedaObjIso {A : Type u₁} {B : Type u₂}
    [Category.{v} A] [Category.{v} B] [Preadditive A] [Preadditive B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) [L.Additive] (X : A) :
    preadditiveCoyoneda.obj (Opposite.op (L.obj X)) ≅
      R ⋙ preadditiveCoyoneda.obj (Opposite.op X) :=
  NatIso.ofComponents (fun F => AddEquiv.toAddCommGrpIso (adj.homAddEquiv X F))
    (fun f => by ext φ; exact adj.homEquiv_naturality_right φ f)

/-- The group of morphisms out of the integers is the group itself: `Hom(ULift ℤ, -)` is the
identity functor on abelian groups. The identification sends a morphism to its value on the
integer generator. -/
def AddCommGrpCat.preadditiveCoyonedaUliftIntIso :
    preadditiveCoyoneda.obj (Opposite.op (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      CategoryTheory.Functor.id AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso (uliftZMultiplesAddEquiv M))
    (fun f => by ext φ; rfl)

namespace CategoryTheory

/-- Morphisms out of the constant integer sheaf on a site are its global sections:
`Hom(Z, F) = Γ(C, F)`, naturally in the abelian sheaf `F`. -/
def integerHomIsoGlobalSections {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] :
    preadditiveCoyoneda.obj (op (integerSheaf J)) ≅ Sheaf.Γ J Ab.{u} :=
  (constantSheafΓAdj J Ab.{u}).preadditiveCoyonedaObjIso (AddCommGrpCat.of (ULift.{u} ℤ)) ≪≫
    Functor.isoWhiskerLeft (Sheaf.Γ J Ab.{u}) AddCommGrpCat.preadditiveCoyonedaUliftIntIso ≪≫
    (Sheaf.Γ J Ab.{u}).rightUnitor

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The global sections `Γ(C_n, F_n)` of the restriction of an abelian sheaf on the total site to
the component in simplicial degree `n`, as a functor of the sheaf. -/
abbrev componentSectionsFunctor (n : SimplexCategory) :
    Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u} :=
  S.restrictAb n ⋙ Sheaf.Γ (S.componentTopology n) Ab.{u}

/-- Morphisms out of the lower shriek image of the constant integer sheaf of a component are the
global sections of the restriction: `Hom(g_{n!}Z, F) = Γ(C_n, F_n)`, naturally in `F`. It is
the lower-shriek adjunction of Stacks 09WG followed by `integerHomIsoGlobalSections`. -/
def componentIntegerHomIsoSections (n : SimplexCategory) :
    preadditiveCoyoneda.obj (op (componentIntegerSheaf S n)) ≅ S.componentSectionsFunctor n :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) Ab.{u}
      (S.componentTopology n) S.totalTopology).preadditiveCoyonedaObjIso
      (integerSheaf (S.componentTopology n)) ≪≫
    Functor.isoWhiskerLeft (S.restrictAb n) (integerHomIsoGlobalSections (S.componentTopology n))

/-- The canonical map `g_{n!}Z → Z` from the lower shriek image of the constant integer sheaf of
a component to the constant integer sheaf of the total site: the transpose, under the
lower-shriek adjunction, of the comparison of constant integer sheaves along the component
inclusion. -/
def componentIntegerToTotal (n : SimplexCategory) :
    componentIntegerSheaf S n ⟶ totalIntegerSheaf S :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) Ab.{u}
      (S.componentTopology n) S.totalTopology).homEquiv _ _).symm
    (constantIntegerRestriction (componentFunctor S n) (S.componentTopology n) S.totalTopology)

/-- The canonical restriction `Γ(C_total, F) → Γ(C_n, F_n)` of a global section of an abelian
sheaf on the total site to simplicial degree `n`: under the two identifications of global
sections with Hom-groups it is precomposition with `componentIntegerToTotal`. -/
def globalSectionsRestriction (n : SimplexCategory) :
    Sheaf.Γ S.totalTopology Ab.{u} ⟶ S.componentSectionsFunctor n :=
  (integerHomIsoGlobalSections S.totalTopology).inv ≫
    preadditiveCoyoneda.map (S.componentIntegerToTotal n).op ≫
    (S.componentIntegerHomIsoSections n).hom


/-- Morphisms out of the degree-`n` term of the integral resolution of Stacks 09WI, as a functor
of the target sheaf. -/
abbrev resolutionTermHom (n : ℕ) : Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u} :=
  preadditiveCoyoneda.obj (op ((simplicialIntegerComplex S).X n))

/-- Morphisms out of the degree-`n` term of the integral resolution of Stacks 09WI are the global
sections of the restriction to degree `n`: the degreewise identification of Stacks 09WI composed
with `componentIntegerHomIsoSections`. -/
def resolutionTermSectionsIso (n : ℕ) :
    S.resolutionTermHom n ≅ S.componentSectionsFunctor ⦋n⦌ :=
  preadditiveCoyoneda.mapIso
      ((simplicialIntegerResolution S).degreeIso n).op.symm ≪≫
    S.componentIntegerHomIsoSections ⦋n⦌

/-- Precomposition with the degree-`n` differential of the integral resolution of Stacks 09WI. -/
def resolutionHomDifferential (n : ℕ) :
    S.resolutionTermHom n ⟶ S.resolutionTermHom (n + 1) :=
  preadditiveCoyoneda.map ((simplicialIntegerComplex S).d (n + 1) n).op

/-- Precomposition with `f` and then with `g` is zero when `g ≫ f` is zero. -/
private theorem preadditiveCoyoneda_map_op_comp_eq_zero {A : Type*} [Category A] [Preadditive A]
    {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0) :
    preadditiveCoyoneda.map g.op ≫ preadditiveCoyoneda.map f.op = 0 := by
  rw [← Functor.map_comp, ← op_comp, h, op_zero, Functor.map_zero]

/-- Two consecutive differentials of the Hom-complex compose to zero. -/
theorem resolutionHomDifferential_comp (n : ℕ) :
    S.resolutionHomDifferential n ≫ S.resolutionHomDifferential (n + 1) = 0 :=
  preadditiveCoyoneda_map_op_comp_eq_zero (HomologicalComplex.d_comp_d _ _ _ _)

/-- The differential of the Hom-complex is precomposition with the differential of the integral
resolution of Stacks 09WI. -/
theorem resolutionHomDifferential_app_apply (n : ℕ) (F : Sheaf S.totalTopology Ab.{u})
    (φ : (simplicialIntegerComplex S).X n ⟶ F) :
    (S.resolutionHomDifferential n).app F φ =
      (simplicialIntegerComplex S).d (n + 1) n ≫ φ := rfl

/-- The cochain complex of Hom-functors obtained by applying `Hom(-, -)` to the integral
resolution of Stacks 09WI. -/
def resolutionHomComplex : CochainComplex (Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u}) ℕ :=
  CochainComplex.of (S.resolutionTermHom) (S.resolutionHomDifferential)
    (S.resolutionHomDifferential_comp)

/-- The differentials of `resolutionHomComplex` are the ones it was built from. -/
theorem resolutionHomComplex_d (n : ℕ) :
    (S.resolutionHomComplex).d n (n + 1) = S.resolutionHomDifferential n := by
  simp only [resolutionHomComplex, CochainComplex.of_d]

/-- The differential `Γ(C_n, F_n) → Γ(C_{n + 1}, F_{n + 1})` of the complex of Stacks 0D77:
precomposition with the degree-`n` differential of the integral resolution of Stacks 09WI,
transported along the identification of Hom-groups with groups of sections. -/
def sectionsDifferential (n : ℕ) :
    S.componentSectionsFunctor ⦋n⦌ ⟶ S.componentSectionsFunctor ⦋n + 1⦌ :=
  (S.resolutionTermSectionsIso n).inv ≫ S.resolutionHomDifferential n ≫
    (S.resolutionTermSectionsIso (n + 1)).hom

/-- Two consecutive differentials of the complex of sections compose to zero. -/
theorem sectionsDifferential_comp (n : ℕ) :
    S.sectionsDifferential n ≫ S.sectionsDifferential (n + 1) = 0 := by
  simp only [sectionsDifferential, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (S.resolutionHomDifferential n), S.resolutionHomDifferential_comp n,
    zero_comp, comp_zero]

/-- The complex of Stacks 0D77 as a cochain complex of functors of the sheaf: in degree `n` its
term is the functor `F ↦ Γ(C_n, F_n)`. -/
def cechSectionsComplexFunctors : CochainComplex (Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u}) ℕ :=
  CochainComplex.of (fun n => S.componentSectionsFunctor ⦋n⦌) (S.sectionsDifferential)
    (S.sectionsDifferential_comp)

/-- The complex of Hom-functors is isomorphic, degreewise by the identification of Hom-groups
with groups of sections, to the complex of sections. -/
def resolutionHomComplexIsoSections :
    S.resolutionHomComplex ≅ S.cechSectionsComplexFunctors :=
  HomologicalComplex.Hom.isoOfComponents (S.resolutionTermSectionsIso) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [cechSectionsComplexFunctors, resolutionHomComplex, CochainComplex.of_d,
      sectionsDifferential, Iso.hom_inv_id_assoc])

/-- The canonical complex `Γ(C_0, F_0) → Γ(C_1, F_1) → Γ(C_2, F_2) → …` of an abelian sheaf `F`
on the total site of a simplicial site, functorially in `F`. Its augmentation by `Γ(C_total, F)`
is `cechSectionsAugmentation`. -/
@[stacks 0D77 "the canonical complex"]
def cechSectionsComplex : Sheaf S.totalTopology Ab.{u} ⥤ CochainComplex Ab.{u} ℕ where
  obj F := (((evaluation (Sheaf S.totalTopology Ab.{u}) Ab.{u}).obj F).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (S.cechSectionsComplexFunctors)
  map f := (NatTrans.mapHomologicalComplex
    ((evaluation (Sheaf S.totalTopology Ab.{u}) Ab.{u}).map f) (ComplexShape.up ℕ)).app _
  map_id F := by
    simp only [Functor.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp f g := by
    simp only [Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- The degree-`n` term of the complex of Stacks 0D77 is `Γ(C_n, F_n)`. -/
theorem cechSectionsComplex_obj_X (F : Sheaf S.totalTopology Ab.{u}) (n : ℕ) :
    ((S.cechSectionsComplex).obj F).X n = (S.componentSectionsFunctor ⦋n⦌).obj F := rfl

/-- The differentials of the complex of Stacks 0D77 are the maps `sectionsDifferential`. -/
theorem cechSectionsComplex_obj_d (F : Sheaf S.totalTopology Ab.{u}) (n : ℕ) :
    ((S.cechSectionsComplex).obj F).d n (n + 1) =
      (S.sectionsDifferential n).app F := by
  simp only [cechSectionsComplex, Functor.mapHomologicalComplex_obj_d,
    cechSectionsComplexFunctors, CochainComplex.of_d, evaluation_obj_map]

/-- Precomposition with the augmentation of the integral resolution of Stacks 09WI. -/
def resolutionHomAugmentation :
    preadditiveCoyoneda.obj (op (totalIntegerSheaf S)) ⟶ S.resolutionTermHom 0 :=
  preadditiveCoyoneda.map ((simplicialIntegerResolution S).augmentation).op

/-- The augmentation of the Hom-complex followed by its first differential is zero. -/
theorem resolutionHomAugmentation_comp :
    S.resolutionHomAugmentation ≫ S.resolutionHomDifferential 0 = 0 :=
  preadditiveCoyoneda_map_op_comp_eq_zero (simplicialIntegerResolution S).augmentation_comp

/-- The augmentation `Γ(C_total, F) → Γ(C_0, F_0)` of the canonical complex, natural in the
abelian sheaf `F`. It is the canonical restriction of a global section to
simplicial degree zero; see `cechSectionsAugmentation_eq`. -/
@[stacks 0D77 "the augmentation"]
def cechSectionsAugmentation :
    Sheaf.Γ S.totalTopology Ab.{u} ⟶ S.componentSectionsFunctor ⦋0⦌ :=
  (integerHomIsoGlobalSections S.totalTopology).inv ≫ S.resolutionHomAugmentation ≫
    (S.resolutionTermSectionsIso 0).hom

/-- The augmentation followed by the first differential of the complex of sections is zero. -/
theorem cechSectionsAugmentation_comp :
    S.cechSectionsAugmentation ≫ S.sectionsDifferential 0 = 0 := by
  simp only [cechSectionsAugmentation, sectionsDifferential, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc (S.resolutionHomAugmentation), S.resolutionHomAugmentation_comp,
    zero_comp, comp_zero]

/-- The augmentation at a sheaf followed by the first differential of the complex of Stacks 0D77
is zero. -/
theorem cechSectionsAugmentation_comp_d (F : Sheaf S.totalTopology Ab.{u}) :
    (S.cechSectionsAugmentation).app F ≫
        ((S.cechSectionsComplex).obj F).d 0 1 = 0 := by
  have h : (S.cechSectionsAugmentation ≫ S.sectionsDifferential 0).app F = 0 := by
    rw [S.cechSectionsAugmentation_comp]; rfl
  rw [S.cechSectionsComplex_obj_d F 0]
  exact h

/-- Precomposition with the augmentation of the integral resolution is injective. -/
theorem resolutionHomAugmentation_app_injective (F : Sheaf S.totalTopology Ab.{u}) :
    Function.Injective ((S.resolutionHomAugmentation).app F) := by
  have := (simplicialIntegerResolution S).augmentation_epi
  intro φ ψ h
  exact (cancel_epi (simplicialIntegerResolution S).augmentation).mp h

/-- Precomposition with the augmentation of the integral resolution is a monomorphism. -/
theorem resolutionHomAugmentation_app_mono (F : Sheaf S.totalTopology Ab.{u}) :
    Mono ((S.resolutionHomAugmentation).app F) :=
  (AddCommGrpCat.mono_iff_injective _).2 (S.resolutionHomAugmentation_app_injective F)

/-- Exactness in degree `-1`: the augmentation `Γ(C_total, F) → Γ(C_0, F_0)` of the canonical
complex is a monomorphism. -/
@[stacks 0D77 "exactness in degree -1"]
theorem cechSectionsAugmentation_app_mono (F : Sheaf S.totalTopology Ab.{u}) :
    Mono ((S.cechSectionsAugmentation).app F) := by
  have := S.resolutionHomAugmentation_app_mono F
  change Mono ((integerHomIsoGlobalSections S.totalTopology).inv.app F ≫
    (S.resolutionHomAugmentation).app F ≫
      (S.resolutionTermSectionsIso 0).hom.app F)
  infer_instance

/-- Exactness in degree `-1`, concretely: the augmentation `Γ(C_total, F) → Γ(C_0, F_0)` of the
canonical complex is injective. -/
@[stacks 0D77 "exactness in degree -1"]
theorem cechSectionsAugmentation_app_injective (F : Sheaf S.totalTopology Ab.{u}) :
    Function.Injective ((S.cechSectionsAugmentation).app F) :=
  (AddCommGrpCat.mono_iff_injective _).1 (S.cechSectionsAugmentation_app_mono F)

/-- The augmented Hom-complex `Hom(Z, F) → Hom(g_{0!}Z, F) → Hom(g_{1!}Z, F)` is exact at
`Hom(g_{0!}Z, F)`. -/
theorem resolutionHomShortComplexZero_exact (F : Sheaf S.totalTopology Ab.{u}) :
    (ShortComplex.mk ((S.resolutionHomAugmentation).app F)
      ((S.resolutionHomDifferential 0).app F)
      (by
        rw [← NatTrans.comp_app, S.resolutionHomAugmentation_comp, NatTrans.app_zero])).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro φ hφ
  have hepi := (simplicialIntegerResolution S).augmentation_epi
  have hc := (simplicialIntegerResolution S).exact_zero.gIsCokernel
  exact ⟨hc.desc (CokernelCofork.ofπ φ hφ), Cofork.IsColimit.π_desc hc⟩

/-- The Hom-complex of the integral resolution, evaluated at an abelian sheaf. -/
abbrev resolutionHomComplexObj (F : Sheaf S.totalTopology Ab.{u}) : CochainComplex Ab.{u} ℕ :=
  (((evaluation (Sheaf S.totalTopology Ab.{u}) Ab.{u}).obj F).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (S.resolutionHomComplex)

/-- The differentials of the evaluated Hom-complex are precomposition with the differentials of
the integral resolution. -/
theorem resolutionHomComplexObj_d (F : Sheaf S.totalTopology Ab.{u}) (n : ℕ) :
    (S.resolutionHomComplexObj F).d n (n + 1) =
      (S.resolutionHomDifferential n).app F := by
  simp only [resolutionHomComplexObj, Functor.mapHomologicalComplex_obj_d]
  exact NatTrans.congr_app (S.resolutionHomComplex_d n) F

/-- The evaluated Hom-complex is isomorphic to the complex of Stacks 0D77. -/
def resolutionHomComplexObjIsoSections (F : Sheaf S.totalTopology Ab.{u}) :
    S.resolutionHomComplexObj F ≅ (S.cechSectionsComplex).obj F :=
  (((evaluation (Sheaf S.totalTopology Ab.{u}) Ab.{u}).obj F).mapHomologicalComplex
    (ComplexShape.up ℕ)).mapIso (S.resolutionHomComplexIsoSections)

/-- For an injective abelian sheaf, three consecutive terms of the evaluated Hom-complex, in
degrees `n`, `n + 1`, `n + 2`, form an exact sequence. -/
theorem resolutionHomComplexObj_sc'_exact (n : ℕ) (F : Sheaf S.totalTopology Ab.{u})
    [Injective F] :
    ((S.resolutionHomComplexObj F).sc' n (n + 1) (n + 1 + 1)).Exact := by
  have hex := (simplicialIntegerResolution S).exact_positive (n + 1) (Nat.succ_pos n)
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)] at hex
  rw [ShortComplex.ab_exact_iff]
  intro φ hφ
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    S.resolutionHomComplexObj_d F (n + 1)] at hφ
  have hφ' : (HomologicalComplex.sc' (simplicialIntegerComplex S)
      (n + 1 + 1) (n + 1) n).f ≫ φ = 0 := hφ
  refine ⟨hex.descToInjective φ hφ', ?_⟩
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    S.resolutionHomComplexObj_d F n]
  exact hex.comp_descToInjective φ hφ'

/-- For an injective abelian sheaf the evaluated Hom-complex is exact in every positive
degree. -/
theorem resolutionHomComplexObj_exactAt_of_injective (F : Sheaf S.totalTopology Ab.{u})
    [Injective F] (n : ℕ) (hn : 0 < n) : (S.resolutionHomComplexObj F).ExactAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1)
    (CochainComplex.prev_nat_succ m) (CochainComplex.next ℕ (m + 1))]
  exact S.resolutionHomComplexObj_sc'_exact m F

/-- Exactness in positive degrees for an injective sheaf: if `F` is an injective abelian sheaf on
the total site, the canonical complex `Γ(C_0, F_0) → Γ(C_1, F_1) → Γ(C_2, F_2) → …` is exact at
`Γ(C_n, F_n)` for every `n > 0`. -/
@[stacks 0D77 "exactness in positive degrees for an injective sheaf"]
theorem cechSectionsComplex_exactAt_of_injective (F : Sheaf S.totalTopology Ab.{u})
    [Injective F] (n : ℕ) (hn : 0 < n) :
    ((S.cechSectionsComplex).obj F).ExactAt n :=
  (S.resolutionHomComplexObj_exactAt_of_injective F n hn).of_iso
    (S.resolutionHomComplexObjIsoSections F)

/-- The identification of Hom-groups with groups of sections carries the differential of the
Hom-complex to the differential of the complex of sections. -/
theorem resolutionTermSectionsIso_hom_comp_sectionsDifferential (n : ℕ) :
    (S.resolutionTermSectionsIso n).hom ≫ S.sectionsDifferential n =
      S.resolutionHomDifferential n ≫
        (S.resolutionTermSectionsIso (n + 1)).hom := by
  simp only [sectionsDifferential, Iso.hom_inv_id_assoc]

/-- The identification of Hom-groups with groups of sections carries the augmentation of the
Hom-complex to the augmentation of the complex of sections. -/
theorem integerHomIso_hom_comp_cechSectionsAugmentation :
    (integerHomIsoGlobalSections S.totalTopology).hom ≫ S.cechSectionsAugmentation =
      S.resolutionHomAugmentation ≫ (S.resolutionTermSectionsIso 0).hom := by
  simp only [cechSectionsAugmentation, Iso.hom_inv_id_assoc]

/-- Exactness in degree `0`: the sequence `Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1)` is exact
at `Γ(C_0, F_0)`. -/
@[stacks 0D77 "exactness in degree 0"]
theorem cechSectionsComplex_shortComplexZero_exact (F : Sheaf S.totalTopology Ab.{u}) :
    (ShortComplex.mk ((S.cechSectionsAugmentation).app F)
      (((S.cechSectionsComplex).obj F).d 0 1)
      (S.cechSectionsAugmentation_comp_d F)).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk
    (Iso.app (integerHomIsoGlobalSections S.totalTopology) F)
    (Iso.app (S.resolutionTermSectionsIso 0) F)
    (Iso.app (S.resolutionTermSectionsIso 1) F) ?_ ?_)
    (S.resolutionHomShortComplexZero_exact F)
  · exact NatTrans.congr_app S.integerHomIso_hom_comp_cechSectionsAugmentation F
  · simp only [S.cechSectionsComplex_obj_d F 0]
    exact NatTrans.congr_app (S.resolutionTermSectionsIso_hom_comp_sectionsDifferential 0) F

/-- The augmentation of the canonical complex of Stacks 0D77 is the canonical restriction of
global sections to simplicial degree zero. -/
theorem cechSectionsAugmentation_eq :
    S.cechSectionsAugmentation = S.globalSectionsRestriction ⦋0⦌ := by
  have hadj : ((simplicialIntegerResolution S).degreeIso 0).inv ≫
      (simplicialIntegerResolution S).augmentation =
      S.componentIntegerToTotal ⦋0⦌ := by
    refine ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S ⦋0⦌) Ab.{u} (S.componentTopology ⦋0⦌)
      S.totalTopology).homEquiv _ _).injective ?_
    rw [(simplicialIntegerResolution S).augmentation_adjacent]
    exact (Equiv.apply_symm_apply _ _).symm
  simp only [cechSectionsAugmentation, globalSectionsRestriction, resolutionTermSectionsIso,
    resolutionHomAugmentation, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hadj]

end SimplicialSiteSituation

end CategoryTheory

end
