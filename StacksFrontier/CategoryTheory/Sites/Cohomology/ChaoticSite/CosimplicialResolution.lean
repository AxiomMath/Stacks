module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ProjectiveReplacementAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Homology of a category computed by a cosimplicial resolution

Let `C` be a small category carrying the chaotic topology, so that the homology groups
`H_n(C, ℱ) = L_nπ_!(ℱ)` of an abelian presheaf are the values of the left derived functors of the
colimit over `Cᵒᵖ`. Let `U_•` be a cosimplicial object of `C` such that for every object `W` the
simplicial set `Mor_C(U_•, W)` is homotopy equivalent to the constant simplicial set on a
singleton. Then `L_nπ_!(ℱ) = H_n(ℱ(U_•))`, the homology of the Moore complex of the simplicial
abelian group `ℱ(U_•)`, for every abelian presheaf `ℱ`.

## Main definitions

* `Stacks.ChaoticSite.IsPointResolution`: the hypothesis on a cosimplicial object that each
  simplicial set of morphisms into an object of `C` be homotopy equivalent to a singleton.
* `Stacks.ChaoticSite.cosimplicialMooreComplex`: the functor sending an abelian presheaf `ℱ` to
  the Moore complex of the simplicial abelian group `ℱ(U_•)`.
* `Stacks.ChaoticSite.cosimplicialHomologyDeltaFunctor`: its homology, as a homological
  δ-functor in `ℱ`.

## Main results

* `Stacks.ChaoticSite.freeRepresentablePresheafHomEquiv` and
  `Stacks.ChaoticSite.freeRepresentablePresheaf_projective`: maps out of `j_{W!}ℤ_W` are the
  sections over `W`, so `j_{W!}ℤ_W` is a projective abelian presheaf.
* `Stacks.ChaoticSite.colimitFreeRepresentablePresheafIso`: `π_!j_{W!}ℤ_W = ℤ`, the colimit over
  `Cᵒᵖ` of `j_{W!}ℤ_W` being the free abelian group on a singleton.
* `Stacks.ChaoticSite.freeRepresentableMooreComplexHomologyIso` and
  `Stacks.ChaoticSite.isZero_cosimplicialHomology_freeRepresentable_succ`: for a point
  resolution, the Moore complex of `j_{W!}ℤ_W(U_•)` has the homology of the alternating constant
  complex on the free abelian group on a singleton, hence `ℤ` in degree zero and nothing above.
* `Stacks.ChaoticSite.leftDerivedColimitIsoMooreComplexHomology`: the homology of `C` with
  coefficients `j_{W!}ℤ_W` is the homology of the Moore complex of `j_{W!}ℤ_W(U_•)`.
* `Stacks.ChaoticSite.cosimplicialMooreComplex_map_shortExact`: evaluation on a cosimplicial
  object followed by the Moore complex is exact in `ℱ`.
* `Stacks.ChaoticSite.leftDerivedColimitNatIsoOfVanishing`: `L_nπ_!(ℱ) = H_n(ℱ(U_•))` in
  every degree and naturally in `ℱ`, given positive-degree vanishing on projective presheaves
  and the degree-zero identification `H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`.
* `Stacks.ChaoticSite.isZero_cosimplicialHomology_projective_succ`: the homology of `ℱ(U_•)`
  vanishes in positive degrees on every projective abelian presheaf.
* `Stacks.ChaoticSite.colimitι_comp_colimitFreeRepresentablePresheafIso_hom` and
  `Stacks.ChaoticSite.pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim_free`: the degree-zero
  comparison on `j_{W!}ℤ_W` is the canonical map of Tag 08Q6, the free abelian group functor
  applied to `Mor_C(U_0, W) → ∗`.
* `Stacks.ChaoticSite.exists_comp_freeAugmentation`: every map out of `ℤ^{Mor_C(U_0, W)}`
  killing the degree-one differential of `j_{W!}ℤ_W(U_•)` factors through that canonical map.
* `Stacks.ChaoticSite.colimitι_isColimit` and
  `Stacks.ChaoticSite.cosimplicialHomologyZeroNatIsoColim`: the colimit injection at `U_0` is a
  cokernel of the degree-one differential of `ℱ(U_•)`, so `H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ` naturally
  in `ℱ`.
* `Stacks.ChaoticSite.leftDerivedColimitNatIso`: `L_nπ_!(ℱ) = H_n(ℱ(U_•))` for every abelian
  presheaf `ℱ`, naturally in `ℱ`.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08P2](https://stacks.math.columbia.edu/tag/08P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe v u₁ u

variable {C : Type u} [SmallCategory C]

/-- Abelian presheaves on a small category have enough projectives. -/
instance enoughProjectives : EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  presheafEnoughProjectives.{u, u} C

/-! ### The free abelian presheaf on a representable is projective -/

/-- **Maps out of `j_{W!}ℤ_W` are the sections over `W`.** -/
@[sga "4 Vbis 2.3.1" "Bijection Hom(r_D(i)"]
def freeRepresentablePresheafHomEquiv {W : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} :
    (freeRepresentablePresheaf W ⟶ F) ≃ (F.obj (op W) : Type u) :=
  ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj W) F).trans yonedaEquiv

/-- `Stacks.ChaoticSite.freeRepresentablePresheafHomEquiv` is natural in the target presheaf. -/
lemma freeRepresentablePresheafHomEquiv_comp {W : C} {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : freeRepresentablePresheaf W ⟶ F) (f : F ⟶ G) :
    freeRepresentablePresheafHomEquiv (α ≫ f) =
      (f.app (op W)) (freeRepresentablePresheafHomEquiv α) := by
  dsimp only [freeRepresentablePresheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

/-- **`j_{W!}ℤ_W` is a projective abelian presheaf.** -/
instance freeRepresentablePresheaf_projective (W : C) :
    Projective (freeRepresentablePresheaf (C := C) W) where
  factors {_ _} g e he := by
    have he' : Epi (e.app (op W)) := (NatTrans.epi_iff_epi_app e).mp he _
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he'
      (freeRepresentablePresheafHomEquiv g)
    refine ⟨freeRepresentablePresheafHomEquiv.symm x, ?_⟩
    apply freeRepresentablePresheafHomEquiv.injective
    rwa [freeRepresentablePresheafHomEquiv_comp, Equiv.apply_symm_apply]

/-! ### The colimit of the free abelian presheaf on a representable -/

/-- The cocone on a representable presheaf with vertex a singleton. -/
@[simps]
def yonedaPointCocone (W : C) : Cocone (yoneda.obj W) where
  pt := PUnit.{u + 1}
  ι := { app _ := ↾fun _ ↦ by cat_disch }

/-- **The colimit of a representable presheaf over `Cᵒᵖ` is a singleton.** -/
def isColimitYonedaPointCocone (W : C) : IsColimit (yonedaPointCocone (C := C) W) where
  desc s := ↾fun _ ↦ s.ι.app (op W) (𝟙 W)
  fac s j := by
    ext h
    refine (ConcreteCategory.congr_hom (s.w h.op) (𝟙 W)).symm.trans ?_
    simp
  uniq s m w := by
    ext ⟨⟩
    exact ConcreteCategory.congr_hom (w (op W)) (𝟙 W)

/-- The free abelian group functor is a left adjoint. -/
instance : AddCommGrpCat.free.{u}.IsLeftAdjoint :=
  AddCommGrpCat.adj.isLeftAdjoint

/-- **`π_!j_{W!}ℤ_W = ℤ`**: the colimit over `Cᵒᵖ` of the free abelian presheaf on a
representable is the free abelian group on a singleton. -/
def colimitFreeRepresentablePresheafIso (W : C) :
    colimit (freeRepresentablePresheaf (C := C) W) ≅
      AddCommGrpCat.free.obj PUnit.{u + 1} :=
  colimit.isoColimitCocone
    ⟨_, isColimitOfPreserves AddCommGrpCat.free (isColimitYonedaPointCocone W)⟩

/-! ### Cosimplicial point resolutions -/

section PointResolution

variable {C : Type u₁} [Category.{v} C]

/-- A cosimplicial object `U_•` of `C` is a *point resolution* when for every object `W` the
simplicial set `Mor_C(U_•, W)` is homotopy equivalent to the constant simplicial set on a
singleton. -/
def IsPointResolution (U : CosimplicialObject C) : Prop :=
  ∀ W : C, ∃ f : U.op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1},
    SimplicialObject.homotopyEquivalences (Type v) f

end PointResolution

variable (U : CosimplicialObject C)

/-- The Moore complex of the evaluation of an abelian presheaf `ℱ` on a cosimplicial object
`U_•`, that is the complex `ℱ(U_•)`, functorially in `ℱ`. -/
abbrev cosimplicialMooreComplex :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  GeneralValued.cosimplicialMooreComplex AddCommGrpCat.{u} U

/-- **Evaluation on a cosimplicial object followed by the Moore complex is an exact functor of
the presheaf.** -/
theorem cosimplicialMooreComplex_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})} (hS : S.ShortExact) :
    (S.map (cosimplicialMooreComplex U)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    hS.map_of_exact
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (Functor.obj U (SimplexCategory.mk n))))

/-- **The homology of `ℱ(U_•)` as a homological δ-functor** in the abelian presheaf `ℱ`, with the
connecting morphisms of the long exact homology sequence. -/
def cosimplicialHomologyDeltaFunctor :
    HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) AddCommGrpCat.{u} :=
  HomologicalDeltaFunctor.ofChainComplexFunctor (cosimplicialMooreComplex U)
    fun hS ↦ cosimplicialMooreComplex_map_shortExact U hS

/-- The degree-`n` functor of `Stacks.ChaoticSite.cosimplicialHomologyDeltaFunctor` is the
homology of `ℱ(U_•)` in degree `n`. -/
lemma cosimplicialHomologyDeltaFunctor_functor (n : ℕ) :
    (cosimplicialHomologyDeltaFunctor U).functor n =
      cosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  rfl

/-- The Moore complex of the free simplicial abelian group on the constant simplicial set with
value a singleton is the alternating constant complex on the free abelian group on a
singleton. -/
def constFreeMooreComplexIso :
    (alternatingFaceMapComplex AddCommGrpCat.{u}).obj
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj
          AddCommGrpCat.free).obj ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1})) ≅
      ChainComplex.alternatingConst.obj (AddCommGrpCat.free.obj PUnit.{u + 1}) :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ PUnit.{u + 1} AddCommGrpCat.free) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app (AddCommGrpCat.free.obj PUnit.{u + 1})

/-- **The Moore complex of the free simplicial abelian group on a simplicial set homotopy
equivalent to a singleton has the homology of `ℤ` placed in degree zero.** -/
def freeMooreComplexHomologyIsoOfHomotopyEquiv {X : SimplicialObject (Type u)}
    {f : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}}
    (hf : SimplicialObject.homotopyEquivalences (Type u) f) (n : ℕ) :
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj
        (X ⋙ AddCommGrpCat.free)).homology n ≅
      (ChainComplex.alternatingConst.obj
        (AddCommGrpCat.free.obj PUnit.{u + 1})).homology n := by
  have hg := SimplicialObject.homotopyEquivalences_whiskering_map AddCommGrpCat.free hf
  have hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj
        AddCommGrpCat.free).map f)) :=
    homotopyEquivalences_le_quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ) _
      (AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map hg)
  have : IsIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj
          AddCommGrpCat.free).map f)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)
  exact asIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj
          AddCommGrpCat.free).map f)) n) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).mapIso
      constFreeMooreComplexIso

/-- **The Moore complex of `j_{W!}ℤ_W(U_•)` has the homology of `ℤ` placed in degree zero**, for
`U_•` a point resolution. -/
def freeRepresentableMooreComplexHomologyIso (hU : IsPointResolution U) (W : C) (n : ℕ) :
    ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).homology n ≅
      (ChainComplex.alternatingConst.obj
        (AddCommGrpCat.free.obj PUnit.{u + 1})).homology n :=
  freeMooreComplexHomologyIsoOfHomotopyEquiv (hU W).choose_spec n

/-! ### Tag 08Q9 for a free abelian presheaf on a representable -/

/-- Let `U_•` be a cosimplicial object of a small category `C` such that every simplicial set
`Mor_C(U_•, W)` is homotopy equivalent to a singleton. The homology `L_nπ_!` of `C` with
coefficients the free abelian presheaf `j_{W!}ℤ_W` on a representable is the homology of the
Moore complex of `j_{W!}ℤ_W(U_•)`. -/
@[stacks 08Q9 "for the abelian sheaves `ℱ = j_{W!}ℤ_W`, the free abelian presheaves on \
  representables, which are the projective generators the source's proof reduces to; `Lπ_!` is \
  read degreewise as the left derived functors `L_nπ_! = H_n(C, -)` of the colimit over `Cᵒᵖ` of \
  Tag 08PF, and `ℱ(U_•)` as the Moore complex of the simplicial abelian group obtained by \
  evaluating `ℱ` on `U_•`"]
def leftDerivedColimitIsoMooreComplexHomology (hU : IsPointResolution U) (W : C) (n : ℕ) :
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).obj
        (freeRepresentablePresheaf W) ≅
      ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).homology n := by
  match n with
  | 0 =>
    exact ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerivedZeroIsoSelf.app
        (freeRepresentablePresheaf W)) ≪≫ colimitFreeRepresentablePresheafIso W ≪≫
      (ChainComplex.alternatingConstHomologyZero
        (AddCommGrpCat.free.obj PUnit.{u + 1})).symm ≪≫
      (freeRepresentableMooreComplexHomologyIso U hU W 0).symm
  | m + 1 =>
    refine (Functor.isZero_leftDerived_obj_projective_succ
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) m
      (freeRepresentablePresheaf W)).iso ?_
    refine IsZero.of_iso ?_ (freeRepresentableMooreComplexHomologyIso U hU W (m + 1))
    exact (ChainComplex.alternatingConst_exactAt (AddCommGrpCat.free.obj PUnit.{u + 1})
      (m + 1) (Nat.succ_ne_zero m)).isZero_homology

/-! ### The reduction of the general case to two computations -/

/-- **The free abelian presheaf on a representable is acyclic for `ℱ ↦ ℱ(U_•)`**, for `U_•` a
point resolution. -/
theorem isZero_cosimplicialHomology_freeRepresentable_succ (hU : IsPointResolution U) (W : C)
    (n : ℕ) :
    IsZero (((cosimplicialHomologyDeltaFunctor U).functor (n + 1)).obj
      (freeRepresentablePresheaf W)) := by
  refine IsZero.of_iso ?_ (freeRepresentableMooreComplexHomologyIso U hU W (n + 1))
  exact (ChainComplex.alternatingConst_exactAt (AddCommGrpCat.free.obj PUnit.{u + 1})
    (n + 1) (Nat.succ_ne_zero n)).isZero_homology

/-- Suppose the homology of `ℱ(U_•)` vanishes in positive degrees on projective abelian presheaves
and agrees in degree zero with the colimit over `Cᵒᵖ`. Then `L_nπ_!(ℱ) = H_n(ℱ(U_•))` in every
degree, naturally in `ℱ`. -/
def leftDerivedColimitNatIsoOfVanishing
    (h0 : (cosimplicialHomologyDeltaFunctor U).functor 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}))
    (hpos : ∀ (n : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) [Projective P],
      IsZero (((cosimplicialHomologyDeltaFunctor U).functor (n + 1)).obj P))
    (n : ℕ) :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n ≅
      cosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  have _ : (cosimplicialHomologyDeltaFunctor U).IsUniversal :=
    HomologicalDeltaFunctor.isUniversal_of_isZero_projective _ hpos
  have _ : (derivedColimitDeltaFunctor.{u, u} (C := C)).IsUniversal :=
    derivedColimitDeltaFunctor_isUniversal.{u, u}
  HomologicalDeltaFunctor.isoApp
    (HomologicalDeltaFunctor.IsUniversal.isoOfIso
      (H := derivedColimitDeltaFunctor.{u, u} (C := C))
      (G := cosimplicialHomologyDeltaFunctor U)
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerivedZeroIsoSelf ≪≫
        h0.symm)) n

/-! ### Positive-degree vanishing on every projective abelian presheaf -/

section DirectSum

open scoped DirectSum

variable {ι : Type u} (F : ι → (Cᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- In each degree the Moore complex of `(⊕ᵢ ℱᵢ)(U_•)` is the direct sum of the Moore complexes
of the `ℱᵢ(U_•)`. -/
def cosimplicialMooreComplexDirectSumEquiv (p : ℕ) :
    (⨁ i, (((cosimplicialMooreComplex U).obj (F i)).X p : Type u)) ≃+
      (((cosimplicialMooreComplex U).obj (directSumPresheaf F)).X p : Type u) :=
  AddEquiv.refl _

/-- The comparison of `Stacks.ChaoticSite.cosimplicialMooreComplexDirectSumEquiv` is compatible
with the differentials. -/
lemma cosimplicialMooreComplexDirectSumEquiv_ladder (p q : ℕ) :
    AddMonoidHom.comp (((cosimplicialMooreComplex U).obj (directSumPresheaf F)).d p q).hom
        (cosimplicialMooreComplexDirectSumEquiv U F p).toAddMonoidHom =
      AddMonoidHom.comp (cosimplicialMooreComplexDirectSumEquiv U F q).toAddMonoidHom
        (DirectSum.map fun i ↦ (((cosimplicialMooreComplex U).obj (F i)).d p q).hom) := by
  classical
  refine DirectSum.addHom_ext fun i y ↦ ?_
  have hcomm := ((cosimplicialMooreComplex U).map (directSumPresheafIncl F i)).comm p q
  have h := ConcreteCategory.congr_hom hcomm y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.map_of]
  exact h

/-- **Vanishing of the homology of `ℱ(U_•)` in a fixed positive degree passes to sectionwise
direct sums.** -/
theorem isZero_cosimplicialHomology_directSum_succ (n : ℕ)
    (h : ∀ i, IsZero (((cosimplicialMooreComplex U).obj (F i)).homology (n + 1))) :
    IsZero (((cosimplicialMooreComplex U).obj (directSumPresheaf F)).homology (n + 1)) := by
  classical
  have hex (K : ChainComplex AddCommGrpCat.{u} ℕ) : IsZero (K.homology (n + 1)) ↔
      Function.Exact (K.d (n + 2) (n + 1)).hom (K.d (n + 1) n).hom := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
        (ChainComplex.next_nat_succ n),
      ShortComplex.ab_exact_iff_function_exact]
    exact Iff.rfl
  refine (hex _).2 ?_
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (cosimplicialMooreComplexDirectSumEquiv U F (n + 2))
    (cosimplicialMooreComplexDirectSumEquiv U F (n + 1))
    (cosimplicialMooreComplexDirectSumEquiv U F n)
    (cosimplicialMooreComplexDirectSumEquiv_ladder U F (n + 2) (n + 1))
    (cosimplicialMooreComplexDirectSumEquiv_ladder U F (n + 1) n) ?_
  exact directSum_exact _ _ fun i ↦ (hex _).1 (h i)

end DirectSum

/-- Vanishing of the homology of `ℱ(U_•)` in a fixed degree passes to retracts. -/
theorem isZero_cosimplicialHomology_of_retract {G G' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (i : G ⟶ G')
    (r : G' ⟶ G) (hir : i ≫ r = 𝟙 G) (n : ℕ)
    (h : IsZero (((cosimplicialMooreComplex U).obj G').homology n)) :
    IsZero (((cosimplicialMooreComplex U).obj G).homology n) := by
  let T : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    cosimplicialMooreComplex U ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  have hT : IsZero (T.obj G') := h
  rw [IsZero.iff_id_eq_zero]
  have h₁ : T.map i ≫ T.map r = 𝟙 (T.obj G) := by rw [← T.map_comp, hir, T.map_id]
  have h₂ : T.map i ≫ T.map r = 0 := by rw [hT.eq_of_tgt (T.map i) 0]; simp
  exact h₁.symm.trans h₂

/-- **The homology of `ℱ(U_•)` vanishes in positive degrees on every projective abelian
presheaf**, for `U_•` a point resolution. -/
theorem isZero_cosimplicialHomology_projective_succ (hU : IsPointResolution U) (n : ℕ)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) [Projective P] :
    IsZero (((cosimplicialHomologyDeltaFunctor U).functor (n + 1)).obj P) := by
  classical
  refine isZero_cosimplicialHomology_of_retract U
    (Projective.factorThru (𝟙 P) (freeCoverHom P)) (freeCoverHom P)
    (Projective.factorThru_comp _ _) (n + 1) ?_
  exact isZero_cosimplicialHomology_directSum_succ U
    (fun j : freeCoverIndex P ↦ freeRepresentablePresheaf j.1) n fun j ↦
      isZero_cosimplicialHomology_freeRepresentable_succ U hU j.1 n

/-! ### The degree-one differential of `ℱ(U_•)` -/

/-- The degree-one differential of the Moore complex of `ℱ(U_•)` is the difference of the two
cofaces `U_0 ⟶ U_1`. -/
lemma cosimplicialMooreComplex_obj_d_one_zero (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((cosimplicialMooreComplex U).obj G).d 1 0 =
      G.map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map (U.map (SimplexCategory.δ (1 : Fin 2))).op :=
  GeneralValued.cosimplicialMooreComplex_obj_d_one_zero U G

/-- **The colimit injection at `U_0` kills the degree-one differential of `ℱ(U_•)`.** -/
theorem d_one_zero_comp_colimitι (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((cosimplicialMooreComplex U).obj G).d 1 0 ≫
        colimit.ι G (op (U.obj (SimplexCategory.mk 0))) = 0 :=
  GeneralValued.d_one_zero_comp_colimitι U G

/-! ### The degree-zero comparison on a free abelian presheaf is the canonical one -/

/-- **The degree-zero comparison for `j_{W!}ℤ_W`.** The colimit injection at an object, followed
by the identification `π_!j_{W!}ℤ_W = ℤ`, is the free abelian group functor applied to the unique
map `Mor_C(-, W) → ∗`. -/
theorem colimitι_comp_colimitFreeRepresentablePresheafIso_hom (W : C) (Y : Cᵒᵖ) :
    colimit.ι (freeRepresentablePresheaf (C := C) W) Y ≫
        (colimitFreeRepresentablePresheafIso W).hom =
      AddCommGrpCat.free.map ((yonedaPointCocone W).ι.app Y) :=
  colimit.isoColimitCocone_ι_hom _ Y

/-- The augmentation kills the degree-one differential of `j_{W!}ℤ_W(U_•)`. -/
lemma d_one_zero_comp_freeAugmentation (W : C) :
    ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).d 1 0 ≫
        AddCommGrpCat.free.map
          ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0)))) = 0 := by
  have hw : ∀ i : Fin 2,
      (freeRepresentablePresheaf (C := C) W).map (U.map (SimplexCategory.δ i)).op ≫
          AddCommGrpCat.free.map
            ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0)))) =
        AddCommGrpCat.free.map
          ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 1)))) := by
    intro i
    change AddCommGrpCat.free.map ((yoneda.obj W).map (U.map (SimplexCategory.δ i)).op) ≫ _ = _
    rw [← AddCommGrpCat.free.map_comp]
    exact congrArg AddCommGrpCat.free.map
      ((yonedaPointCocone W).w (U.map (SimplexCategory.δ i)).op)
  rw [cosimplicialMooreComplex_obj_d_one_zero, Preadditive.sub_comp, hw 0, hw 1, sub_self]

/-- The Moore complex of the free simplicial abelian group on the constant simplicial set with
value a singleton. -/
abbrev constFreeMooreComplex : ChainComplex AddCommGrpCat.{u} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).obj
    (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}))

/-- The chain map of Moore complexes induced by the chosen homotopy equivalence
`Mor_C(U_•, W) → ∗`. -/
def freeCollapse (hU : IsPointResolution U) (W : C) :
    (cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W) ⟶ constFreeMooreComplex.{u} :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).map
    (((SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).map
      (hU W).choose)

/-- In degree zero `Stacks.ChaoticSite.freeCollapse` is the augmentation, there being only one
map `Mor_C(U_0, W) → ∗`. -/
lemma freeCollapse_f_zero (hU : IsPointResolution U) (W : C) :
    (freeCollapse U hU W).f 0 =
      AddCommGrpCat.free.map
        ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0)))) := by
  have h : ∀ x : U.obj (SimplexCategory.mk 0) ⟶ W,
      (hU W).choose.app (op (SimplexCategory.mk 0)) x =
        (yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0))) x := fun _ ↦ rfl
  exact congrArg AddCommGrpCat.free.map (ConcreteCategory.ext_apply h)

/-- `Stacks.ChaoticSite.freeCollapse` is a quasi-isomorphism. -/
lemma quasiIso_freeCollapse (hU : IsPointResolution U) (W : C) :
    QuasiIso (freeCollapse U hU W) :=
  homotopyEquivalences_le_quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ) _
    (AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map
      (SimplicialObject.homotopyEquivalences_whiskering_map AddCommGrpCat.free
        (hU W).choose_spec))

/-- The comparison `H_0 ≅ opcycles 0` of chain complexes is natural. -/
private theorem homologyMap_comp_isoHomologyι₀_hom {K L : ChainComplex AddCommGrpCat.{u} ℕ}
    (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ (ChainComplex.isoHomologyι₀ L).hom =
      (ChainComplex.isoHomologyι₀ K).hom ≫ HomologicalComplex.opcyclesMap φ 0 := by
  rw [← cancel_epi (ChainComplex.isoHomologyι₀ K).inv,
    Iso.inv_hom_id_assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The map induced by `Stacks.ChaoticSite.freeCollapse` on degree-zero opcycles is an
isomorphism. -/
lemma isIso_opcyclesMap_freeCollapse (hU : IsPointResolution U) (W : C) :
    IsIso (HomologicalComplex.opcyclesMap (freeCollapse U hU W) 0) := by
  have h0 : IsIso (HomologicalComplex.homologyMap (freeCollapse U hU W) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 0).mp ((quasiIso_freeCollapse U hU W).quasiIsoAt 0)
  have heq : HomologicalComplex.opcyclesMap (freeCollapse U hU W) 0 =
      (ChainComplex.isoHomologyι₀ _).inv ≫
        HomologicalComplex.homologyMap (freeCollapse U hU W) 0 ≫
          (ChainComplex.isoHomologyι₀ _).hom := by
    rw [homologyMap_comp_isoHomologyι₀_hom, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- **Every map out of `ℤ^{Mor_C(U_0, W)}` killing the degree-one differential of
`j_{W!}ℤ_W(U_•)` factors through the augmentation.** -/
theorem exists_comp_freeAugmentation (hU : IsPointResolution U) (W : C) {T : AddCommGrpCat.{u}}
    (L : ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).X 0 ⟶ T)
    (hL : ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).d 1 0 ≫ L = 0) :
    ∃ m : AddCommGrpCat.free.obj PUnit.{u + 1} ⟶ T,
      AddCommGrpCat.free.map
          ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0)))) ≫ m = L := by
  have := isIso_opcyclesMap_freeCollapse U hU W
  refine ⟨HomologicalComplex.pOpcycles constFreeMooreComplex.{u} 0 ≫
    inv (HomologicalComplex.opcyclesMap (freeCollapse U hU W) 0) ≫
      ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).descOpcycles L 1
        (by simp) hL, ?_⟩
  rw [← freeCollapse_f_zero U hU W]
  erw [← HomologicalComplex.p_opcyclesMap_assoc,
    IsIso.hom_inv_id_assoc, HomologicalComplex.p_descOpcycles]

/-! ### The degree-zero identification for an arbitrary abelian presheaf -/

/-- **A point resolution admits a morphism `U_0 ⟶ W` for every object `W`.** -/
lemma nonempty_hom_of_isPointResolution (hU : IsPointResolution U) (W : C) :
    Nonempty (U.obj (SimplexCategory.mk 0) ⟶ W) := by
  obtain ⟨b, -, -⟩ := (hU W).choose_spec
  exact ⟨b.app (op (SimplexCategory.mk 0)) PUnit.unit⟩

/-- A chosen morphism `U_0 ⟶ W`. -/
def pointResolutionHom (hU : IsPointResolution U) (W : C) : U.obj (SimplexCategory.mk 0) ⟶ W :=
  (nonempty_hom_of_isPointResolution U hU W).some

/-- The value of `Stacks.CategoryHomology.freeRepresentableHom` on a generator: the restriction
of the section along that morphism. -/
lemma freeRepresentableHom_app_apply_of {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (W : C)
    (s : G.obj (op W)) (Y : Cᵒᵖ) (g : Y.unop ⟶ W) :
    (freeRepresentableHom W s).app Y (FreeAbelianGroup.of g) = (G.map g.op) s := by
  change (FreeAbelianGroup.lift fun k : Y.unop ⟶ W ↦ (G.map k.op) s)
      (FreeAbelianGroup.of g) = _
  rw [FreeAbelianGroup.lift_apply_of]

/-- The augmentation sends every generator to the generator of `ℤ`. -/
lemma freeAugmentation_apply_of (W : C) (Y : Cᵒᵖ) (g : Y.unop ⟶ W) :
    (AddCommGrpCat.free.map ((yonedaPointCocone W).ι.app Y)) (FreeAbelianGroup.of g) =
      FreeAbelianGroup.of PUnit.unit := by
  rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  rfl

/-- **Any two morphisms `U_0 ⟶ W` restrict identically into a map killing the degree-one
differential of `ℱ(U_•)`.** -/
theorem map_op_comp_eq_of_isPointResolution (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) {T : AddCommGrpCat.{u}}
    (h : G.obj (op (U.obj (SimplexCategory.mk 0))) ⟶ T)
    (hh : ((cosimplicialMooreComplex U).obj G).d 1 0 ≫ h = 0) {W : C}
    (g g' : U.obj (SimplexCategory.mk 0) ⟶ W) :
    G.map g.op ≫ h = G.map g'.op ≫ h := by
  refine ConcreteCategory.ext_apply fun s ↦ ?_
  have hd : ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).d 1 0 ≫
      (((cosimplicialMooreComplex U).map (freeRepresentableHom W s)).f 0 ≫ h) = 0 := by
    rw [← Category.assoc, ← ((cosimplicialMooreComplex U).map (freeRepresentableHom W s)).comm 1 0,
      Category.assoc, hh, comp_zero]
  obtain ⟨m, hm⟩ := exists_comp_freeAugmentation U hU W _ hd
  have key : ∀ g'' : U.obj (SimplexCategory.mk 0) ⟶ W,
      (G.map g''.op ≫ h) s = m (FreeAbelianGroup.of PUnit.unit) := by
    intro g''
    have h1 := ConcreteCategory.congr_hom hm (FreeAbelianGroup.of g'')
    have hA : (AddCommGrpCat.free.map ((yonedaPointCocone W).ι.app
        (op (U.obj (SimplexCategory.mk 0)))) ≫ m) (FreeAbelianGroup.of g'')
          = m (FreeAbelianGroup.of PUnit.unit) :=
      (ConcreteCategory.comp_apply _ _ _).trans
        (congrArg (fun z ↦ m z) (freeAugmentation_apply_of W _ g''))
    have hB : (((cosimplicialMooreComplex U).map (freeRepresentableHom W s)).f 0 ≫ h)
        (FreeAbelianGroup.of g'') = (G.map g''.op ≫ h) s :=
      (ConcreteCategory.comp_apply _ _ _).trans
        ((congrArg (fun z ↦ h z)
            (freeRepresentableHom_app_apply_of W s (op (U.obj (SimplexCategory.mk 0))) g'')).trans
          (ConcreteCategory.comp_apply _ _ _).symm)
    exact (hB.symm.trans h1.symm).trans hA
  exact (key g).trans (key g').symm

/-- The cocone on `ℱ` attached to a map out of `ℱ(U_0)` killing the degree-one differential: over
`V` it is the restriction along a chosen morphism `U_0 ⟶ V`. -/
def colimitιCocone (hU : IsPointResolution U) (G : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    {T : AddCommGrpCat.{u}} (h : G.obj (op (U.obj (SimplexCategory.mk 0))) ⟶ T)
    (hh : ((cosimplicialMooreComplex U).obj G).d 1 0 ≫ h = 0) : Cocone G where
  pt := T
  ι :=
    { app Y := G.map (pointResolutionHom U hU Y.unop).op ≫ h
      naturality Y Y' φ := by
        change G.map φ ≫ G.map (pointResolutionHom U hU Y'.unop).op ≫ h =
          (G.map (pointResolutionHom U hU Y.unop).op ≫ h) ≫ 𝟙 T
        rw [Category.comp_id, ← Category.assoc, ← G.map_comp,
          show φ ≫ (pointResolutionHom U hU Y'.unop).op =
            (pointResolutionHom U hU Y'.unop ≫ φ.unop).op from rfl]
        exact map_op_comp_eq_of_isPointResolution U hU G h hh _ _ }

/-- The colimit injection at `U_0` is a cokernel of the degree-one differential of `ℱ(U_•)`. -/
def colimitι_isColimit (hU : IsPointResolution U) (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsColimit (CokernelCofork.ofπ (colimit.ι G (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι U G)) :=
  Cofork.IsColimit.mk _
    (fun S ↦ colimit.desc G (colimitιCocone U hU G S.π (CokernelCofork.condition S)))
    (fun S ↦ by
      refine (colimit.ι_desc _ _).trans ?_
      refine (map_op_comp_eq_of_isPointResolution U hU G S.π (CokernelCofork.condition S)
        (pointResolutionHom U hU (U.obj (SimplexCategory.mk 0))) (𝟙 _)).trans ?_
      simp)
    (fun S m hm ↦ by
      have key : ∀ m' : colimit G ⟶ S.pt,
          colimit.ι G (op (U.obj (SimplexCategory.mk 0))) ≫ m' = S.π →
            m' = colimit.desc G (colimitιCocone U hU G S.π (CokernelCofork.condition S)) := by
        intro m' hm'
        refine colimit.hom_ext fun Y ↦ ?_
        refine Eq.trans ?_
          (colimit.ι_desc (colimitιCocone U hU G S.π (CokernelCofork.condition S)) Y).symm
        rw [← colimit.w G (pointResolutionHom U hU Y.unop).op, Category.assoc, hm']
        rfl
      exact key m hm)

/-- **`H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`, at the level of degree-zero opcycles.** -/
def cosimplicialOpcyclesZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((cosimplicialMooreComplex U).obj G).opcycles 0 ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.opcyclesIsCokernel ((cosimplicialMooreComplex U).obj G) 1 0 (by simp))
    (colimitι_isColimit U hU G)

/-- `Stacks.ChaoticSite.cosimplicialOpcyclesZeroIsoColim` is compatible with the colimit
injection at `U_0`. -/
lemma pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((cosimplicialMooreComplex U).obj G).pOpcycles 0 ≫
        (cosimplicialOpcyclesZeroIsoColim U hU G).hom =
      colimit.ι G (op (U.obj (SimplexCategory.mk 0))) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (HomologicalComplex.opcyclesIsCokernel ((cosimplicialMooreComplex U).obj G) 1 0 (by simp))
    (colimitι_isColimit U hU G) WalkingParallelPair.one

/-- **The degree-zero comparison on `j_{W!}ℤ_W` is the canonical map.** Read on degree-zero
chains, the identification of `H_0(j_{W!}ℤ_W(U_•))` with `π_!j_{W!}ℤ_W = ℤ` is the free abelian
group functor applied to `Mor_C(U_0, W) → ∗`. -/
lemma pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim_free (hU : IsPointResolution U) (W : C) :
    ((cosimplicialMooreComplex U).obj (freeRepresentablePresheaf W)).pOpcycles 0 ≫
        (cosimplicialOpcyclesZeroIsoColim U hU (freeRepresentablePresheaf W)).hom ≫
          (colimitFreeRepresentablePresheafIso W).hom =
      AddCommGrpCat.free.map
        ((yonedaPointCocone W).ι.app (op (U.obj (SimplexCategory.mk 0)))) := by
  rw [← Category.assoc, pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim,
    colimitι_comp_colimitFreeRepresentablePresheafIso_hom]

/-- **`H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`**, the comparison being induced by the colimit injection at
`U_0`. -/
def cosimplicialHomologyZeroIsoColim (hU : IsPointResolution U)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((cosimplicialMooreComplex U).obj G).homology 0 ≅ colimit G :=
  ChainComplex.isoHomologyι₀ ((cosimplicialMooreComplex U).obj G) ≪≫
    cosimplicialOpcyclesZeroIsoColim U hU G

/-- `Stacks.ChaoticSite.cosimplicialHomologyZeroIsoColim` is natural in the abelian
presheaf. -/
lemma cosimplicialHomologyZeroIsoColim_naturality (hU : IsPointResolution U)
    {G G' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : G ⟶ G') :
    HomologicalComplex.homologyMap ((cosimplicialMooreComplex U).map α) 0 ≫
        (cosimplicialHomologyZeroIsoColim U hU G').hom =
      (cosimplicialHomologyZeroIsoColim U hU G).hom ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).map α := by
  have hop : HomologicalComplex.opcyclesMap ((cosimplicialMooreComplex U).map α) 0 ≫
      (cosimplicialOpcyclesZeroIsoColim U hU G').hom =
        (cosimplicialOpcyclesZeroIsoColim U hU G).hom ≫
          (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).map α := by
    rw [← cancel_epi (((cosimplicialMooreComplex U).obj G).pOpcycles 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim, ← Category.assoc,
      pOpcycles_comp_cosimplicialOpcyclesZeroIsoColim]
    exact (colimit.ι_map α (op (U.obj (SimplexCategory.mk 0)))).symm
  have hhom : HomologicalComplex.homologyMap ((cosimplicialMooreComplex U).map α) 0 ≫
      (ChainComplex.isoHomologyι₀ ((cosimplicialMooreComplex U).obj G')).hom =
        (ChainComplex.isoHomologyι₀ ((cosimplicialMooreComplex U).obj G)).hom ≫
          HomologicalComplex.opcyclesMap ((cosimplicialMooreComplex U).map α) 0 := by
    exact homologyMap_comp_isoHomologyι₀_hom _
  calc HomologicalComplex.homologyMap ((cosimplicialMooreComplex U).map α) 0 ≫
        (cosimplicialHomologyZeroIsoColim U hU G').hom
      = (HomologicalComplex.homologyMap ((cosimplicialMooreComplex U).map α) 0 ≫
          (ChainComplex.isoHomologyι₀ ((cosimplicialMooreComplex U).obj G')).hom) ≫
            (cosimplicialOpcyclesZeroIsoColim U hU G').hom := by
        rw [cosimplicialHomologyZeroIsoColim, Iso.trans_hom, Category.assoc]
    _ = (ChainComplex.isoHomologyι₀ ((cosimplicialMooreComplex U).obj G)).hom ≫
          (HomologicalComplex.opcyclesMap ((cosimplicialMooreComplex U).map α) 0 ≫
            (cosimplicialOpcyclesZeroIsoColim U hU G').hom) := by
        rw [hhom, Category.assoc]
    _ = (cosimplicialHomologyZeroIsoColim U hU G).hom ≫
          (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).map α := by
        rw [hop, cosimplicialHomologyZeroIsoColim, Iso.trans_hom, Category.assoc]

/-- **`H_0(ℱ(U_•)) = colim_{Cᵒᵖ}ℱ`, naturally in `ℱ`**, by the canonical comparison. -/
def cosimplicialHomologyZeroNatIsoColim (hU : IsPointResolution U) :
    (cosimplicialHomologyDeltaFunctor U).functor 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun G ↦ cosimplicialHomologyZeroIsoColim U hU G)
    fun α ↦ cosimplicialHomologyZeroIsoColim_naturality U hU α

/-- Let `U_•` be a cosimplicial object of a small category `C` such that every simplicial set
`Mor_C(U_•, W)` is homotopy equivalent to a singleton. For every abelian presheaf `ℱ` the
homology `L_nπ_!` of `C` with coefficients `ℱ` is the homology of the Moore complex of `ℱ(U_•)`,
naturally in `ℱ`. -/
@[stacks 08Q9]
def leftDerivedColimitNatIso (hU : IsPointResolution U) (n : ℕ) :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n ≅
      cosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  leftDerivedColimitNatIsoOfVanishing U (cosimplicialHomologyZeroNatIsoColim U hU)
    (fun m P _ ↦ isZero_cosimplicialHomology_projective_succ U hU m P) n


end Stacks.ChaoticSite

end
