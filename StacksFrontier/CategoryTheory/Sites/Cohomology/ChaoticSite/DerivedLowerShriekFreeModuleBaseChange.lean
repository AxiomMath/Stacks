module

public import Mathlib.Algebra.Category.Ring.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StandardSimplexContractible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Change of structure rings on a free module, for derived lower shriek

Let `C` be a small category with the chaotic topology, so that the homology groups
`L_nπ_!(ℱ) = H_n(C, ℱ)` of an abelian sheaf are the left derived functors of the colimit over
`Cᵒᵖ` ([Stacks, Tag 08PF]), and let `U_•` be a cosimplicial object of `C` which is a *point
resolution*: every simplicial set `Mor_C(U_•, W)` is homotopy equivalent to a singleton. For
such a `U_•` the homology of `C` is the homology of the Moore complex of the evaluation on
`U_•` ([Stacks, Tag 08Q9]).

Let `φ : F ⟶ G` be a map of abelian sheaves on `C` which `L_nπ_!` inverts in every degree. Then
`L_nπ_!` also inverts the induced map of copowers
`∐_{Mor_C(-, W)} F(-) ⟶ ∐_{Mor_C(-, W)} G(-)`
for every object `W` of `C`. For the underlying map of abelian sheaves of a map of sheaves of
rings `O ⟶ O'`, the two copowers are the abelian sheaves underlying the free `O`-module
`j_{W!}O_W` on a representable and its base change `j_{W!}O'_W`.

The site `Δ` has the point resolution `U_• = 𝟭`, which gives the corresponding statement for a
homomorphism of simplicial rings.

## Main definitions

* `Stacks.ChaoticSite.mooreHomologyFunctor`: the homology of the Moore complex of a simplicial
  object of an abelian category, in a fixed degree, as a functor.

## Main results

* `Stacks.ChaoticSite.isIso_mooreHomologyFunctor_map_copowerMap`: over an arbitrary abelian
  category, a map of simplicial objects inverted by the degree-`n` homology of the Moore complex
  stays inverted after multiplication by a simplicial set homotopy equivalent to a singleton.
* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff`: a map of abelian sheaves is inverted by
  `L_nπ_!` exactly when the degree-`n` homology of the Moore complex of its evaluation on `U_•`
  inverts it.
* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerMap` and
  `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_freeModule`: the statement on a chaotic
  site, for a map of abelian sheaves and for the underlying map of a map of sheaves of rings.
* `Stacks.ChaoticSite.isPointResolution_id_simplexCategory`: `Δ` with `U_• = 𝟭` is a point
  resolution.
* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_simplicialFreeModule`: the statement at the
  site `Δ`, for a homomorphism of simplicial rings.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
* [Stacks Project, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe w v u

/-! ### The mechanism, over an arbitrary abelian category -/

/-- The homology of the Moore complex of a simplicial object in a fixed degree, as a functor
of the simplicial object. -/
abbrev mooreHomologyFunctor (A : Type u) [Category.{v} A] [Abelian A] (n : ℕ) :
    SimplicialObject A ⥤ A :=
  alternatingFaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n

section Mechanism

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A homotopy equivalence of simplicial objects is inverted by the homology of the Moore
complex in every degree. -/
lemma isIso_mooreHomologyFunctor_map_of_homotopyEquivalences {P P' : SimplicialObject A}
    {a : P ⟶ P'} (ha : SimplicialObject.homotopyEquivalences A a) (n : ℕ) :
    IsIso ((mooreHomologyFunctor A n).map a) := by
  have hq : QuasiIso ((alternatingFaceMapComplex A).map a) :=
    homotopyEquivalences_le_quasiIso A (ComplexShape.down ℕ) _
      (homotopyEquivalences_alternatingFaceMapComplex_map ha)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)

omit [Abelian A] in
/-- If a functor sends the right, left and bottom edges of a commutative square to isomorphisms,
it sends the top edge to an isomorphism. -/
private lemma isIso_map_of_sq {B : Type*} [Category B] (F : A ⥤ B) {X Y Z T : A}
    (x : X ⟶ Y) (y : Y ⟶ T) (z : X ⟶ Z) (t : Z ⟶ T) (hsq : x ≫ y = z ≫ t)
    [IsIso (F.map y)] [IsIso (F.map z)] [IsIso (F.map t)] : IsIso (F.map x) := by
  have hx : F.map x = F.map z ≫ F.map t ≫ inv (F.map y) := by
    rw [← Category.assoc, ← F.map_comp, ← hsq, F.map_comp, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [hx]
  infer_instance

variable {P P' : SimplicialObject A} (ψ : P ⟶ P')
  {S : SimplicialObject (Type w)}
  {a : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}}
  [∀ j, HasCoproduct fun _ : S.obj j => P.obj j]
  [∀ j, HasCoproduct fun _ : S.obj j => P'.obj j]
  [∀ j, HasCoproduct
    fun _ : ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}).obj j => P.obj j]
  [∀ j, HasCoproduct
    fun _ : ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}).obj j => P'.obj j]

/-- A map of simplicial objects inverted in degree `n` by the homology of the Moore complex stays
inverted after multiplication by the constant simplicial set on a singleton. -/
private lemma isIso_mooreHomologyFunctor_map_copowerMap_const (n : ℕ)
    (hψ : IsIso ((mooreHomologyFunctor A n).map ψ)) :
    IsIso ((mooreHomologyFunctor A n).map
      (Functor.copowerMap ψ (𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1})))) := by
  exact isIso_map_of_sq (mooreHomologyFunctor A n) _ _ _ _
    (Functor.copowerMap_comp_copowerProj ψ
      (𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1})))

/-- **A map of simplicial objects inverted in degree `n` by the homology of the Moore complex
stays inverted after multiplication by a contractible simplicial set.** Here `S` is given
together with a homotopy equivalence `S ⟶ ∗` onto the constant simplicial set on a
singleton. -/
theorem isIso_mooreHomologyFunctor_map_copowerMap
    (ha : SimplicialObject.homotopyEquivalences (Type w) a) (n : ℕ)
    (hψ : IsIso ((mooreHomologyFunctor A n).map ψ)) :
    IsIso ((mooreHomologyFunctor A n).map (Functor.copowerMap ψ (𝟙 S))) := by
  have hsq : Functor.copowerMap ψ (𝟙 S) ≫ Functor.copowerMap (𝟙 P') a =
      Functor.copowerMap (𝟙 P) a ≫
        Functor.copowerMap ψ (𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1})) := by
    rw [Functor.copowerMap_comp, Functor.copowerMap_comp, Category.comp_id, Category.id_comp,
      Category.comp_id, Category.id_comp]
  have : IsIso ((mooreHomologyFunctor A n).map (Functor.copowerMap (𝟙 P) a)) :=
    isIso_mooreHomologyFunctor_map_of_homotopyEquivalences
      (SimplicialObject.homotopyEquivalences_copowerMap_id P ha) n
  have : IsIso ((mooreHomologyFunctor A n).map (Functor.copowerMap (𝟙 P') a)) :=
    isIso_mooreHomologyFunctor_map_of_homotopyEquivalences
      (SimplicialObject.homotopyEquivalences_copowerMap_id P' ha) n
  have : IsIso ((mooreHomologyFunctor A n).map
      (Functor.copowerMap ψ (𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1})))) :=
    isIso_mooreHomologyFunctor_map_copowerMap_const ψ n hψ
  exact isIso_map_of_sq (mooreHomologyFunctor A n) _ _ _ _ hsq

end Mechanism

/-! ### Derived lower shriek of a free module on a chaotic site -/

section ChaoticSite

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- A map of abelian sheaves on a chaotic site with a
cosimplicial point resolution `U_•` is inverted by `L_nπ_!` exactly when it is inverted by the
degree-`n` homology of the Moore complex of its evaluation on `U_•`. -/
lemma isIso_leftDerivedColimit_map_iff (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map φ) ↔
      IsIso ((mooreHomologyFunctor AddCommGrpCat.{u} n).map
        (Functor.whiskerLeft U.op φ)) :=
  NatIso.isIso_map_iff (leftDerivedColimitNatIso U hU n) φ

/-- **Copowers by a representable and derived lower shriek.** Let `U_•` be a
cosimplicial point resolution of a small category `C` with the chaotic topology and let
`φ : F ⟶ G` be a map of abelian sheaves on `C` inverted by `L_nπ_!` in every degree. Then for
every object `W` the induced map on the copowers `∐_{Mor_C(-, W)} F(-) ⟶ ∐_{Mor_C(-, W)} G(-)`
is inverted by `L_nπ_!` in every degree. -/
theorem isIso_leftDerivedColimit_map_copowerMap (hU : IsPointResolution U) (W : C)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ G)
    (hφ : ∀ n, IsIso
      (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map φ))
    (n : ℕ) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
      (Functor.copowerMap φ (𝟙 (yoneda.obj W)))) := by
  obtain ⟨a, ha⟩ := hU W
  rw [isIso_leftDerivedColimit_map_iff U hU]
  have hwl : Functor.whiskerLeft U.op (Functor.copowerMap φ (𝟙 (yoneda.obj W))) =
      Functor.copowerMap (Functor.whiskerLeft U.op φ) (𝟙 (U.op ⋙ yoneda.obj W)) := rfl
  rw [hwl]
  exact isIso_mooreHomologyFunctor_map_copowerMap _ ha n
    ((isIso_leftDerivedColimit_map_iff U hU φ n).mp (hφ n))

/-- **Change of structure rings on a free module, for derived lower shriek on a chaotic
site.** Let `C` be a small category with the chaotic topology, let `U_•` be a cosimplicial
point resolution of `C`, and let `O ⟶ O'` be a map of sheaves of rings on `C` whose underlying
map of abelian sheaves is inverted by `L_nπ_!` in every degree. Then for every object `W` the
induced map `∐_{Mor_C(-, W)} O(-) ⟶ ∐_{Mor_C(-, W)} O'(-)` is inverted by `L_nπ_!` in every
degree. These two copowers are the abelian sheaves underlying the free module `j_{W!}O_W` and
its base change `j_{W!}O'_W`. -/
theorem isIso_leftDerivedColimit_map_freeModule (hU : IsPointResolution U) (W : C)
    {O O' : Cᵒᵖ ⥤ RingCat.{u}} (f : O ⟶ O')
    (hf : ∀ n, IsIso
      (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
        (Functor.whiskerRight f (forget₂ RingCat.{u} AddCommGrpCat.{u}))))
    (n : ℕ) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
      (Functor.copowerMap (Functor.whiskerRight f (forget₂ RingCat.{u} AddCommGrpCat.{u}))
        (𝟙 (yoneda.obj W)))) :=
  isIso_leftDerivedColimit_map_copowerMap U hU W _ hf n

end ChaoticSite

/-! ### The fibre category `Δ` of a simplicial situation -/

/-- The simplicial set `Mor_Δ(⦋•⦌, W)` is the standard simplex on `W`, up to the universe lift
in Mathlib's `SSet.stdSimplex`. -/
@[sga "4 V 7.3.1.6"]
private def yonedaIsoStdSimplex (W : SimplexCategory) :
    (𝟭 SimplexCategory).op ⋙ yoneda.obj W ≅ (SSet.stdSimplex.{0}).obj W :=
  NatIso.ofComponents (fun _ => Equiv.ulift.symm.toIso) (by intros; rfl)

/-- The simplicial set `Mor_Δ(⦋•⦌, ⦋0⦌)` is the constant simplicial set on a singleton. -/
private def yonedaZeroIsoConst :
    (𝟭 SimplexCategory).op ⋙ yoneda.obj ⦋0⦌ ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{1} :=
  NatIso.ofComponents (fun x => Equiv.toIso (Equiv.equivPUnit (unop x ⟶ ⦋0⦌)))
    (by intros; ext; rfl)

/-- **`Δ` with `U_• = 𝟭` is a cosimplicial point resolution.** -/
theorem isPointResolution_id_simplexCategory :
    IsPointResolution (𝟭 SimplexCategory) := fun W =>
  ⟨_, SimplicialObject.homotopyEquivalences_iso_comp_iso (yonedaIsoStdSimplex W)
    ((SSet.stdSimplex.{0}).map (default : W ⟶ ⦋0⦌))
    ((yonedaIsoStdSimplex ⦋0⦌).symm ≪≫ yonedaZeroIsoConst)
    ((SSet.stdSimplex.homotopyEquivalences_hom_obj₀ W.len).1 _)⟩

/-- **Change of structure rings on a free simplicial module.** Let `A_• ⟶ B_•` be a
homomorphism of simplicial rings whose underlying map of simplicial abelian groups is inverted
by `L_nπ_!` in every degree, for the site `Δ` with the chaotic topology. Then for every `⦋m⦌`
the induced map `∐_{Mor_Δ(-, ⦋m⦌)} A_•(-) ⟶ ∐_{Mor_Δ(-, ⦋m⦌)} B_•(-)` is inverted by `L_nπ_!`
in every degree. -/
theorem isIso_leftDerivedColimit_map_simplicialFreeModule (m : ℕ)
    {A B : SimplicialObject RingCat.{0}} (f : A ⟶ B)
    (hf : ∀ n, IsIso
      (((colim : (SimplexCategoryᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0}).leftDerived
        n).map (Functor.whiskerRight f (forget₂ RingCat.{0} AddCommGrpCat.{0}))))
    (n : ℕ) :
    IsIso (((colim : (SimplexCategoryᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0}).leftDerived
      n).map (Functor.copowerMap
        (Functor.whiskerRight f (forget₂ RingCat.{0} AddCommGrpCat.{0}))
        (𝟙 (yoneda.obj ⦋m⦌)))) :=
  isIso_leftDerivedColimit_map_freeModule (𝟭 SimplexCategory)
    isPointResolution_id_simplexCategory ⦋m⦌ f hf n

end Stacks.ChaoticSite

end
