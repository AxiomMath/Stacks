module


public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Skyscraper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of algebraic structures and the extension `j_!`

Let `X` be a topological space, `j : U → X` the inclusion of an open subset, and `(C, F)` a
*type of algebraic structure*: a category `C` together with a faithful set-valued functor
`F : C ⥤ Type` such that `C` has limits and filtered colimits, both preserved by `F`. Assuming
that `C` has an initial object `e`, extension by `e` along `j` is left adjoint to restriction,
both on presheaves and on sheaves, and the stalks of an extended sheaf are the stalks of the
original sheaf at points of `U` and `e` at points outside `U`. This is
[Stacks, Tag 00A6](https://stacks.math.columbia.edu/tag/00A6).

## Main definitions

* `AlgebraicStructureType`: a category `C` together with a faithful functor `C ⥤ Type v` preserving
  small limits and small filtered colimits.
* `PShCategory`: the category of `S.C`-valued presheaves on `X`.
* `IsSheafOfAlgStruct`: the condition that the underlying presheaf of sets be a sheaf.
* `ShOfAlgStruct`: the category of sheaves of algebraic structures on `X`.
* `jpRestrict`: the presheaf restriction `j_p`, precomposition with `Opens U ⥤ Opens X`.
* `jInverseSheaf`: the sheaf restriction `j^{-1}`.
* `jpShriek00A6`: the presheaf extension `j_{p!}`, the left Kan extension along the open
  embedding, whose value is `𝓕(V)` on opens `V ⊆ U` and `e` on all other opens.
* `sheafify00A6`: sheafification of `S.C`-valued presheaves on `X`.
* `jShriek00A6`: the sheaf extension `j_!`, the sheafification of `j_{p!}`.
* `stalk00A6`: the stalk of a presheaf of algebraic structures at a point.

## Main results

* `statement_1_jp_adjoint`: `j_{p!} ⊣ j_p` on presheaves.
* `statement_2_jShriek_adjoint`: `Hom(j_!𝓕, 𝓖) ≃ Hom(𝓕, j^{-1}𝓖)` on sheaves.
* `statement_3_stalk_in_U`: `(j_!𝓕)_x ≅ 𝓕_x` for `x ∈ U`.
* `statement_3_stalk_off_U`: `(j_!𝓕)_x ≅ e` for `x ∉ U`.
* `statement_4_counit_presheaf`: `j_p ∘ j_{p!} ≅ 𝟭` on presheaves on `U`.
* `statement_5_counit_sheaf`: `j^{-1} ∘ j_! ≅ 𝟭` on sheaves on `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

variable (S : AlgebraicStructureType.{v, u}) (X : TopCat.{v}) (U : TopologicalSpace.Opens X)

/-- A presheaf of algebraic structures of type `S` on `X` is a `S.C`-valued presheaf,
i.e. a contravariant functor `Opens(X)ᵒᵖ ⥤ S.C`. -/
@[sga "3 IV 4.3.1" "special case",
  sga "3 IV 4.3.17" "special case",
  sga "4 I 1.2" "special case",
  sga "4 II 6.0" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
abbrev PShCategory : Type max u v := TopCat.Presheaf S.C X

/-- A presheaf `𝓕` of algebraic structures is a *sheaf* if its underlying presheaf of sets
`F ∘ 𝓕 : Opens(X)ᵒᵖ ⥤ Type v` is a sheaf of sets on `X`. -/
@[sga "3 IV 4.3.18" "special case", sga "4 II 6.1" "special case", sga "4 II 6.3.2" "special case"]
def IsSheafOfAlgStruct (𝓕 : PShCategory S X) : Prop :=
  TopCat.Presheaf.IsSheaf (𝓕 ⋙ S.F)

/-- The category of sheaves of algebraic structures, as the full subcategory of presheaves
satisfying the sheaf condition. -/
@[sga "3 IV 4.3.1" "partial", sga "4 II 6.3.2" "special case"]
abbrev ShOfAlgStruct : Type max u v :=
  { 𝓕 : PShCategory S X // IsSheafOfAlgStruct S X 𝓕 }

/-- The TopCat associated to an open subset. -/
abbrev openTopCat : TopCat.{v} := (Opens.toTopCat X).obj U

/-- The inclusion `j : U → X` as a TopCat morphism. -/
abbrev openIncl : openTopCat X U ⟶ X := U.inclusion'

/-- The functor `Opens U ⥤ Opens X` given by the open embedding `j : U ⥤ X`,
sending an open `V ⊆ U` to itself viewed as an open of `X`. -/
abbrev openEmbeddingFunctor : Opens (openTopCat X U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

/-- The open-embedding functor `Opens U ⥤ Opens X` is full: an inclusion between the images of
two opens of `U` is the image of an inclusion between them. -/
instance openEmbFull : (openEmbeddingFunctor X U).Full := by
  constructor
  intro a b f
  refine ⟨homOfLE (fun ⟨x, hx⟩ hxa => ?_), rfl⟩
  obtain ⟨⟨y, hy⟩, hyb, rfl⟩ :=
    leOfHom f (show x ∈ ((openEmbeddingFunctor X U).obj a).carrier from ⟨⟨x, hx⟩, hxa, rfl⟩)
  exact hyb

/-! ### Restriction -/

/-- The presheaf restriction functor
`j_p : PShCategory(X, C) → PShCategory(U, C)`, `𝓖 ↦ 𝓖|_U`, defined by precomposition with the
open-embedding functor `Opens U → Opens X`. -/
@[ega "0 3.1.5", sga "3 I 2.1.1" "restriction G ↦ G_S", sga "3 IV 4.3.17" "special case"]
def jpRestrict : PShCategory S X ⥤ PShCategory S (openTopCat X U) :=
  (Functor.whiskeringLeft _ _ S.C).obj (openEmbeddingFunctor X U).op

/-- The restriction of a sheaf along an open inclusion is again a sheaf. -/
@[ega "0 3.1.5" "special case"]
theorem jpRestrict_isSheaf (𝓖 : ShOfAlgStruct S X) :
    IsSheafOfAlgStruct S (openTopCat X U) ((jpRestrict S X U).obj 𝓖.1) := by
  unfold IsSheafOfAlgStruct
  have heq : (jpRestrict S X U).obj 𝓖.1 ⋙ S.F = (openEmbeddingFunctor X U).op ⋙ (𝓖.1 ⋙ S.F) := by
    simp only [jpRestrict, Functor.whiskeringLeft]
    exact Functor.assoc _ _ _
  rw [heq]
  have := Topology.IsOpenEmbedding.functor_isContinuous (Opens.isOpenEmbedding U)
  exact Functor.op_comp_isSheaf_of_isSheaf (openEmbeddingFunctor X U)
    (Opens.grothendieckTopology (openTopCat X U))
    (Opens.grothendieckTopology X)
    (𝓖.1 ⋙ S.F) 𝓖.2

/-- The sheaf restriction functor `j^{-1} : Sh(X, C) → Sh(U, C)`, sending a sheaf to its
presheaf restriction along the open inclusion. -/
@[ega "0 3.1.5", ega "0 3.7.1" "special case", sga "4 III 1.9.2", sga "4 III 5.3" "special case"]
def jInverseSheaf : ShOfAlgStruct S X → ShOfAlgStruct S (openTopCat X U) :=
  fun 𝓖 => ⟨(jpRestrict S X U).obj 𝓖.1, jpRestrict_isSheaf S X U 𝓖⟩

/-! ### Extension by the initial object on presheaves -/

variable [HasInitial S.C]

private noncomputable def liftToU' (V : Opens X) : Opens (openTopCat X U) :=
  ⟨Subtype.val ⁻¹' V.carrier, V.2.preimage continuous_subtype_val⟩

private lemma embed_liftToU' (V : Opens X) (hV : V ≤ U) :
    (openEmbeddingFunctor X U).obj (liftToU' X U V) = V := by
  ext x
  simp only [openEmbeddingFunctor, Topology.IsOpenEmbedding.functor, liftToU', Opens.carrier_eq_coe,
    IsOpenMap.coe_functor_obj, Opens.coe_inclusion', Opens.coe_mk,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy⟩, hym, rfl⟩
    exact hym
  · exact fun hx => ⟨⟨x, hV hx⟩, hx, rfl⟩

private lemma embed_carrier_eq' (W : Opens (openTopCat X U)) :
    ((openEmbeddingFunctor X U).obj W).carrier = Subtype.val '' W.carrier :=
  rfl

private lemma embed_le_U' (W : Opens (openTopCat X U)) :
    (openEmbeddingFunctor X U).obj W ≤ U :=
  Subtype.coe_image_subset _ _

private lemma liftToU_le_of_embed' (V : Opens X)
    (W : Opens (openTopCat X U)) (hW : V ≤ (openEmbeddingFunctor X U).obj W) :
    liftToU' X U V ≤ W := by
  intro ⟨x, hxU⟩ hx
  simp only [liftToU', Opens.carrier_eq_coe] at hx
  obtain ⟨⟨z, hz⟩, hzW, rfl⟩ := (embed_carrier_eq' X U W).le (hW hx)
  exact hzW

private lemma costructuredArrow_hasTerminal' (Y : (Opens X)ᵒᵖ) (h : Y.unop ≤ U) :
    HasTerminal (CostructuredArrow (openEmbeddingFunctor X U).op Y) := by
  let f : (openEmbeddingFunctor X U).op.obj (op (liftToU' X U Y.unop)) ⟶ Y :=
    (homOfLE (embed_liftToU' X U Y.unop h).ge).op
  exact IsTerminal.hasTerminal (X := CostructuredArrow.mk f) (IsTerminal.ofUniqueHom
    (fun a => CostructuredArrow.homMk (homOfLE (liftToU_le_of_embed' X U Y.unop a.left.unop
      (leOfHom a.hom.unop))).op (Subsingleton.elim _ _))
    (fun a g => CostructuredArrow.ext g _ (Subsingleton.elim _ _)))

private lemma costructuredArrow_isEmpty' (Y : (Opens X)ᵒᵖ) (h : ¬ Y.unop ≤ U) :
    IsEmpty (CostructuredArrow (openEmbeddingFunctor X U).op Y) :=
  ⟨fun a => h (le_trans (leOfHom a.hom.unop) (embed_le_U' X U a.left.unop))⟩

/-- Every `S.C`-valued presheaf on `U` has a pointwise left Kan extension along the opposite of
the open-embedding functor: at an open `V ⊆ U` the indexing category has a terminal object, and
at any other open it is empty, so the defining colimit exists in both cases. -/
instance openEmb_hasPointwiseLKE :
    ∀ (F : (Opens (openTopCat X U))ᵒᵖ ⥤ S.C),
      (openEmbeddingFunctor X U).op.HasPointwiseLeftKanExtension F := by
  intro F Y
  by_cases h : Y.unop ≤ U
  · have := costructuredArrow_hasTerminal' X U Y h
    exact hasColimit_of_domain_hasTerminal
  · have := costructuredArrow_isEmpty' X U Y h
    exact ⟨⟨⟨⊥_ S.C, ⟨fun j => (IsEmpty.false j).elim,
      fun {A B} f => (IsEmpty.false A).elim⟩⟩,
      ⟨fun s => initial.to s.pt, fun s j => (IsEmpty.false j).elim,
       fun s m _ => initial.hom_ext _ _⟩⟩⟩

/-- The presheaf extension by the initial object `j_{p!} : PShCategory(U, C) ⥤ PShCategory(X, C)`,
defined as the left Kan extension along the opposite of the open-embedding functor. Its value at
an open `V ⊆ U` is `𝓕(V)`, and its value at any other open is the initial object of `S.C`. -/
noncomputable def jpShriek00A6 : PShCategory S (openTopCat X U) ⥤ PShCategory S X :=
  (openEmbeddingFunctor X U).op.lan

/-- For a presheaf `𝓕` on `U` and an open `V` of `U`, the value of `j_{p!}𝓕` at the image of `V`
in `X` is isomorphic to `𝓕(V)`. -/
theorem jpShriek_value_on_U
    (𝓕 : PShCategory S (openTopCat X U)) (V : Opens (openTopCat X U)) :
    Nonempty (((jpShriek00A6 S X U).obj 𝓕).obj (op ((openEmbeddingFunctor X U).obj V))
              ≅ 𝓕.obj (op V)) :=
  ⟨((asIso ((Functor.lanUnit (openEmbeddingFunctor X U).op).app 𝓕)).app (op V)).symm⟩

/-- For an open `V` of `X` not contained in `U`, the value of `j_{p!}𝓕` at `V` is an initial object
of `S.C`: the colimit defining it is indexed by an empty category. -/
noncomputable def jpShriek_obj_isInitial (𝓕 : PShCategory S (openTopCat X U)) (V : Opens X)
    (hV : ¬ V ≤ U) : IsInitial (((jpShriek00A6 S X U).obj 𝓕).obj (op V)) :=
  have : IsEmpty (CostructuredArrow (openEmbeddingFunctor X U).op (op V)) :=
    ⟨fun a => hV ((leOfHom a.hom.unop).trans (Subtype.coe_image_subset _ _))⟩
  (isColimitEquivIsInitialOfIsEmpty S.C _ (colimit.isColimit _)).ofIso
    (Functor.leftKanExtensionObjIsoColimit (openEmbeddingFunctor X U).op 𝓕 (op V)).symm

/-- For an open `V` of `X` not contained in `U`, the value of `j_{p!}𝓕` at `V` is isomorphic to
the initial object of `S.C`. -/
theorem jpShriek_value_off_U
    (𝓕 : PShCategory S (openTopCat X U)) (V : Opens X) (hV : ¬ V ≤ U) :
    Nonempty (((jpShriek00A6 S X U).obj 𝓕).obj (op V) ≅ (⊥_ S.C)) :=
  ⟨(jpShriek_obj_isInitial S X U 𝓕 V hV).uniqueUpToIso initialIsInitial⟩

/-! ### Sheafification -/

/-- Sheafification of `S.C`-valued presheaves on `X`, given by the plus construction for the
Grothendieck topology of `X` applied twice. -/
@[sga "3 IV 4.3.15" "special case"]
noncomputable def sheafify00A6 : PShCategory S X ⥤ PShCategory S X :=
  (Opens.grothendieckTopology X).sheafification S.C

omit [HasInitial S.C] in
/-- Sheafification produces a sheaf. -/
@[sga "3 IV 4.3.14" "special case", sga "4 II 3.2" "Clause 3, special case"]
theorem sheafify_isSheaf00A6 (𝓕 : PShCategory S X) :
    IsSheafOfAlgStruct S X ((sheafify00A6 S X).obj 𝓕) := by
  unfold IsSheafOfAlgStruct sheafify00A6
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  rw [GrothendieckTopology.sheafification_obj, GrothendieckTopology.sheafify]
  have iso1 : J.plusObj (J.plusObj 𝓕) ⋙ S.F ≅ J.plusObj (J.plusObj 𝓕 ⋙ S.F) :=
    J.plusCompIso S.F (J.plusObj 𝓕)
  have iso2 : J.plusObj (J.plusObj 𝓕 ⋙ S.F) ≅ J.plusObj (J.plusObj (𝓕 ⋙ S.F)) :=
    (J.plusFunctor (Type v)).mapIso (J.plusCompIso S.F 𝓕)
  exact (Presheaf.isSheaf_of_iso_iff (iso1 ≪≫ iso2)).mpr (J.sheafify_isSheaf (𝓕 ⋙ S.F))

/-- The sheaf extension `j_! : Sh(U, C) → Sh(X, C)`, defined as the sheafification of the
presheaf extension `j_{p!}`. -/
@[sga "4 III 1.7", sga "4 III 5.3" "special case"]
noncomputable def jShriek00A6 : ShOfAlgStruct S (openTopCat X U) → ShOfAlgStruct S X :=
  fun 𝓕 => ⟨(sheafify00A6 S X).obj ((jpShriek00A6 S X U).obj 𝓕.1), sheafify_isSheaf00A6 S X _⟩

/-! ### Stalks -/

/-- The stalk of a presheaf of algebraic structures at a point, the colimit of its values over
the open neighbourhoods of that point. -/
@[ega "0 3.1.6" "special case"]
noncomputable def stalk00A6 [HasColimits S.C] (𝓕 : PShCategory S X) (x : X) : S.C :=
  TopCat.Presheaf.stalk 𝓕 x

omit [HasInitial S.C] in
/-- A presheaf of algebraic structures whose underlying presheaf of sets is a sheaf is a sheaf
for the Grothendieck topology of `X` in the categorical sense. -/
@[ega "0 3.1.3" "Converse, special case"]
lemma isSheaf_categorical [HasColimits S.C]
    (𝓖 : PShCategory S X) (h : IsSheafOfAlgStruct S X 𝓖) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) 𝓖 :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp S.F 𝓖).mpr h

omit [HasInitial S.C] in
/-- The plus construction does not change stalks: the stalk functor at `x` sends the unit
`Q ⟶ Q⁺` to an isomorphism. -/
lemma isIso_stalkFunctor_map_toPlus [HasColimits S.C] (Q : PShCategory S X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor S.C x).map
      ((Opens.grothendieckTopology (X : TopCat.{v})).toPlus Q)) := by
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  classical
  refine isIso_of_coyoneda_map_bijective _ fun A => ?_
  let adj : TopCat.Presheaf.stalkFunctor S.C x ⊣ skyscraperPresheafFunctor x :=
    skyscraperPresheafStalkAdjunction x (C := S.C)
  have hSheaf : Presheaf.IsSheaf J (skyscraperPresheaf x A) := skyscraperPresheaf_isSheaf x A
  have nat_left := fun (g : (TopCat.Presheaf.stalkFunctor S.C x).obj (J.plusObj Q) ⟶ A) =>
    adj.homEquiv_naturality_left (J.toPlus Q) g
  refine ⟨fun g₁ g₂ hg => ?_, fun g => ⟨(adj.homEquiv (J.plusObj Q) A).symm
    (J.plusLift (adj.homEquiv Q A g) hSheaf), (adj.homEquiv Q A).injective ?_⟩⟩
  · have hg' : J.toPlus Q ≫ adj.homEquiv (J.plusObj Q) A g₁ =
        J.toPlus Q ≫ adj.homEquiv (J.plusObj Q) A g₂ :=
      (nat_left g₁).symm.trans ((congr_arg (adj.homEquiv Q A) hg).trans (nat_left g₂))
    exact (adj.homEquiv (J.plusObj Q) A).injective
      ((J.plusLift_unique _ hSheaf _ rfl).trans (J.plusLift_unique _ hSheaf _ hg'.symm).symm)
  · rw [nat_left _, Equiv.apply_symm_apply]
    exact J.toPlus_plusLift _ hSheaf

/-- Sheafification preserves stalks: the stalk of `P` at `x` is isomorphic to the stalk of its
sheafification at `x`. -/
@[sga "4 IV 6.8.2" "special case"]
noncomputable def sheafify_stalk_iso [HasColimits S.C] (P : PShCategory S X) (x : X) :
    stalk00A6 S X P x ≅ stalk00A6 S X ((sheafify00A6 S X).obj P) x := by
  unfold stalk00A6 sheafify00A6
  rw [← TopCat.Presheaf.stalkFunctor_obj, ← TopCat.Presheaf.stalkFunctor_obj,
    GrothendieckTopology.sheafification_obj]
  have h₁ := isIso_stalkFunctor_map_toPlus S X P x
  have h₂ := isIso_stalkFunctor_map_toPlus S X
    ((Opens.grothendieckTopology (X : TopCat.{v})).plusObj P) x
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  suffices hIso : IsIso ((TopCat.Presheaf.stalkFunctor S.C x).map (J.toSheafify P)) from
    asIso ((TopCat.Presheaf.stalkFunctor S.C x).map (J.toSheafify P))
  change IsIso ((TopCat.Presheaf.stalkFunctor S.C x).map (J.toPlus P ≫ J.plusMap (J.toPlus P)))
  simp only [Functor.map_comp]
  rw [show (TopCat.Presheaf.stalkFunctor S.C x).map (J.plusMap (J.toPlus P)) =
      (TopCat.Presheaf.stalkFunctor S.C x).map (J.toPlus (J.plusObj P)) from
    ((cancel_epi ((TopCat.Presheaf.stalkFunctor S.C x).map (J.toPlus P))).mp
      (by rw [← Functor.map_comp, ← Functor.map_comp]
          exact congr_arg _ (J.toPlus_naturality (J.toPlus P)))).symm]
  exact IsIso.comp_isIso

/-- The open-embedding functor `Opens U ⥤ Opens X` is cocontinuous for the Grothendieck
topologies of `U` and of `X`. -/
@[sga "4 III 2.7" "cocontinuity of Φ"]
instance openEmbeddingFunctor_isCocontinuous :
    (openEmbeddingFunctor X U).IsCocontinuous
      (Opens.grothendieckTopology (openTopCat X U))
      (Opens.grothendieckTopology X) :=
  (Adjunction.isCocontinuous_iff_coverPreserving (J := Opens.grothendieckTopology _)
    (K := Opens.grothendieckTopology X)
    (Opens.isOpenEmbedding U).isOpenMap.adjunction).mpr
    (coverPreserving_opens_map U.inclusion')

/-- The open-embedding functor `Opens U ⥤ Opens X` is continuous for the Grothendieck topologies
of `U` and of `X`. -/
@[sga "4 III 1.9.2", sga "4 III 2.7" "continuity of Φ"]
instance openEmbeddingFunctor_isContinuous :
    (openEmbeddingFunctor X U).IsContinuous
      (Opens.grothendieckTopology (openTopCat X U))
      (Opens.grothendieckTopology X) :=
  Topology.IsOpenEmbedding.functor_isContinuous (Opens.isOpenEmbedding U)

omit [HasInitial S.C] in
/-- If the sheafification unit of the underlying presheaf of sets `P ⋙ S.F` is an isomorphism at
`W`, then so is the underlying-set map of the sheafification unit of `P` at `W`. -/
lemma isIso_F_map_toSheafify_app [HasColimits S.C] (P : PShCategory S X) (W : (Opens X)ᵒᵖ)
    (h : IsIso ((toSheafify (Opens.grothendieckTopology (X : TopCat.{v})) (P ⋙ S.F)).app W)) :
    IsIso (S.F.map (((Opens.grothendieckTopology (X : TopCat.{v})).toSheafify P).app W)) := by
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  set Q : (Opens X)ᵒᵖ ⥤ Type v := P ⋙ S.F
  have hpp : (J.toSheafify Q).app W ≫ ((plusPlusIsoSheafify J (Type v) Q).hom).app W =
      (toSheafify J Q).app W := by
    simpa only [NatTrans.comp_app] using
      NatTrans.congr_app (toSheafify_plusPlusIsoSheafify_hom (J := J) (D := Type v) Q) W
  have hJQ : IsIso ((J.toSheafify Q).app W) := IsIso.of_isIso_fac_right hpp
  have hwhisker : S.F.map ((J.toSheafify P).app W) ≫ ((J.sheafifyCompIso S.F P).hom).app W =
      (J.toSheafify Q).app W := by
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using
      NatTrans.congr_app (J.whiskerRight_toSheafify_sheafifyCompIso_hom S.F P) W
  exact IsIso.of_isIso_fac_right hwhisker

/-- For a `Type v`-valued presheaf `Q` on `X` whose restriction to `U` is a sheaf on `U`, the
sheafification unit of `Q` is an isomorphism at every open of `X` coming from an open of `U`. -/
lemma isIso_toSheafify_app_of_restrict_isSheaf (Q : (Opens X)ᵒᵖ ⥤ Type v)
    (hQ : Presheaf.IsSheaf (Opens.grothendieckTopology (openTopCat X U))
      ((openEmbeddingFunctor X U).op ⋙ Q))
    (V : (Opens (openTopCat X U))ᵒᵖ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (X : TopCat.{v})) Q).app
      ((openEmbeddingFunctor X U).op.obj V)) := by
  set Jp := Opens.grothendieckTopology (openTopCat X U)
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  set G := openEmbeddingFunctor X U
  have hIsoA : IsIso ((toSheafify Jp (G.op ⋙ Q)).app V) :=
    have := isIso_toSheafify Jp hQ
    NatIso.isIso_app_of_isIso _ _
  have hIsoBhom : IsIso (((G.pushforwardContinuousSheafificationCompatibility
      (Type v) Jp J).hom.app Q).hom) :=
    Functor.map_isIso (sheafToPresheaf Jp (Type v))
      ((G.pushforwardContinuousSheafificationCompatibility (Type v) Jp J).hom.app Q)
  rw [← show (toSheafify Jp (G.op ⋙ Q)).app V ≫
        (((G.pushforwardContinuousSheafificationCompatibility (Type v) Jp J).hom.app Q).hom).app V =
      (toSheafify J Q).app (G.op.obj V) by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using NatTrans.congr_app
      (G.toSheafify_pullbackSheafificationCompatibility (A := Type v) (J := Jp) (K := J) Q) V]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hIsoA (NatIso.isIso_app_of_isIso _ _)

omit [HasInitial S.C] in
/-- The restriction of the sheafification unit `toSheafify P` to an open subspace `U` is an
isomorphism when `P` restricted to `U` is already a sheaf on `U` in the categorical sense. -/
lemma toSheafify_restrict_isIso [HasColimits S.C] (P : PShCategory S X)
    (hShU : Presheaf.IsSheaf (Opens.grothendieckTopology (openTopCat X U))
      ((jpRestrict S X U).obj P)) :
    IsIso ((jpRestrict S X U).map
      ((Opens.grothendieckTopology X).toSheafify P)) := by
  have hSh : Presheaf.IsSheaf (Opens.grothendieckTopology (openTopCat X U))
      ((openEmbeddingFunctor X U).op ⋙ (P ⋙ S.F)) :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp S.F _).mp hShU
  suffices h : ∀ V, IsIso (((jpRestrict S X U).map
      ((Opens.grothendieckTopology X).toSheafify P)).app V) from NatIso.isIso_of_isIso_app _
  intro V
  have : IsIso (S.F.map (((jpRestrict S X U).map
      ((Opens.grothendieckTopology X).toSheafify P)).app V)) :=
    isIso_F_map_toSheafify_app S X P ((openEmbeddingFunctor X U).op.obj V)
      (isIso_toSheafify_app_of_restrict_isSheaf X U (P ⋙ S.F) hSh V)
  exact isIso_of_reflects_iso _ S.F

/-! ### Adjointness, stalks and the counit identities -/

variable [HasColimits S.C]

omit [HasColimits S.C] in
/-- Adjointness on presheaves: the extension `j_{p!} : PShCategory(U, C) ⥤ PShCategory(X, C)` is
left adjoint to the restriction `j_p : PShCategory(X, C) ⥤ PShCategory(U, C)`. -/
@[stacks_fixed 00A6 "(1)",
  sga "4 I 5.1" "special case",
  sga "4 I 5.8.3" "partial",
  sga "4 IV 9.2.4" "special case"]
theorem statement_1_jp_adjoint :
    Nonempty (jpShriek00A6 S X U ⊣ jpRestrict S X U) :=
  ⟨Functor.lanAdjunction _ _⟩

/-- Adjointness on sheaves: for a sheaf `𝓕` on `U` and a sheaf `𝓖` on `X` there is a bijection
`Hom(j_!𝓕, 𝓖) ≃ Hom(𝓕, j^{-1}𝓖)`. -/
@[stacks_fixed 00A6 "(2)", sga "4 XVII 5.1.1" "top. spaces, alg. struct"]
theorem statement_2_jShriek_adjoint :
    ∀ (𝓕 : ShOfAlgStruct S (openTopCat X U)) (𝓖 : ShOfAlgStruct S X),
      Nonempty ((((jShriek00A6 S X U) 𝓕).1 ⟶ 𝓖.1) ≃ (𝓕.1 ⟶ ((jInverseSheaf S X U) 𝓖).1)) := by
  intro 𝓕 𝓖
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  have hQ : Presheaf.IsSheaf J 𝓖.1 := isSheaf_categorical S X 𝓖.1 𝓖.2
  have sheafEquiv : (J.sheafify ((jpShriek00A6 S X U).obj 𝓕.1) ⟶ 𝓖.1) ≃
                    ((jpShriek00A6 S X U).obj 𝓕.1 ⟶ 𝓖.1) := {
    toFun := fun g => J.toSheafify _ ≫ g
    invFun := fun η => J.sheafifyLift η hQ
    left_inv := fun g => (J.sheafifyLift_unique _ hQ g rfl).symm
    right_inv := fun η => J.toSheafify_sheafifyLift η hQ
  }
  exact ⟨sheafEquiv.trans
    ((Functor.lanAdjunction (openEmbeddingFunctor X U).op S.C).homEquiv 𝓕.1 𝓖.1)⟩

/-- The functor from open neighbourhoods of a point `x ∈ U` in `U` to open neighbourhoods of `x`
in `X`, sending an open neighbourhood to its image under the open embedding. -/
def nhdsLift' (x : X) (hx : x ∈ U) :
    OpenNhds (X := TopCat.of (U : Type _)) ⟨x, hx⟩ ⥤ OpenNhds (X := X) x where
  obj W := ⟨(Opens.isOpenEmbedding U).functor.obj W.1,
    Set.mem_image_of_mem Subtype.val W.2⟩
  map f := homOfLE (Set.image_mono (leOfHom f))

/-- `nhdsLift' X U x hx` is initial: the open neighbourhoods of `x` contained in `U` are cofinal
among all open neighbourhoods of `x` in `X`. -/
instance nhdsLift'_initial (x : X) (hx : x ∈ U) : (nhdsLift' X U x hx).Initial := by
  rw [Functor.initial_iff_of_isCofiltered]
  exact ⟨fun V => ⟨⟨(Opens.map U.inclusion').obj V.1, V.2⟩, ⟨homOfLE (fun y hy => by
    obtain ⟨⟨z, hz⟩, hzV, rfl⟩ := hy
    exact hzV)⟩⟩,
   fun {d c} s s' => ⟨c, 𝟙 c, by simp [Subsingleton.elim s s']⟩⟩

/-- For a presheaf `P` on `X` and a point `x ∈ U`, the stalk of the restriction `j_p(P)` at
`⟨x, hx⟩` is isomorphic to the stalk of `P` at `x`. -/
noncomputable def stalk_restrict_iso (P : PShCategory S X) (x : X) (hx : x ∈ U) :
    stalk00A6 S (openTopCat X U) ((jpRestrict S X U).obj P) ⟨x, hx⟩ ≅ stalk00A6 S X P x := by
  haveI : (nhdsLift' X U x hx).op.Final := Functor.final_op_of_initial _
  exact Functor.Final.colimitIso (nhdsLift' X U x hx).op ((OpenNhds.inclusion x).op ⋙ P)

/-- For `x ∈ U`, the stalk `(j_!𝓕)_x` is isomorphic to the stalk `𝓕_x`. -/
@[stacks_fixed 00A6 "(3)", sga "4 III 1.9.2" "stalk at y∈Y ≅ H_y"]
theorem statement_3_stalk_in_U
    (𝓕 : ShOfAlgStruct S (openTopCat X U))
    (x : X) (hx : x ∈ U) :
    Nonempty (stalk00A6 S X (jShriek00A6 S X U 𝓕).1 x ≅
              stalk00A6 S (openTopCat X U) 𝓕.1 ⟨x, hx⟩) := by
  let xu : (openTopCat X U : TopCat) := ⟨x, hx⟩
  have iso1 : stalk00A6 S X ((jpShriek00A6 S X U).obj 𝓕.1) x ≅
      stalk00A6 S X ((sheafify00A6 S X).obj ((jpShriek00A6 S X U).obj 𝓕.1)) x :=
    sheafify_stalk_iso S X ((jpShriek00A6 S X U).obj 𝓕.1) x
  have iso2 : stalk00A6 S (openTopCat X U) ((jpRestrict S X U).obj ((jpShriek00A6 S X U).obj 𝓕.1))
      xu ≅
      stalk00A6 S X ((jpShriek00A6 S X U).obj 𝓕.1) x :=
    stalk_restrict_iso S X U ((jpShriek00A6 S X U).obj 𝓕.1) x hx
  have iso3 : stalk00A6 S (openTopCat X U) ((jpRestrict S X U).obj ((jpShriek00A6 S X U).obj 𝓕.1))
      xu ≅
      stalk00A6 S (openTopCat X U) 𝓕.1 xu :=
    (TopCat.Presheaf.stalkFunctor S.C xu).mapIso
      (asIso ((Functor.lanUnit (openEmbeddingFunctor X U).op).app 𝓕.1)).symm
  exact ⟨iso1.symm ≪≫ iso2.symm ≪≫ iso3⟩

/-- For `x ∉ U`, the stalk `(j_!𝓕)_x` is isomorphic to the initial object of `S.C`. -/
@[stacks_fixed 00A6 "(3)", sga "4 III 1.9.2" "special case"]
theorem statement_3_stalk_off_U
    (𝓕 : ShOfAlgStruct S (openTopCat X U))
    (x : X) (hx : x ∉ U) :
    Nonempty (stalk00A6 S X (jShriek00A6 S X U 𝓕).1 x ≅ (⊥_ S.C)) := by
  have hVals : ∀ j : (OpenNhds x)ᵒᵖ,
      IsInitial (((OpenNhds.inclusion x).op ⋙ (jpShriek00A6 S X U).obj 𝓕.1).obj j) := fun j =>
    jpShriek_obj_isInitial S X U 𝓕.1 ((OpenNhds.inclusion x).op.obj j).unop
      fun hle => hx (hle j.unop.2)
  have hInit : IsInitial (stalk00A6 S X ((jpShriek00A6 S X U).obj 𝓕.1) x) := by
    unfold stalk00A6
    show IsInitial (colimit ((OpenNhds.inclusion x).op ⋙ (jpShriek00A6 S X U).obj 𝓕.1))
    exact IsInitial.ofUniqueHom
      (fun A => colimit.desc _ ⟨A, ⟨fun j => (hVals j).to A,
        fun {j k} _ => (hVals j).hom_ext _ _⟩⟩)
      (fun A g => colimit.hom_ext fun j => (hVals j).hom_ext _ _)
  exact ⟨(hInit.ofIso (sheafify_stalk_iso S X ((jpShriek00A6 S X U).obj 𝓕.1) x)).uniqueUpToIso
    initialIsInitial⟩

omit [HasColimits S.C] in
/-- The composite `j_p ∘ j_{p!}` is naturally isomorphic to the identity functor on
`PShCategory(U, C)`. -/
@[stacks_fixed 00A6 "(4)"]
theorem statement_4_counit_presheaf :
    Nonempty ((jpShriek00A6 S X U ⋙ jpRestrict S X U) ≅
              (Functor.id (PShCategory S (openTopCat X U)))) :=
  ⟨(asIso (Functor.lanUnit (openEmbeddingFunctor X U).op (H := S.C))).symm⟩

/-- For every sheaf `𝓕` on `U`, the underlying presheaves of `j^{-1}(j_!𝓕)` and of `𝓕` are
isomorphic. -/
@[stacks_fixed 00A6 "(5)"]
theorem statement_5_counit_sheaf :
    ∀ (𝓕 : ShOfAlgStruct S (openTopCat X U)),
      Nonempty ((jInverseSheaf S X U (jShriek00A6 S X U 𝓕)).1 ≅ 𝓕.1) := by
  intro 𝓕
  set J := Opens.grothendieckTopology (X : TopCat.{v})
  let e := asIso ((Functor.lanUnit (openEmbeddingFunctor X U).op).app 𝓕.1)
  have hIso : IsIso ((jpRestrict S X U).map (J.toSheafify ((jpShriek00A6 S X U).obj 𝓕.1))) :=
    toSheafify_restrict_isIso S X U _ ((Presheaf.isSheaf_of_iso_iff e.symm).mpr
      (isSheaf_categorical S (openTopCat X U) 𝓕.1 𝓕.2))
  exact ⟨(asIso ((jpRestrict S X U).map (J.toSheafify _))).symm ≪≫ e.symm⟩
