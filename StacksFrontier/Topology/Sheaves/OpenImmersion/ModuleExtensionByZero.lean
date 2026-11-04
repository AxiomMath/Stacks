module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.OpenSubspace
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 00AB — extension by zero of modules along an open immersion

Let `(X, 𝒪)` be a ringed space, let `U ⊆ X` be open with inclusion `j : U → X`, and let `𝒪|_U` be
the restriction of `𝒪` to `U`. Stacks 00AB says that the extension-by-zero functor
`j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` is fully faithful and that a sheaf `G` of `𝒪`-modules lies in its
essential image exactly when the stalk `G_x` vanishes for every `x ∈ X ∖ U`. Both clauses are
`full_and_faithful_and_essImage_jShriek`.

## Shape of the formalization

`Mod(𝒪)` is Mathlib's `SheafOfModules 𝒪` for the Grothendieck topology of `Opens X`, and `𝒪|_U`
is the pushforward of `𝒪` along the functor `Opens U ⥤ Opens X` taking an open of `U` to its
image. Restriction of modules `j^*` is `SheafOfModules.pushforward` along that functor, and
`j_!` is its left adjoint `SheafOfModules.pullback`, which Mathlib provides.

* Full faithfulness is formal: `j_!`, `j^*` and the pushforward `j_*` form an adjoint triple, the
  counit of `j^* ⊣ j_*` is invertible because `j⁻¹ j (W) = W` for an open `W ⊆ U`, and in an
  adjoint triple that is equivalent to invertibility of the unit of `j_! ⊣ j^*`.
* The essential-image description is checked on stalks. The key input is that the presheaf-level
  extension by zero `j_{p!}` has no sections over an open `V ⊄ U`. This is proved by writing a
  presheaf of modules as a cokernel of a morphism between coproducts of free presheaves of
  modules on Yoneda presheaves (`PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork`),
  which `j_{p!}` preserves, and computing that `j_{p!}` sends the free presheaf on `yoneda W` for
  an open `W ⊆ U` to the free presheaf on `yoneda (j W)`, whose sections over `V ⊄ U` are the
  free module on the empty set of maps `V ⟶ j W`.

Sheafification does not change stalks, so the stalk of `j_! F` off `U` vanishes as well; and a
morphism of sheaves of modules that is invertible on all stalks is invertible, because forgetting
the module structure reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace ExtensionByZeroModules

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

variable {X : TopCat.{u}} (U : Opens X)

/-- The open subset `U`, viewed as a topological space via the subspace topology; the open
immersion `j : U → X` is `U.inclusion'`. This is `Stacks.Topology.openSubspace` under the name
this file uses. -/
abbrev Usp : TopCat.{u} := Stacks.Topology.openSubspace U

/-- The image functor on opens of an open embedding is continuous for the topologies of opens. -/
instance imF_isContinuous : (TopCat.Presheaf.imF U).IsContinuous
    (Opens.grothendieckTopology (Usp U)) (Opens.grothendieckTopology X) :=
  U.isOpenEmbedding.functor_isContinuous

variable (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The restriction `𝒪|_U` of the sheaf of rings `𝒪` to the open subspace `U`. -/
noncomputable abbrev resRing : Sheaf (Opens.grothendieckTopology (Usp U)) RingCat.{u} :=
  ((TopCat.Presheaf.imF U).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology (Usp U)) (Opens.grothendieckTopology X)).obj O

/-- Restriction of presheaves of modules along `j` has a left adjoint. -/
instance presheafPushforwardIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := TopCat.Presheaf.imF U) (R := O.obj)
      (S := (resRing U O).obj)
      (𝟙 (resRing U O) : resRing U O ⟶ resRing U O).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- Restriction of sheaves of modules along `j` has a left adjoint, namely `j_!`. -/
@[sga "4 IV 11.3.1" "special case"]
instance sheafPushforwardIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := TopCat.Presheaf.imF U) (R := O) (S := resRing U O)
      (𝟙 (resRing U O) : resRing U O ⟶ resRing U O)).IsRightAdjoint := by
  have := presheafPushforwardIsRightAdjoint U O
  exact SheafOfModules.instIsRightAdjointPushforward _

/-- **Restriction of modules to an open subspace**, `j^* : Mod(𝒪) ⥤ Mod(𝒪|_U)`. On sections it
is `(j^*M)(W) = M(j(W))`, with `𝒪|_U(W) = 𝒪(j(W))` acting. -/
noncomputable def jStar : SheafOfModules.{u} O ⥤ SheafOfModules.{u} (resRing U O) :=
  SheafOfModules.pushforward (𝟙 (resRing U O))

/-- **Extension by zero**, `j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)`, defined as the left adjoint of the
restriction functor `j^*`. -/
noncomputable def jShriek : SheafOfModules.{u} (resRing U O) ⥤ SheafOfModules.{u} O :=
  SheafOfModules.pullback (𝟙 (resRing U O))

/-- **`j_! ⊣ j^*`**: extension by zero is left adjoint to restriction. -/
noncomputable def jShriekAdjunction : jShriek U O ⊣ jStar U O :=
  SheafOfModules.pullbackPushforwardAdjunction (𝟙 (resRing U O))

/-- The morphism of sheaves of rings `𝒪 ⟶ j_*(𝒪|_U)` given by restricting a section over `V` to
`V ∩ U`. -/
noncomputable def toPushRing :
    O ⟶ ((Opens.map U.inclusion').sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Usp U))).obj (resRing U O) :=
  ⟨Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) O.obj⟩

/-- **Pushforward of modules along an open immersion**, `j_* : Mod(𝒪|_U) ⥤ Mod(𝒪)`. -/
noncomputable def jPush : SheafOfModules.{u} (resRing U O) ⥤ SheafOfModules.{u} O :=
  SheafOfModules.pushforward (toPushRing U O)

/-- First compatibility of `toPushRing` with the poset adjunction `imF ⊣ j⁻¹`. -/
lemma toPushRing_left :
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) O.obj =
      (toPushRing U O).hom ≫ (Opens.map U.inclusion').op.whiskerLeft
        (𝟙 (resRing U O) : resRing U O ⟶ resRing U O).hom :=
  rfl

/-- The triangle identity of the poset adjunction `imF ⊣ j⁻¹`, transported into `𝒪`: over an
open `W` of `U`, restricting from `j(W)` to `j(j⁻¹(j(W)))` and back is the identity. -/
lemma map_counit_comp_map_unit (W : (Opens (Usp U))ᵒᵖ) :
    O.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
          ((TopCat.Presheaf.imF U).obj W.unop)).op ≫
        O.obj.map ((TopCat.Presheaf.imF U).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop)).op =
      𝟙 (O.obj.obj (op ((TopCat.Presheaf.imF U).obj W.unop))) := by
  rw [← Functor.map_comp, ← op_comp,
    show ((TopCat.Presheaf.imF U).map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop) ≫
          U.isOpenEmbedding.isOpenMap.adjunction.counit.app
            ((TopCat.Presheaf.imF U).obj W.unop)) = 𝟙 _ from
      Subsingleton.elim _ _, op_id]
  simp

/-- Second compatibility of `toPushRing` with the poset adjunction `imF ⊣ j⁻¹`. -/
lemma toPushRing_right :
    (𝟙 (resRing U O) : resRing U O ⟶ resRing U O).hom ≫
        (TopCat.Presheaf.imF U).op.whiskerLeft (toPushRing U O).hom ≫
        Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit)
          (resRing U O).obj = 𝟙 (resRing U O).obj := by
  ext W : 2
  exact map_counit_comp_map_unit U O W

/-- **`j^* ⊣ j_*`**: restriction to an open subspace is left adjoint to pushforward. -/
noncomputable def jStarAdjunction : jStar U O ⊣ jPush U O :=
  SheafOfModules.pushforwardPushforwardAdj U.isOpenEmbedding.isOpenMap.adjunction _ _
    (toPushRing_left U O) (toPushRing_right U O)

/-- The composite `Opens U ⥤ Opens X ⥤ Opens U` of the image functor and the preimage functor is
continuous. -/
instance imF_comp_isContinuous : (TopCat.Presheaf.imF U ⋙ Opens.map U.inclusion').IsContinuous
    (Opens.grothendieckTopology (Usp U)) (Opens.grothendieckTopology (Usp U)) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _

/-- The unit of the poset adjunction `imF ⊣ j⁻¹` is invertible: `j⁻¹(j(W)) = W` for an open `W` of
`U`, and any two parallel morphisms of opens agree. -/
instance isIso_adjunction_unit : IsIso U.isOpenEmbedding.isOpenMap.adjunction.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  exact ⟨homOfLE (le_of_eq (Opens.map_functor_eq W)), Subsingleton.elim _ _,
    Subsingleton.elim _ _⟩

/-- **`j^* j_* = id`.** Restricting the pushforward of a sheaf of `𝒪|_U`-modules back to `U`
recovers it, because `j⁻¹(j(W)) = W` for an open `W ⊆ U`. -/
noncomputable def jStarPushIso :
    jPush U O ⋙ jStar U O ≅ 𝟭 (SheafOfModules.{u} (resRing U O)) :=
  SheafOfModules.pushforwardComp (𝟙 (resRing U O)) (toPushRing U O) ≪≫
    SheafOfModules.pushforwardNatIso _ (asIso U.isOpenEmbedding.isOpenMap.adjunction.unit) ≪≫
    SheafOfModules.pushforwardCongr (by ext W : 3; exact map_counit_comp_map_unit U O W) ≪≫
    SheafOfModules.pushforwardId _

/-- The counit of `j^* ⊣ j_*` is invertible. -/
instance isIso_jStarAdjunction_counit : IsIso (jStarAdjunction U O).counit :=
  (jStarAdjunction U O).isIso_counit_of_iso (jStarPushIso U O)

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` of an open immersion, for sheaves of modules. -/
noncomputable def openImmersionTriple :
    Adjunction.Triple (jShriek U O) (jStar U O) (jPush U O) :=
  ⟨jShriekAdjunction U O, jStarAdjunction U O⟩

/-- The unit of `j_! ⊣ j^*` is invertible: `j^* j_! = id`. -/
theorem isIso_jShriekAdjunction_unit : IsIso (jShriekAdjunction U O).unit := by
  rw [show jShriekAdjunction U O = (openImmersionTriple U O).adj₁ from rfl,
    (openImmersionTriple U O).isIso_unit_iff_isIso_counit]
  exact isIso_jStarAdjunction_counit U O

/-- `j_!` is fully faithful. -/
noncomputable def jShriekFullyFaithful : (jShriek U O).FullyFaithful :=
  haveI := isIso_jShriekAdjunction_unit U O
  (jShriekAdjunction U O).fullyFaithfulLOfIsIsoUnit

/-! ### The presheaf-level extension by zero vanishes away from `U` -/

/-- The restriction functor `j_p : PSh-Mod(𝒪) ⥤ PSh-Mod(𝒪|_U)` on presheaves of modules. -/
noncomputable abbrev jpStar :
    PresheafOfModules.{u} O.obj ⥤ PresheafOfModules.{u} (resRing U O).obj :=
  PresheafOfModules.pushforward (𝟙 (resRing U O) : resRing U O ⟶ resRing U O).hom

/-- The presheaf-level extension by zero `j_{p!}`, the left adjoint of `j_p`. -/
noncomputable abbrev jpShriek :
    PresheafOfModules.{u} (resRing U O).obj ⥤ PresheafOfModules.{u} O.obj :=
  PresheafOfModules.pullback (𝟙 (resRing U O) : resRing U O ⟶ resRing U O).hom

/-- Evaluation of `j_{p!}M` is corepresented by `j_{p!}M`, by the adjunction `j_{p!} ⊣ j_p`. -/
noncomputable def jpShriekCorepresentableBy (M : PresheafOfModules.{u} (resRing U O).obj) :
    (jpStar U O ⋙ coyoneda.obj (op M)).CorepresentableBy ((jpShriek U O).obj M) where
  homEquiv {N} := (PresheafOfModules.pullbackPushforwardAdjunction _).homEquiv M N
  homEquiv_comp _ _ :=
    (PresheafOfModules.pullbackPushforwardAdjunction _).homEquiv_naturality_right _ _

/-- `j_{p!}` takes the free presheaf of modules on a Yoneda presheaf of an open `W ⊆ U` to the
free presheaf of modules on the Yoneda presheaf of the image `j(W)`. -/
noncomputable def jpShriekFreeYonedaIso (W : Opens (Usp U)) :
    (jpShriek U O).obj ((PresheafOfModules.free (resRing U O).obj).obj (yoneda.obj W)) ≅
      (PresheafOfModules.free O.obj).obj (yoneda.obj ((TopCat.Presheaf.imF U).obj W)) :=
  (jpShriekCorepresentableBy U O _).uniqueUpToIso
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy _ W)

/-- The image in `X` of an open subset of `U` is contained in `U`. -/
lemma imF_le (W : Opens (Usp U)) : (TopCat.Presheaf.imF U).obj W ≤ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

/-- An open of `X` not contained in `U` is not contained in the image of any open of `U`. -/
lemma not_le_imF {V : Opens X} (hV : ¬ V ≤ U) (W : Opens (Usp U)) :
    ¬ V ≤ (TopCat.Presheaf.imF U).obj W :=
  fun h => hV (h.trans (imF_le U W))

/-- The free presheaf of modules on a Yoneda presheaf `yoneda V'` has no nonzero sections over an
open `V ⊄ V'`, since there `yoneda V'` is empty. -/
lemma isZero_free_yoneda_obj {V V' : Opens X} (h : ¬ V ≤ V') :
    IsZero (((PresheafOfModules.free O.obj).obj (yoneda.obj V')).obj (op V)) := by
  have : Subsingleton (((PresheafOfModules.free O.obj).obj (yoneda.obj V')).obj (op V)) :=
    ⟨fun _ _ => Finsupp.ext fun f => (h (leOfHom f)).elim⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- `j_{p!}` of the free presheaf of modules on `yoneda W`, `W ⊆ U`, has no sections outside
`U`: its sections over `V` are the free module on the maps `V ⟶ j(W)`, and there are none when
`V ⊄ U`. -/
lemma isZero_jpShriek_freeYoneda_obj (W : Opens (Usp U)) {V : Opens X} (hV : ¬ V ≤ U) :
    IsZero (((jpShriek U O).obj
      ((PresheafOfModules.free (resRing U O).obj).obj (yoneda.obj W))).obj (op V)) :=
  (isZero_free_yoneda_obj O (not_le_imF U hV W)).of_iso
    ((PresheafOfModules.evaluation O.obj (op V)).mapIso (jpShriekFreeYonedaIso U O W))

/-- `j_{p!}` is a left adjoint, hence preserves colimits indexed by categories in universe `u`. -/
instance jpShriek_preservesColimitsOfSize :
    Limits.PreservesColimitsOfSize.{u, u} (jpShriek U O) :=
  (PresheafOfModules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits

/-- `j_{p!}` preserves colimits indexed by small categories such as `WalkingParallelPair`. -/
instance jpShriek_preservesColimitsOfSizeZero :
    Limits.PreservesColimitsOfSize.{0, 0} (jpShriek U O) :=
  (PresheafOfModules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits

/-- If `j_{p!}` has no sections over `V` on the diagram of a colimit, it has none on the vertex. -/
private lemma isZero_jpShriek_pt_of_isColimit {J : Type*} [Category J] {F : J ⥤ _}
    {c : Cocone F} {V : Opens X}
    [PreservesColimit F (jpShriek U O ⋙ PresheafOfModules.evaluation O.obj (op V))]
    (hc : IsColimit c)
    (h : ∀ j, IsZero (((jpShriek U O).obj (F.obj j)).obj (op V))) :
    IsZero (((jpShriek U O).obj c.pt).obj (op V)) :=
  IsColimit.isZero_pt (isColimitOfPreserves (jpShriek U O ⋙ PresheafOfModules.evaluation O.obj
    (op V)) hc) (Functor.isZero _ h)

/-- `j_{p!}` of a coproduct of free Yoneda presheaves has no sections outside `U`. -/
lemma isZero_jpShriek_freeYonedaCoproduct (N : PresheafOfModules.{u} (resRing U O).obj)
    {V : Opens X} (hV : ¬ V ≤ U) :
    IsZero (((jpShriek U O).obj N.freeYonedaCoproduct).obj (op V)) :=
  isZero_jpShriek_pt_of_isColimit U O (colimit.isColimit _) fun m =>
    isZero_jpShriek_freeYoneda_obj U O m.as.1.unop hV

/-- **`j_{p!}M` has no sections over an open not contained in `U`.** Every presheaf of modules is
a cokernel of a morphism between coproducts of free Yoneda presheaves, and `j_{p!}` preserves
that colimit, so the vanishing propagates from the free Yoneda case. -/
lemma isZero_jpShriek_obj (M : PresheafOfModules.{u} (resRing U O).obj)
    {V : Opens X} (hV : ¬ V ≤ U) : IsZero (((jpShriek U O).obj M).obj (op V)) :=
  isZero_jpShriek_pt_of_isColimit U O M.isColimitFreeYonedaCoproductsCokernelCofork fun j => by
    cases j <;> exact isZero_jpShriek_freeYonedaCoproduct U O _ hV

/-- The abelian presheaf underlying `j_{p!}M` vanishes on opens not contained in `U`. -/
lemma isZero_jpShriek_presheaf_obj (M : PresheafOfModules.{u} (resRing U O).obj)
    {V : Opens X} (hV : ¬ V ≤ U) : IsZero (((jpShriek U O).obj M).presheaf.obj (op V)) :=
  @AddCommGrpCat.isZero_of_subsingleton _
    (ModuleCat.isZero_iff_subsingleton.1 (isZero_jpShriek_obj U O M hV))

/-- **The stalk of `j_{p!}M` at a point outside `U` is zero.** No open neighbourhood of such a
point is contained in `U`, so the filtered colimit computing the stalk is a colimit of zeros. -/
lemma isZero_stalk_jpShriek (M : PresheafOfModules.{u} (resRing U O).obj) (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((jpShriek U O).obj M).presheaf x) := by
  refine Limits.IsColimit.isZero_pt (Limits.colimit.isColimit _) (Functor.isZero _ fun V => ?_)
  exact isZero_jpShriek_presheaf_obj U O M fun hle => hx (hle V.unop.2)

/-- The abelian sheaf underlying `j_! F` is the sheafification of the abelian presheaf
underlying `j_{p!}F`. -/
noncomputable def jShriekPresheafIso (F : SheafOfModules.{u} (resRing U O)) :
    ((jShriek U O).obj F).val.presheaf ≅
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          ((jpShriek U O).obj F.val).presheaf) :=
  (SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj).mapIso
      ((SheafOfModules.pullbackIso (𝟙 (resRing U O))).app F) ≪≫
    (PresheafOfModules.sheafificationCompForgetCompToPresheaf (𝟙 O.obj)).app _

/-- **Stacks 00AB, stalks off `U`.** The stalk of `j_! F` at a point outside `U` is zero:
sheafification does not change stalks, and the stalk of `j_{p!}F` there is zero. -/
theorem isZero_stalk_jShriek (F : SheafOfModules.{u} (resRing U O)) (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((jShriek U O).obj F).val.presheaf x) := by
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) ((jpShriek U O).obj F.val).presheaf)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  exact ((isZero_stalk_jpShriek U O F.val x hx).of_iso
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((jpShriek U O).obj F.val).presheaf))).symm).of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso (jShriekPresheafIso U O F))

/-! ### Recognising isomorphisms of sheaves of modules stalkwise -/

section StalkwiseIso

/-- The abelian presheaf underlying a sheaf of `𝒪`-modules. -/
noncomputable abbrev toAb : SheafOfModules.{u} O ⥤ TopCat.Presheaf AddCommGrpCat.{u} X :=
  SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj

/-- A morphism of sheaves of `𝒪`-modules which is an isomorphism on every stalk is an
isomorphism: the underlying morphism of abelian sheaves is one, and forgetting the module
structure reflects isomorphisms. -/
lemma isIso_of_stalk_isIso {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toAb O).map f))) : IsIso f := by
  have h' : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf O).map f).hom) := h
  have : IsIso ((SheafOfModules.toSheaf O).map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ((SheafOfModules.toSheaf O).map f)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf O)

end StalkwiseIso

/-! ### The counit is an isomorphism when the stalks vanish off `U` -/

/-- On underlying abelian presheaves, `j^*` is precomposition with the image functor on opens. -/
lemma toAb_jStar_map {M N : SheafOfModules.{u} O} (f : M ⟶ N) :
    (toAb (resRing U O)).map ((jStar U O).map f) =
      Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map f) :=
  rfl

/-- **If `G_x = 0` for every `x ∉ U`, the counit `j_!(j^*G) ⟶ G` is an isomorphism.** It suffices
to check this on stalks. At a point of `U` it follows from the right triangle identity together
with invertibility of the unit, transported through the identification of the stalks of a
restriction. At a point outside `U` both stalks vanish. -/
theorem counit_isIso_of_stalk_isZero (G : SheafOfModules.{u} O)
    (hG : ∀ x : X, x ∉ U → IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x)) :
    IsIso ((jShriekAdjunction U O).counit.app G) := by
  have := isIso_jShriekAdjunction_unit U O
  set φ := (jShriekAdjunction U O).counit.app G
  refine isIso_of_stalk_isIso O φ fun x => ?_
  by_cases hx : x ∈ U
  · have hR : IsIso ((jStar U O).map φ) :=
      isIso_of_hom_comp_eq_id _ ((jShriekAdjunction U O).right_triangle_components G)
    have : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ)) := by
      rw [← toAb_jStar_map U O φ]
      exact Functor.map_isIso _ _
    simpa using (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
      ((toAb O).map φ) ⟨x, hx⟩).mp inferInstance
  · exact (isZero_stalk_jShriek U O ((jStar U O).obj G) x hx).isIso (hG x hx) _

/-- **Stacks 00AB, the essential image.** A sheaf `G` of `𝒪`-modules lies in the essential image
of `j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` if and only if `G_x = 0` for every `x ∈ X ∖ U`.

For "only if", an isomorphism `j_! F ≅ G` induces isomorphisms of stalks and the stalk of `j_! F`
vanishes off `U`. For "if", the vanishing makes the counit `j_!(j^*G) ⟶ G` invertible. -/
theorem jShriek_essImage (G : SheafOfModules.{u} O) :
    (jShriek U O).essImage G ↔
      ∀ x : X, x ∉ U → IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x) := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩ x hx
    exact (isZero_stalk_jShriek U O F x hx).of_iso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso ((toAb O).mapIso e)).symm
  · intro hG
    have := counit_isIso_of_stalk_isZero U O G hG
    exact ⟨(jStar U O).obj G, ⟨asIso ((jShriekAdjunction U O).counit.app G)⟩⟩

/-- **Stacks 00AB.** Let `(X, 𝒪)` be a ringed space and let `j : (U, 𝒪|_U) → (X, 𝒪)` be an open
subspace. The extension-by-zero functor `j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` is fully faithful, and its
essential image consists exactly of those sheaves `G` of `𝒪`-modules with `G_x = 0` for all
`x ∈ X ∖ U`.

The stalk `G_x` is a module over the stalk `𝒪_x` whose underlying abelian group is the stalk of
the underlying abelian sheaf of `G` (Mathlib's `PresheafOfModules.instModuleStalk`), and a module
is zero exactly when its underlying group is; so `G_x = 0` is expressed here as vanishing of that
abelian group. The sheaf of rings is allowed to be non-commutative, which is more general than
the ringed spaces of the source. -/
@[stacks 00AB, sga "4 IV 11.3.1" "special case"]
theorem full_and_faithful_and_essImage_jShriek :
    (jShriek U O).Full ∧ (jShriek U O).Faithful ∧
      ∀ G : SheafOfModules.{u} O, (jShriek U O).essImage G ↔
        ∀ x : X, x ∉ U → IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf x) :=
  ⟨(jShriekFullyFaithful U O).full, (jShriekFullyFaithful U O).faithful, jShriek_essImage U O⟩

end ExtensionByZeroModules
