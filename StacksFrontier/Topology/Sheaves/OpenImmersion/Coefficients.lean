module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Geometry.RingedSpace.Stalks
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 00A0 for (pre)sheaves with values in an arbitrary category

Let `j : U ⟶ X` be an open embedding of topological spaces (the inclusion of an open subset in
Stacks 00A0) and let `A` be any category. This file proves the five clauses of Stacks 00A0 for
`A`-valued (pre)sheaves. In particular they hold for (pre)sheaves of abelian groups and of
algebraic structures in the sense of Stacks 007M, for which nothing beyond the category `A`
itself is needed. The case of (pre)sheaves of modules over a sheaf of rings is
`StacksFrontier/Topology/Sheaves/OpenImmersion/ModuleRestriction.lean`, and the case of sets is
`StacksFrontier/Topology/Sheaves/OpenImmersion/Basic.lean`.

Stacks defines `j_p` as the left adjoint of `j_*` on presheaves and `j⁻¹` as the left adjoint of
`j_*` on sheaves (Stacks 008C). The clauses are therefore formalized as follows, for every `A`:

* (1) `restrictPresheafAdjunction`: the restriction `V ↦ G(j V)` is left adjoint to
  `j_* = TopCat.Presheaf.pushforward A j`; so it *is* `j_p`. When `A` has colimits, so that
  Mathlib's colimit-built `TopCat.Presheaf.pullback A j` exists, `presheafPullbackIsoRestrict`
  identifies the two (this is Mathlib's `IsOpenMap.pullbackIso`).
* (2) `restrictSheafAdjunction`: for sheaves, the restriction `hj.sheafPullback A` (which is a
  sheaf with no sheafification) is left adjoint to `j_* = TopCat.Sheaf.pushforward A j`; so it
  *is* `j⁻¹`. Under the hypotheses for which Mathlib constructs `TopCat.Sheaf.pullback A j`
  (the sheafification of `j_p`), `sheafPullbackIsoRestrict` identifies the two (this is
  Mathlib's `Topology.IsOpenEmbedding.sheafPullbackIso`).
* (3) `restrictStalkIso`: for any presheaf `G` on `X` and `u ∈ U`, the colimit of the
  restriction over the neighbourhoods of `u` is the colimit of `G` over the neighbourhoods of
  `j u`, as soon as the latter exists (no colimits are assumed in `A`: stalks of algebraic
  structures are filtered colimits). `sheafPullbackStalkIso` is the same statement for Mathlib's
  sheaf pullback.
* (4) `isIso_restrictPresheafAdjunction_counit`: the counit `j_p j_* ⟶ 𝟭` is an isomorphism, and
  `isIso_presheafPullbackPushforwardAdjunction_counit` states it for Mathlib's adjunction.
* (5) `isIso_restrictSheafAdjunction_counit`: the counit `j⁻¹ j_* ⟶ 𝟭` is an isomorphism, and
  `isIso_sheafPullbackPushforwardAdjunction_counit` states it for Mathlib's adjunction.

All of (4) and (5) come from the adjunction `hj.functor ⊣ Opens.map j` of posets of opens
(`IsOpenMap.adjunction`), whose unit `V ⟶ j⁻¹(j V)` is an isomorphism because `j` is injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe w v u

namespace OpenImmersionSheaves

variable (A : Type*) [Category A] {X U : TopCat.{u}} (j : U ⟶ X)
  (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j))

/-- The unit `V ⟶ j⁻¹(j V)` of the adjunction `hj.functor ⊣ Opens.map j` is an isomorphism:
`j⁻¹(j V) = V` since `j` is injective. -/
theorem isIso_isOpenMap_adjunction_unit : IsIso hj.isOpenMap.adjunction.unit := by
  have happ : ∀ V : Opens U, IsIso (hj.isOpenMap.adjunction.unit.app V) := by
    intro V
    have hle : ((Opens.map j).obj (hj.functor.obj V)) ≤ V := by
      intro x hx
      have hx' : (ConcreteCategory.hom j) x ∈ (ConcreteCategory.hom j) '' (V : Set U) := hx
      rw [hj.injective.mem_set_image] at hx'
      exact hx'
    exact ⟨⟨homOfLE hle, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

/-- Restriction of `A`-valued presheaves along the open embedding `j`: `G ↦ (V ↦ G(j V))`. -/
noncomputable abbrev restrictPresheafFunctor : X.Presheaf A ⥤ U.Presheaf A :=
  (Functor.whiskeringLeft _ _ A).obj hj.functor.op

/-- **Stacks 00A0 (1), for presheaves with values in any category `A`.** The restriction
`G ↦ (V ↦ G(V))` of presheaves along the open embedding `j : U ⟶ X` is left adjoint to the
pushforward `j_* = TopCat.Presheaf.pushforward A j`. Since Stacks defines `j_p` as the left
adjoint of `j_*` (Stacks 008C), this says that `j_p G` is given by `V ↦ G(V)` for `V ⊆ U` open.
No hypothesis on `A` is needed. The adjunction is the whiskering of the opposite of the
adjunction `hj.functor ⊣ Opens.map j` of posets of opens. -/
@[stacks 00A0 "(1) for presheaves with values in any category: restriction is left adjoint to
  `j_*`, i.e. is `j_p`; see `presheafPullbackIsoRestrict` for Mathlib's colimit-built `j_p`"]
noncomputable def restrictPresheafAdjunction :
    restrictPresheafFunctor A j hj ⊣ Presheaf.pushforward A j :=
  Adjunction.whiskerLeft A hj.isOpenMap.adjunction.op

/-- **Stacks 00A0 (1), Mathlib's `j_p`.** When `A` has colimits, Mathlib's presheaf pullback
`TopCat.Presheaf.pullback A j` (the left Kan extension, computed by colimits) is isomorphic to
the restriction. This is Mathlib's `IsOpenMap.pullbackIso`. -/
@[stacks 00A0 "(1) for Mathlib's colimit-built `j_p` (Mathlib `IsOpenMap.pullbackIso`)"]
noncomputable def presheafPullbackIsoRestrict [HasColimits A] :
    Presheaf.pullback A j ≅ restrictPresheafFunctor A j hj :=
  hj.isOpenMap.pullbackIso

/-- **Stacks 00A0 (4), for presheaves with values in any category `A`.** The counit
`j_p j_* ⟶ 𝟭` of `restrictPresheafAdjunction` is an isomorphism: its component at `F` and `V`
is `F` applied to the isomorphism `V ≅ j⁻¹(j V)`. -/
@[stacks 00A0 "(4) for presheaves with values in any category"]
theorem isIso_restrictPresheafAdjunction_counit :
    IsIso (restrictPresheafAdjunction A j hj).counit := by
  have : IsIso hj.isOpenMap.adjunction.op.counit := by
    have := isIso_isOpenMap_adjunction_unit j hj
    change IsIso (NatTrans.op hj.isOpenMap.adjunction.unit)
    infer_instance
  have happ : ∀ F, IsIso ((restrictPresheafAdjunction A j hj).counit.app F) := by
    intro F
    have happ' : ∀ z, IsIso (((restrictPresheafAdjunction A j hj).counit.app F).app z) := by
      intro z
      rw [restrictPresheafAdjunction, Adjunction.whiskerLeft_counit_app_app]
      exact Functor.map_isIso F (hj.isOpenMap.adjunction.op.counit.app z)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

include hj in
/-- The pushforward of `A`-valued presheaves along an open embedding is fully faithful. -/
noncomputable def presheafPushforwardFullyFaithfulOf :
    (Presheaf.pushforward A j).FullyFaithful :=
  haveI := isIso_restrictPresheafAdjunction_counit A j hj
  (restrictPresheafAdjunction A j hj).fullyFaithfulROfIsIsoCounit

include hj in
/-- **Stacks 00A0 (4), Mathlib's adjunction.** When `A` has colimits, the counit of Mathlib's
adjunction `TopCat.Presheaf.pullback A j ⊣ TopCat.Presheaf.pushforward A j` is an isomorphism. -/
@[stacks 00A0 "(4) for Mathlib's `j_p ⊣ j_*`"]
theorem isIso_presheafPullbackPushforwardAdjunction_counit [HasColimits A] :
    IsIso (Presheaf.pullbackPushforwardAdjunction A j).counit := by
  have ff := presheafPushforwardFullyFaithfulOf A j hj
  have := ff.full
  have := ff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-- **Stacks 00A0 (2), for sheaves with values in any category `A`.** The restriction
`hj.sheafPullback A : Sh(X, A) ⥤ Sh(U, A)`, `G ↦ (V ↦ G(V))` — a sheaf as it stands, with no
sheafification — is left adjoint to the pushforward `j_* = TopCat.Sheaf.pushforward A j`.
Since Stacks defines `j⁻¹` on sheaves as the left adjoint of `j_*` (Stacks 008C), this says
that `j⁻¹ G` is given by `V ↦ G(V)` for `V ⊆ U` open. No hypothesis on `A` is needed. -/
@[stacks 00A0 "(2) for sheaves with values in any category: restriction is left adjoint to
  `j_*`, i.e. is `j⁻¹`; see `sheafPullbackIsoRestrict` for Mathlib's sheafified `j⁻¹`"]
noncomputable def restrictSheafAdjunction :
    hj.sheafPullback A ⊣ Sheaf.pushforward A j :=
  haveI := hj.functor_isContinuous
  hj.isOpenMap.adjunction.sheafPushforwardContinuous (E := A) _ _

/-- **Stacks 00A0 (5), for sheaves with values in any category `A`.** The counit
`j⁻¹ j_* ⟶ 𝟭` of `restrictSheafAdjunction` is an isomorphism. -/
@[stacks 00A0 "(5) for sheaves with values in any category"]
theorem isIso_restrictSheafAdjunction_counit :
    IsIso (restrictSheafAdjunction A j hj).counit := by
  have h := isIso_restrictPresheafAdjunction_counit A j hj
  have happ : ∀ F, IsIso ((restrictSheafAdjunction A j hj).counit.app F) := by
    intro F
    have : IsIso ((sheafToPresheaf _ A).map ((restrictSheafAdjunction A j hj).counit.app F)) :=
      inferInstanceAs (IsIso ((restrictPresheafAdjunction A j hj).counit.app F.obj))
    exact isIso_of_fully_faithful (sheafToPresheaf _ A) _
  exact NatIso.isIso_of_isIso_app _

include hj in
/-- The pushforward of `A`-valued sheaves along an open embedding is fully faithful. -/
noncomputable def sheafPushforwardFullyFaithfulOf :
    (Sheaf.pushforward A j).FullyFaithful :=
  haveI := isIso_restrictSheafAdjunction_counit A j hj
  (restrictSheafAdjunction A j hj).fullyFaithfulROfIsIsoCounit

/-- If the stalk of `G` at `j u` exists, so does the stalk at `u` of the restriction of `G`:
the functor `V ↦ j V` on open neighbourhoods is initial, being a left adjoint. -/
theorem hasColimit_restrict_nhds (G : X.Presheaf A) (u : U)
    [HasColimit ((OpenNhds.inclusion (j u)).op ⋙ G)] :
    HasColimit ((OpenNhds.inclusion u).op ⋙ (restrictPresheafFunctor A j hj).obj G) := by
  have := Functor.initial_of_adjunction (hj.adjunctionNhds u)
  exact (inferInstance : HasColimit ((hj.functorNhds u).op ⋙ (OpenNhds.inclusion (j u)).op ⋙ G))

/-- **Stacks 00A0 (3), for presheaves with values in any category `A`.** For a presheaf `G` on
`X` and `u ∈ U`, if the stalk `G_{j u}` (the colimit of `G` over the open neighbourhoods of
`j u`) exists, then so does the stalk at `u` of the restriction `V ↦ G(V)`
(`hasColimit_restrict_nhds`) and the two are canonically isomorphic: the neighbourhoods of
`j u` of the form `j V` are cofinal. No colimits are assumed in `A`. This is the argument of
Mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso`, which needs `HasColimits A`. -/
@[stacks 00A0 "(3) for presheaves with values in any category, stalk of the restriction"]
noncomputable def restrictStalkIso (G : X.Presheaf A) (u : U)
    [HasColimit ((OpenNhds.inclusion (j u)).op ⋙ G)] :
    haveI := hasColimit_restrict_nhds A j hj G u
    colimit ((OpenNhds.inclusion u).op ⋙ (restrictPresheafFunctor A j hj).obj G) ≅
      colimit ((OpenNhds.inclusion (j u)).op ⋙ G) :=
  haveI := Functor.initial_of_adjunction (hj.adjunctionNhds u)
  Functor.Final.colimitIso (hj.functorNhds u).op ((OpenNhds.inclusion (j u)).op ⋙ G)

section Mathlib

variable {FA : A → A → Type*} {CA : A → Type u}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- **Stacks 00A0 (2), Mathlib's `j⁻¹`.** Under the hypotheses for which Mathlib constructs the
sheaf pullback `TopCat.Sheaf.pullback A j` (the sheafification of the presheaf pullback), it is
isomorphic to the restriction `hj.sheafPullback A`. This is Mathlib's
`Topology.IsOpenEmbedding.sheafPullbackIso`. -/
@[stacks 00A0 "(2) for Mathlib's sheafified `j⁻¹` (Mathlib
  `Topology.IsOpenEmbedding.sheafPullbackIso`)"]
noncomputable def sheafPullbackIsoRestrict :
    Sheaf.pullback A j ≅ hj.sheafPullback A :=
  hj.sheafPullbackIso A

include hj in
/-- **Stacks 00A0 (5), Mathlib's adjunction.** The counit of Mathlib's adjunction
`TopCat.Sheaf.pullback A j ⊣ TopCat.Sheaf.pushforward A j` is an isomorphism. -/
@[stacks 00A0 "(5) for Mathlib's `j⁻¹ ⊣ j_*`"]
theorem isIso_sheafPullbackPushforwardAdjunction_counit :
    IsIso (Sheaf.pullbackPushforwardAdjunction A j).counit := by
  have ff := sheafPushforwardFullyFaithfulOf A j hj
  have := ff.full
  have := ff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-- **Stacks 00A0 (3), Mathlib's `j⁻¹`.** For a sheaf `G` on `X` and `u ∈ U`, the stalk of
Mathlib's sheaf pullback `j⁻¹ G` at `u` is the stalk of `G` at `j u`:
`(j⁻¹ G)_u ≅ (G|_U)_u ≅ G_{j u}`, through clause (2) and `restrictStalkIso`. -/
@[stacks 00A0 "(3) for Mathlib's sheafified `j⁻¹`"]
noncomputable def sheafPullbackStalkIso (G : X.Sheaf A) (u : U) :
    Presheaf.stalk ((Sheaf.pullback A j).obj G).obj u ≅
      Presheaf.stalk G.obj ((ConcreteCategory.hom j) u) :=
  (Presheaf.stalkFunctor A u).mapIso
      ((sheafToPresheaf _ _).mapIso ((sheafPullbackIsoRestrict A j hj).app G)) ≪≫
    restrictStalkIso A j hj G.obj u

end Mathlib

end OpenImmersionSheaves
