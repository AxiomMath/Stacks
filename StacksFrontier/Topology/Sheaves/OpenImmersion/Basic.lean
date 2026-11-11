module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 00A0 — open immersions and (pre)sheaves

Let `X` be a topological space and `j : U → X` the inclusion of an open subset. Stacks 00A0
describes the restriction `G|_U` of a (pre)sheaf on `X` to `U` and its interaction with the
pushforward `j_*`. The inclusion is encoded here as a morphism `j : U ⟶ X` of `TopCat` whose
underlying map is an open embedding, the standard idiom for an open immersion; specializing `j`
to the inclusion of an open subset recovers the statement of the tag.

All five clauses are formalized for (pre)sheaves of sets:

* (1) `presheaf_pullback_iso_restriction`: the presheaf pullback `j_p G`, the colimit-based
  left adjoint of `j_*`, is canonically isomorphic to the naive restriction `V ↦ G(j V)`;
* (2) `sheaf_pullback_iso_restriction`: for a sheaf `G` the naive restriction is again a sheaf
  (`restrictSheaf`), and the sheaf pullback `j⁻¹ G` is canonically isomorphic to it, so no
  sheafification is needed;
* (3) `stalk_sheaf_pullback_iso`: the stalk of `j⁻¹ G` at `u ∈ U` is the stalk of `G` at
  `j u`; `stalkPullbackHom_isIso` pins this down to the canonical comparison map already at
  the presheaf level;
* (4) `presheaf_pullback_pushforward_counit_isIso`: the counit of `j_p ⊣ j_*` is a natural
  isomorphism, i.e. `j_p ∘ j_* ≅ id` on presheaves;
* (5) `sheaf_pullback_pushforward_counit_isIso`: likewise the counit of `j⁻¹ ⊣ j_*` is a
  natural isomorphism on sheaves.

Clauses (1)–(3) are Mathlib's canonical comparison maps (`IsOpenMap.pullbackObjIso`,
`Topology.IsOpenEmbedding.sheafPullbackIso`, `Presheaf.stalkPullbackIso`); clauses (4) and (5)
are deduced from full faithfulness of the pushforward along an open embedding, proved here as
`presheafPushforwardFullyFaithful` and `sheafPushforwardFullyFaithful`. The open-embedding
hypothesis is genuinely needed for (4) and (5): for an arbitrary continuous `j` the counit
need not be an isomorphism. Every isomorphism is produced as honest data — an `≅`, or `IsIso`
of a named canonical morphism — never merely as `Nonempty`.

The tag asserts the same descriptions for (pre)sheaves of abelian groups, of algebraic
structures and of modules. Those cases are proved in
`StacksFrontier/Topology/Sheaves/OpenImmersion/Coefficients.lean`, for (pre)sheaves with values in
an arbitrary category (which covers abelian groups and every type of algebraic structure), and
in `StacksFrontier/Topology/Sheaves/OpenImmersion/ModuleRestriction.lean`, for (pre)sheaves of
modules over a (pre)sheaf of rings.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open TopCat

universe u

namespace OpenImmersionSheaves

variable {X U : TopCat.{u}} (j : U ⟶ X)
    (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j))

/-- The naive restriction `G|_U` of a presheaf `G` on `X` to the opens of `U`:
`V ↦ G(j V)` for `V ⊆ U` open, realized via precomposition with `hj.functor.op`
(valid because `j` is an open embedding). -/
@[ega "0 3.1.5"]
noncomputable def restrictPresheaf (G : X.Presheaf (Type u)) : U.Presheaf (Type u) :=
  hj.functor.op ⋙ G

/-- For a sheaf `G` on `X`, the naive restriction `V ↦ G(j V)` is again a sheaf
on `U`, because open covers of an open `V ⊆ U` are open covers in `X`. This is the
restriction `G|_U` of the tag, packaged as an object of `U.Sheaf (Type u)`. -/
@[ega "0 3.1.5", sga "4 III 1.9.2", sga "4 III 5.3" "Clause 2, special case"]
noncomputable def restrictSheaf (G : X.Sheaf (Type u)) : U.Sheaf (Type u) :=
  ⟨hj.functor.op ⋙ G.obj, Presheaf.isSheaf_of_isOpenEmbedding hj G.2⟩

/-- **Stacks 00A0 (1).** For a presheaf of sets `G` on `X`, the presheaf pullback
`j_p G` (the colimit-based left adjoint of `j_*`) is canonically isomorphic to
the naive restriction `V ↦ G(j V)`:
`(j_p G) ≅ restrictPresheaf hj G`.
Componentwise, for every open `V ⊆ U`, the canonical colimit map
`G(j V) → (j_p G)(V)` is a bijection (the colimit defining `(j_p G)(V)`
collapses to its value at the largest neighbourhood `j V = V`). The
isomorphism is exhibited as honest data: it is Mathlib's canonical
`IsOpenMap.pullbackObjIso`, whose `V`-component is the canonical comparison
`pullbackObjObjOfImageOpen`. -/
@[stacks 00A0 "(1)"]
noncomputable def presheaf_pullback_iso_restriction (G : X.Presheaf (Type u)) :
    (Presheaf.pullback (Type u) j).obj G ≅ restrictPresheaf j hj G :=
  hj.isOpenMap.pullbackObjIso G

/-- **Stacks 00A0 (1), naturality.** The isomorphism of clause (1) is natural
in `G`: it is the `G`-component of the natural isomorphism
`IsOpenMap.pullbackIso`, witnessing the canonical natural isomorphism of
functors `j_p ≅ (- ⋙ hj.functor.op)`. -/
theorem presheaf_pullback_iso_restriction_natural {G H : X.Presheaf (Type u)}
    (u : G ⟶ H) :
    (Presheaf.pullback (Type u) j).map u ≫ (presheaf_pullback_iso_restriction j hj H).hom
      = (presheaf_pullback_iso_restriction j hj G).hom ≫ Functor.whiskerLeft hj.functor.op u :=
  hj.isOpenMap.pullbackObjIso_hom_naturality u

/-- **Stacks 00A0 (2).** For a sheaf of sets `G` on `X`, the sheaf pullback
`j⁻¹ G` (sheafification of `j_p G`) is canonically isomorphic, as a *sheaf on
`U`*, to the restriction sheaf `restrictSheaf hj G` (no sheafification is needed,
by the sheaf condition built into `restrictSheaf`). The isomorphism lives in the
category `U.Sheaf (Type u)`. It is exhibited as honest data: the `G`-component of
Mathlib's canonical natural isomorphism `Topology.IsOpenEmbedding.sheafPullbackIso`
(note `(hj.sheafPullback _).obj G = restrictSheaf hj G` by definition). -/
@[stacks 00A0 "(2)",
  ega "0 3.7.1" "special case",
  sga "4 III 2.7" "Φ^* ≅ (i^{-1})^s",
  sga "4 III 5.3" "Clause 2, special case"]
noncomputable def sheaf_pullback_iso_restriction (G : X.Sheaf (Type u)) :
    (Sheaf.pullback (Type u) j).obj G ≅ restrictSheaf j hj G :=
  (hj.sheafPullbackIso (Type u)).app G

/-- **Stacks 00A0 (3).** For a sheaf of sets `G` on `X` and a point `u ∈ U`, the
stalk of the sheaf pullback `j⁻¹ G` at `u` is canonically isomorphic to the
stalk of `G` at `j u`:
`(j⁻¹ G)_u ≅ G_{j u}`.
This is the special case `f = j` of the canonical stalk identity
`(f⁻¹ G)_x ≅ G_{f x}`. It is exhibited as honest data, built from the canonical
comparison maps: the underlying presheaf of `j⁻¹ G` is canonically isomorphic to
the presheaf pullback `j_p (G^♭)` (via clause (2) and
`IsOpenMap.pullbackObjIso`), and `Presheaf.stalkPullbackIso` identifies the
stalk of the presheaf pullback at `u` with the stalk of `G` at `j u`. -/
@[stacks 00A0 "(3)"]
noncomputable def stalk_sheaf_pullback_iso (G : X.Sheaf (Type u)) (u : U) :
    Presheaf.stalk ((Sheaf.pullback (Type u) j).obj G).obj u
      ≅ Presheaf.stalk G.obj ((ConcreteCategory.hom j) u) :=
  ((Presheaf.stalkFunctor (Type u) u).mapIso
      (((sheafToPresheaf _ _).mapIso (sheaf_pullback_iso_restriction j hj G)) ≪≫
        (hj.isOpenMap.pullbackObjIso G.obj).symm)) ≪≫
    (Presheaf.stalkPullbackIso (Type u) j G.obj u).symm

/-- For an open embedding `j`, the presheaf
pushforward functor `j_* = Presheaf.pushforward (Type u) j` is fully faithful.

Mathematical argument. By definition `j_* F = (Opens.map j).op ⋙ F`, i.e. `j_*`
is *precomposition* with `(Opens.map j).op`. Mathlib's `IsOpenMap.adjunction`
gives an adjunction `hj.functor ⊣ Opens.map j` of the open-set posets, where
`hj.functor : Opens U ⥤ Opens X` sends `V ↦ j(V)`. The unit `η : 𝟙 ⟶ hj.functor ⋙
Opens.map j` sends `V ↦ j⁻¹(j(V)) = V` (using injectivity of the embedding `j`),
hence is an isomorphism; therefore the left adjoint `hj.functor` is fully
faithful (`Adjunction.fullyFaithfulLOfIsIsoUnit`), and so is its opposite
`hj.functor.op`. Oppositing the adjunction gives `(Opens.map j).op ⊣ hj.functor.op`
with `hj.functor.op` (the right adjoint) fully faithful, so its counit is an
isomorphism. Whiskering this adjunction into the presheaf category
(`Adjunction.whiskerLeft (Type u)`) produces an adjunction `(_ ⋙ hj.functor.op) ⊣
(_ ⋙ (Opens.map j).op) = j_*` whose counit is again an isomorphism (its
components are `F.map (counit)`, images of isos). A right adjoint with iso counit
is fully faithful (`Adjunction.fullyFaithfulROfIsIsoCounit`). Hence `j_*` is fully
faithful. -/
@[sga "4 IV 9.2.4" "a), special case"]
noncomputable def presheafPushforwardFullyFaithful
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j)) :
    (Presheaf.pushforward (Type u) j).FullyFaithful := by
  -- the unit of `hj.functor ⊣ Opens.map j` is an isomorphism
  haveI : IsIso (hj.isOpenMap.adjunction.unit) := by
    have happ : ∀ V : Opens U, IsIso (hj.isOpenMap.adjunction.unit.app V) := by
      intro V
      have hle : ((Opens.map j).obj (hj.functor.obj V)) ≤ V := by
        intro x hx
        have hx' : (ConcreteCategory.hom j) x ∈ (ConcreteCategory.hom j) '' (V : Set U) := hx
        rw [hj.injective.mem_set_image] at hx'
        exact hx'
      exact ⟨⟨homOfLE hle, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact NatIso.isIso_of_isIso_app _
  -- hence `hj.functor` is fully faithful
  haveI : hj.functor.Full := (Adjunction.fullyFaithfulLOfIsIsoUnit hj.isOpenMap.adjunction).full
  haveI : hj.functor.Faithful := (Adjunction.fullyFaithfulLOfIsIsoUnit
      hj.isOpenMap.adjunction).faithful
  -- opposite adjunction; its right adjoint `hj.functor.op` is fully faithful so counit is iso
  have adjOp : (Opens.map j).op ⊣ hj.functor.op := hj.isOpenMap.adjunction.op
  haveI : IsIso adjOp.counit := inferInstance
  -- whisker into presheaves: counit stays iso (componentwise `F.map (iso)`)
  haveI hladj : IsIso (Adjunction.whiskerLeft (Type u) adjOp).counit := by
    have happ2 : ∀ F, IsIso ((Adjunction.whiskerLeft (Type u) adjOp).counit.app F) := by
      intro F
      have happ3 : ∀ z, IsIso (((Adjunction.whiskerLeft (Type u) adjOp).counit.app F).app z) := by
        intro z
        rw [Adjunction.whiskerLeft_counit_app_app]
        have : IsIso (adjOp.counit.app z) := inferInstance
        exact Functor.map_isIso F (adjOp.counit.app z)
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  -- the lifted right adjoint is exactly `j_*`; iso counit ⇒ fully faithful
  exact @Adjunction.fullyFaithfulROfIsIsoCounit _ _ _ _ _ _
    (Adjunction.whiskerLeft (Type u) adjOp) hladj

/-- For an open embedding `j`, the sheaf pushforward
functor `j_* = Sheaf.pushforward (Type u) j` is fully faithful.

Mathematical argument. The forgetful functor `sheafToPresheaf` is fully faithful,
and `Sheaf.pushforward (Type u) j ⋙ sheafToPresheaf` is (definitionally) equal to
`sheafToPresheaf ⋙ Presheaf.pushforward (Type u) j` (the underlying presheaf of
the sheaf pushforward is the presheaf pushforward of the underlying presheaf,
`Sheaf.pushforward_obj_val`). The latter is a composite of two fully faithful
functors (`sheafToPresheaf` and `j_*` on presheaves, by
`presheafPushforwardFullyFaithful`), hence fully faithful. A functor `F` with
`F ⋙ G` fully faithful and `G` faithful is itself fully faithful
(`Functor.FullyFaithful.ofCompFaithful`), applied with `G = sheafToPresheaf`. -/
@[sga "4 IV 9.2.4" "a), special case"]
noncomputable def sheafPushforwardFullyFaithful
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j)) :
    (Sheaf.pushforward (Type u) j).FullyFaithful := by
  haveI ffp := presheafPushforwardFullyFaithful j hj
  have hcomp : (Sheaf.pushforward (Type u) j ⋙ sheafToPresheaf _ _).FullyFaithful :=
    (CategoryTheory.fullyFaithfulSheafToPresheaf _ _).comp ffp
  letI hF : (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat)) (Type u)).Faithful :=
    inferInstance
  exact @Functor.FullyFaithful.ofCompFaithful _ _ _ _ _ _ _ _ hF hcomp

/-- **Stacks 00A0 (3), canonical-map form.** The canonical stalk comparison map
`TopCat.Presheaf.stalkPullbackHom`,
`G_{j u} ⟶ (j_p G)_u`, is an isomorphism for every presheaf `G` on `X` and every
`u ∈ U`. (For an open embedding, neighbourhoods of `u` contained in `U` are
cofinal among neighbourhoods of `j u` in `X`, so the colimits agree.) This
pins down the bijection of clause (3) to the canonical map, before
sheafification.

Proof: Mathlib packages this comparison map as the *hom* of the canonical
isomorphism `Presheaf.stalkPullbackIso (Type u) j G u`; indeed
`(Presheaf.stalkPullbackIso (Type u) j G u).hom = Presheaf.stalkPullbackHom (Type u) j G u`
holds by `rfl`. Hence it is an isomorphism. (Mathlib already proves this canonical
stalk comparison is an iso for *every* continuous map; the open-embedding
hypothesis is not needed for this particular formulation.) -/
theorem stalkPullbackHom_isIso
    (j : U ⟶ X)
    (G : X.Presheaf (Type u)) (u : U) :
    IsIso (Presheaf.stalkPullbackHom (Type u) j G u) := by
  have h : Presheaf.stalkPullbackHom (Type u) j G u
      = (Presheaf.stalkPullbackIso (Type u) j G u).hom := rfl
  rw [h]
  infer_instance

/-- **Stacks 00A0 (4).** On the category `PSh(U)` of presheaves of sets on `U`,
the *canonical* natural transformation `j_p ∘ j_* ⟶ id` — namely the counit of
the adjunction `j_p ⊣ j_*` (`pullback ⊣ pushforward`) — is a natural
isomorphism. Equivalently, for every presheaf of sets `F` on `U` and every open
`V ⊆ U`, the canonical map `(j_p j_* F)(V) → F(V)` is a bijection, naturally in
`F`. This exhibits the canonical natural isomorphism `j_p ∘ j_* ≅ id_{PSh(U)}`.
The open-embedding hypothesis `hj` is required: for an arbitrary continuous `j`
this counit need not be an isomorphism.

Proof: A counit of an adjunction `L ⊣ R` is an isomorphism whenever the right
adjoint `R` is fully faithful (`Adjunction.counit_isIso_of_R_fully_faithful`).
Here `R = j_* = Presheaf.pushforward (Type u) j`, which is fully faithful for the
open embedding `j` by `presheafPushforwardFullyFaithful`. -/
@[stacks 00A0 "(4)", sga "4 IV 9.2.4" "a), special case"]
theorem presheaf_pullback_pushforward_counit_isIso
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j)) :
    IsIso (Presheaf.pullbackPushforwardAdjunction (Type u) j).counit := by
  have ff := presheafPushforwardFullyFaithful j hj
  have := ff.full
  have := ff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-- **Stacks 00A0 (5).** On the category `Sh(U)` of sheaves of sets on `U`, the
*canonical* natural transformation `j⁻¹ ∘ j_* ⟶ id` — namely the counit of the
adjunction `j⁻¹ ⊣ j_*` (`Sheaf.pullback ⊣ Sheaf.pushforward`) — is a natural
isomorphism. Equivalently, for every sheaf of sets `F` on `U` and every open
`V ⊆ U`, the canonical map `(j⁻¹ j_* F)(V) → F(V)` is a bijection, naturally in
`F`. This exhibits the canonical natural isomorphism `j⁻¹ ∘ j_* ≅ id_{Sh(U)}`.
The open-embedding hypothesis `hj` is required: for an arbitrary continuous `j`
this counit need not be an isomorphism.

Proof: As for clause (4), the counit of `Sheaf.pullback ⊣ Sheaf.pushforward`
is an isomorphism because its right adjoint `j_* = Sheaf.pushforward (Type u) j`
is fully faithful for the open embedding `j`
(`sheafPushforwardFullyFaithful`), via
`Adjunction.counit_isIso_of_R_fully_faithful`. -/
@[stacks 00A0 "(5)", ega "I 9.4.2" "(i)", sga "4 IV 9.2.4" "a), special case"]
theorem sheaf_pullback_pushforward_counit_isIso
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j)) :
    IsIso (Sheaf.pullbackPushforwardAdjunction (Type u) j).counit := by
  have ff := sheafPushforwardFullyFaithful j hj
  have := ff.full
  have := ff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

end OpenImmersionSheaves
