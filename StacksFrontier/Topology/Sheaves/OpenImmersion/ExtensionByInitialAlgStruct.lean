module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.PushforwardAlgStruct

/-!
# Extension by the initial object along an open immersion (Stacks 00AA)

Let `X` be a topological space, `j : U → X` the inclusion of an open subset, and
`(C, F)` a type of algebraic structure (Stacks 007L) whose category `C` has an
initial object `e`. The *extension by initial* functor

  `j_! : Sh(U, C) ⥤ Sh(X, C)`

is the sheafification of the presheaf extension `j_{p!}`, which sends `V ⊆ X` to
`F(V)` when `V ⊆ U` and to `e` otherwise. This file proves that `j_!` is full and
faithful, and that a sheaf `G ∈ Sh(X, C)` lies in its essential image exactly
when the stalk `G_x` is an initial object of `C` for every `x ∈ X ∖ U`.

## Shape of the formalization

`j_{p!}` is realized as the left Kan extension `(opensFunctor X U).op.lan` along
the opposite of the inclusion of opens, which is the pointwise formula the source
describes: at `V ⊆ U` the indexing category has a terminal object and the colimit
is `F(V)`, and at `V ⊄ U` it is empty and the colimit is `e`. Full faithfulness
then comes from the composite adjunction `lan ⊣ restriction` followed by
`sheafification ⊣ forget`, and the essential-image description is checked
stalkwise, using that `F` reflects isomorphisms to descend from `Type` to `C`.

007L itself is not re-encoded here: it is `AlgebraicStructureType`, the declaration
carrying the 007M tag, in
`StacksFrontier/Topology/Sheaves/AlgebraicStructure/Defs.lean`. The closed-inclusion
counterpart of this lemma (Stacks 00AH) is proved over the same structure in
`StacksFrontier/Topology/Sheaves/ClosedImmersion/PushforwardAlgStruct.lean`.

Note the `[HasColimits S.C]` in the statements below. 007L asks only for *filtered*
colimits; realizing `j_{p!}` as the left Kan extension `(opensFunctor X U).op.lan`
needs arbitrary ones, because the indexing comma category is empty at opens `V ⊄ U`
and the empty category is not filtered. So the results here are proved under a
hypothesis slightly stronger than 007L, and it is written into the statements rather
than hidden inside the bundle. Defining `j_{p!}` by the source's explicit formula
(`F(V)` for `V ⊆ U`, the initial object otherwise) would remove the hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

namespace Stacks

/-- The open inclusion `j : U → X` of an open subset, regarded as a morphism in `TopCat`. -/
@[implicit_reducible]
noncomputable def openInclusion (X : TopCat.{u}) (U : Opens X) : TopCat.of (U : Type _) ⟶ X :=
  TopCat.ofHom ⟨((↑) : U → X), continuous_subtype_val⟩

/-- The induced functor on opens `Opens U ⥤ Opens X` sending an open `V' ⊆ U` to itself viewed
as an open in `X`. -/
@[implicit_reducible]
noncomputable def opensFunctor (X : TopCat.{u}) (U : Opens X) : Opens (U : Type _) ⥤ Opens X :=
  IsOpenMap.functor (f := openInclusion X U) U.isOpen.isOpenMap_subtype_val

/-- The **presheaf extension by initial** `j_{p!}`.

This is the functor `Presheaf C U ⥤ Presheaf C X` defined as the left Kan extension of a
presheaf `F : (Opens U)ᵒᵖ ⥤ C` along the opposite of the open-inclusion functor on opens
`(opensFunctor X U)ᵒᵖ : (Opens U)ᵒᵖ ⥤ (Opens X)ᵒᵖ`.

Pointwise, the left Kan extension at `V ⊆ X` is computed as a colimit over open
neighborhoods `W ⊆ U` containing `V` (i.e. with `V ⊆ W` as subsets of `X`). When `V ⊆ U`, the
diagram has the terminal object `V` (viewed as an open in `U`), so the colimit reduces to
`F(V)`; when `V ⊄ U` the indexing category is empty, so the colimit is the initial object of
`C`. This is exactly the presheaf extension by initial object as described in the Stacks
Project. -/
@[implicit_reducible]
noncomputable def presheafExtByInitial (X : TopCat.{u}) (U : Opens X) {C : Type u} [Category.{u} C]
    [HasColimits C] : TopCat.Presheaf C (TopCat.of (U : Type _)) ⥤ TopCat.Presheaf C X :=
  (opensFunctor X U).op.lan

/-- **Extension by the initial object `j_!`.**

The functor `j_! : Sh(U, C) ⥤ Sh(X, C)` is defined as the sheafification of the presheaf
extension `j_{p!}`: take a sheaf on `U`, regard it as a presheaf, extend by the initial object
to obtain a presheaf on `X`, and then sheafify. -/
@[implicit_reducible]
noncomputable def jLowerShriek (X : TopCat.{u}) (U : Opens X) {C : Type u} [Category.{u} C]
    [HasColimits C] [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (TopCat.of (U : Type _)) ⥤ TopCat.Sheaf C X :=
  sheafToPresheaf _ _ ⋙ presheafExtByInitial X U ⋙ presheafToSheaf _ _

/-! ## Part 1: opensFunctor is fully faithful

The open inclusion functor `opensFunctor X U : Opens U ⥤ Opens X` is fully faithful because
it is the `IsOpenMap.functor` associated to the open map `Subtype.val : U → X`.
Faithfulness is already in Mathlib (`IsOpenMap.functor_faithful`). Fullness follows because
the functor maps an open `V` of `U` to the corresponding open subset of `X`, and any inclusion
between images in `Opens X` lifts to an inclusion in `Opens U`.
-/

/-- The open inclusion functor on opens is full.
    A morphism `opensFunctor(V) ⟶ opensFunctor(W)` in `Opens X` is a proof that `V ⊆ W`
    (as subsets of X). Since V, W are opens of U (subsets of U ⊆ X), this is the same as
    `V ⊆ W` in `Opens U`. -/
lemma opensFunctor_full (X : TopCat.{u}) (U : Opens X) : (opensFunctor X U).Full where
  map_surjective {_ W} f := ⟨homOfLE fun x hx => by
    obtain ⟨y, hy, hyx⟩ : (↑x : X) ∈ (Subtype.val '' (W : Set (↥U)) : Set X) :=
      leOfHom f ⟨x, hx, rfl⟩
    exact Subtype.val_injective hyx ▸ hy, Subsingleton.elim _ _⟩

/-- The open inclusion functor on opens is faithful (from Mathlib). -/
lemma opensFunctor_faithful (X : TopCat.{u}) (U : Opens X) : (opensFunctor X U).Faithful :=
  IsOpenMap.functor_faithful _

/-! ## Part 2: The presheaf extension (left Kan extension) is fully faithful

Since `opensFunctor X U` is fully faithful, so is `(opensFunctor X U).op`.
The left Kan extension along a fully faithful functor is fully faithful:
- The lan adjunction is `(opensFunctor X U).op.lan ⊣ whiskeringLeft`
  (from `Functor.lanAdjunction`)
- The unit of this adjunction is a natural isomorphism when the base functor is fully faithful
  (from `Functor.instIsIsoAppLanUnit_1` which requires `[L.Full] [L.Faithful]`
  and `[L.HasPointwiseLeftKanExtension F]`)
- By `Adjunction.fullyFaithfulLOfIsIsoUnit`, the left Kan extension functor is fully faithful
-/

/-- The presheaf extension by initial is fully faithful. -/
noncomputable def presheafExtByInitial_fullyFaithful (X : TopCat.{u}) (U : Opens X) {C : Type u}
    [Category.{u} C] [HasColimits C] [(opensFunctor X U).Full] [(opensFunctor X U).Faithful] :
    (presheafExtByInitial X U (C := C)).FullyFaithful := by
  have : IsIso ((opensFunctor X U).op.lanAdjunction C).unit := Functor.coreflective' _
  exact Adjunction.fullyFaithfulLOfIsIsoUnit ((opensFunctor X U).op.lanAdjunction C)

/-! ## Part 3: jLowerShriek is fully faithful

The functor `jLowerShriek = sheafToPresheaf ⋙ presheafExtByInitial ⋙ presheafToSheaf`.

**Proof strategy**: Construct the adjunction `jLowerShriek ⊣ j^*` and show the unit is an iso.

The right adjoint `j^*` (restriction to U) is defined as:
  `sheafToPresheaf ⋙ (whiskeringLeft _ _ _).obj (opensFunctor X U).op ⋙ presheafToSheaf`
(forget sheaf structure, restrict presheaf from X to U, then sheafify).

The adjunction `jLowerShriek ⊣ j^*` is the composite of:
- `Functor.lanAdjunction`: `lan ⊣ whiskeringLeft`
- `sheafificationAdjunction`: `presheafToSheaf ⊣ sheafToPresheaf`

The unit `η : Id → j^* ∘ j_!` at a sheaf `F` on `U` is:
  `F → sheafify(lan(F.presheaf) ∘ opensFunctor.op)`

This is an iso because:
1. The lan unit gives `F.presheaf ≅ lan(F.presheaf) ∘ opensFunctor.op`
   (since opensFunctor.op is fully faithful, by `instIsIsoAppLanUnit_1`)
2. `F.presheaf` is already a sheaf on U
3. Therefore `lan(F.presheaf) ∘ opensFunctor.op` is already a sheaf on U
4. Sheafifying a sheaf gives an isomorphic sheaf

By `Adjunction.fullyFaithfulLOfIsIsoUnit`, we conclude `jLowerShriek` is fully faithful.
-/

/-- The functor `opensFunctor X U : Opens U ⥤ Opens X` is cocontinuous for the Grothendieck
topologies of open covers. -/
instance opensFunctor_isCocontinuous (X : TopCat.{u}) (U : Opens X) :
    (opensFunctor X U).IsCocontinuous (Opens.grothendieckTopology (TopCat.of (U : Type _)))
      (Opens.grothendieckTopology X)
    where
  cover_lift := by
    intro V S hS x hx
    obtain ⟨W', f', hf', hxW'⟩ := hS (x : X) ⟨x, hx, rfl⟩
    exact
      ⟨⟨Subtype.val ⁻¹' (W' : Set X), W'.isOpen.preimage continuous_subtype_val⟩,
        homOfLE
          (fun y hy => by
            obtain ⟨z, hz, hzy⟩ := (leOfHom f') hy
            exact Subtype.val_injective hzy ▸ hz),
        S.downward_closed hf' (homOfLE (Set.image_preimage_subset _ _)),
        hxW'⟩

/-- The functor `opensFunctor X U : Opens U ⥤ Opens X` is continuous for the Grothendieck
topologies of open covers. -/
instance opensFunctor_isContinuous (X : TopCat.{u}) (U : Opens X) :
    (opensFunctor X U).IsContinuous (Opens.grothendieckTopology (TopCat.of (U : Type _)))
      (Opens.grothendieckTopology X) := by
  have : (opensFunctor X U).Full := opensFunctor_full X U
  have : (opensFunctor X U).Faithful := opensFunctor_faithful X U
  apply Functor.isContinuous_of_coverPreserving
  · apply compatiblePreservingOfDownwardsClosed
    intro V W hW
    set c' : Opens (U : Type _) :=
      ⟨Subtype.val ⁻¹' (W : Set X), W.isOpen.preimage continuous_subtype_val⟩
    refine ⟨c', ?_⟩
    have heq : (opensFunctor X U).obj c' = W := by
      apply Opens.ext
      simp only [opensFunctor, IsOpenMap.functor, Opens.coe_mk, c']
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        obtain ⟨y, -, rfl⟩ := leOfHom hW hx
        exact ⟨y, hx, rfl⟩
    exact heq ▸ Iso.refl _
  · constructor
    intro V S hS x hx
    obtain ⟨y, hyV, rfl⟩ : x ∈ (Subtype.val '' (V : Set (↥U)) : Set X) := hx
    obtain ⟨W, f, hf, hyW⟩ := hS y hyV
    exact ⟨_, (opensFunctor X U).map f, ⟨W, f, 𝟙 _, hf, by simp⟩, ⟨y, hyW, rfl⟩⟩

/-- The adjunction `j_! ⊣ j^*`, obtained from `lan ⊣ restriction` and
`sheafification ⊣ forget`. -/
private noncomputable def jLowerShriekAdjunction (S : AlgebraicStructureType.{u, u})
    [HasColimits S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C] :
    jLowerShriek (C := S.C) X U ⊣ (opensFunctor X U).sheafPushforwardContinuous S.C
      (Opens.grothendieckTopology (TopCat.of (U : Type _))) (Opens.grothendieckTopology X) :=
  Adjunction.restrictFullyFaithful
    ((opensFunctor X U).op.lanAdjunction S.C |>.comp
      (sheafificationAdjunction (Opens.grothendieckTopology X) S.C))
    (Functor.FullyFaithful.ofFullyFaithful
      (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C))
    (Functor.FullyFaithful.ofFullyFaithful (𝟭 _)) (Functor.associator _ _ _ |>.symm) (Iso.refl _)

/-- The unit of `j_! ⊣ j^*` is an isomorphism. -/
private instance isIso_jLowerShriekAdjunction_unit (S : AlgebraicStructureType.{u, u})
    [HasColimits S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C] :
    IsIso (jLowerShriekAdjunction S X U).unit := by
  have : (opensFunctor X U).Full := opensFunctor_full X U
  have : (opensFunctor X U).Faithful := opensFunctor_faithful X U
  set L := (opensFunctor X U).op
  set G := opensFunctor X U
  set J_X := Opens.grothendieckTopology X
  set J_U := Opens.grothendieckTopology (TopCat.of (U : Type _))
  have hiso_lan : IsIso (L.lanAdjunction S.C).unit := Functor.coreflective' L
  have lan_whisker_iso : L.lan ⋙ (Functor.whiskeringLeft _ _ S.C).obj L ≅ 𝟭 _ :=
    (asIso (L.lanAdjunction S.C).unit).symm
  have sheaf_round_trip : sheafToPresheaf J_U S.C ⋙ presheafToSheaf J_U S.C ≅ 𝟭 _ := by
    have : IsIso (sheafificationAdjunction J_U S.C).counit := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun S => isIso_sheafificationAdjunction_counit S
    exact asIso (sheafificationAdjunction J_U S.C).counit
  have main_iso :
    jLowerShriek (C := S.C) X U ⋙ G.sheafPushforwardContinuous S.C J_U J_X ≅ 𝟭 _ := by
    have inner :
      (L.lan ⋙ presheafToSheaf J_X S.C) ⋙ G.sheafPushforwardContinuous S.C J_U J_X ≅
        presheafToSheaf J_U S.C :=
      (Functor.associator _ _ _) ≪≫
        NatIso.hcomp (Iso.refl L.lan)
          (G.pushforwardContinuousSheafificationCompatibility S.C J_U J_X).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        NatIso.hcomp lan_whisker_iso (Iso.refl _) ≪≫ Functor.leftUnitor _
    change
      (sheafToPresheaf J_U S.C ⋙
          ((L.lan ⋙ presheafToSheaf J_X S.C) ⋙ G.sheafPushforwardContinuous S.C J_U J_X)) ≅
        𝟭 _
    exact NatIso.hcomp (Iso.refl (sheafToPresheaf J_U S.C)) inner ≪≫ sheaf_round_trip
  exact Adjunction.isIso_unit_of_iso _ main_iso

/-- `jLowerShriek` is Full. -/
lemma jLowerShriek_full (S : AlgebraicStructureType.{u, u}) [HasColimits S.C] [HasInitial S.C]
    (X : TopCat.{u}) (U : Opens X) [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C] :
    (jLowerShriek (C := S.C) X U).Full :=
  (Adjunction.fullyFaithfulLOfIsIsoUnit (jLowerShriekAdjunction S X U)).full

/-- `jLowerShriek` is Faithful. -/
lemma jLowerShriek_faithful (S : AlgebraicStructureType.{u, u}) [HasColimits S.C] [HasInitial S.C]
    (X : TopCat.{u}) (U : Opens X) [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C] :
    (jLowerShriek (C := S.C) X U).Faithful :=
  (Adjunction.fullyFaithfulLOfIsIsoUnit (jLowerShriekAdjunction S X U)).faithful

/-! ## Part 4: Essential image characterization

**Forward direction**: If `G ≅ j_!(F)` for some sheaf `F` on `U`, then for `x ∉ U`,
the stalk `G_x` is initial.

Proof:
- `G.stalk x ≅ (j_!(F)).stalk x` (isomorphic sheaves have isomorphic stalks)
- `(j_!(F)).stalk x = (sheafify(lan(F.presheaf))).stalk x ≅ (lan(F.presheaf)).stalk x`
  (sheafification preserves stalks)
- The stalk of `lan(F.presheaf)` at `x` is the colimit of the diagram indexed by the
  comma category `CostructuredArrow (opensFunctor X U).op (op V)` as `V` ranges over
  neighborhoods of `x`. For `x ∉ U`, eventually the neighborhoods `V` are not contained in `U`,
  so the indexing category becomes empty, and the colimit over the empty diagram is initial.
- More precisely: the stalk is the filtered colimit `colim_{V ∋ x} (lan(F.presheaf))(V)`.
  When `V ⊄ U`, `(lan(F.presheaf))(V) = colim_{W ⊆ U, V ⊆ opensFunctor(W)} F.presheaf(W)`,
  which is a colimit over an empty category (no `W ⊆ U` satisfies `V ⊆ W` when `V` is not in U)
  = initial object.
- Therefore all terms in the filtered colimit for the stalk are initial, hence the colimit is
initial.

**Backward direction**: If `∀ x ∉ U, G_x is initial`, then `G ∈ essImage(j_!)`.

Proof:
- Define `F := j^*(G)` (restriction of G to U).
- Construct a natural map `φ : j_!(F) → G` (the counit of the adjunction `j_! ⊣ j^*`).
- Show `φ` is an isomorphism by checking it induces isomorphisms on all stalks:
  - At `x ∈ U`: The stalk of `j_!(j^*G)` at `x ∈ U` is isomorphic to `(j^*G)_x = G_x`
    (since the unit of `j_! ⊣ j^*` is an iso, stalks at points in U are preserved).
  - At `x ∉ U`: Both `(j_!(j^*G))_x` and `G_x` are initial objects, and any morphism
    between initial objects is an isomorphism.
- Use that `F` (the forgetful functor to `Type u`) reflects isomorphisms to conclude `φ` is an iso.
- Therefore `G ≅ j_!(j^*G)`, so `G ∈ essImage(j_!)`.
-/

private noncomputable def lan_obj_isInitial' (X : TopCat.{u}) (U : Opens X) {C : Type u}
    [Category.{u} C] [HasColimits C] (P : TopCat.Presheaf C (TopCat.of (U : Type _))) (V : Opens X)
    (x : X) (hxV : x ∈ V) (hxU : x ∉ (U : Set X)) :
    IsInitial (((opensFunctor X U).op.lan.obj P).obj (op V)) := by
  set L := (opensFunctor X U).op
  haveI hempty : IsEmpty (CostructuredArrow L (op V)) := by
    constructor
    intro ⟨W_op, _, f⟩
    obtain ⟨z, -, hz⟩ := leOfHom f.unop hxV
    exact hxU (hz ▸ z.2)
  have iso := L.leftKanExtensionObjIsoColimit P (op V)
  set D := CostructuredArrow.proj L (op V) ⋙ P
  have hinit : IsInitial (colimit D) := by
    refine IsColimit.mk (fun s => ?_) (fun s j => ?_) (fun s m _ => ?_)
    · exact
        colimit.desc D ⟨s.pt, ⟨fun j => (hempty.false j).elim, fun {j} => (hempty.false j).elim⟩⟩
    · exact j.as.elim
    · apply colimit.hom_ext (F := D)
      intro j
      exact (hempty.false j).elim
  exact IsInitial.ofIso hinit iso.symm

private noncomputable def isInitial_colimit_of_all_initial' {J : Type u} [Category.{u} J]
    {C : Type u} [Category.{u} C] (F : J ⥤ C) [HasColimit F] (hF : ∀ j, IsInitial (F.obj j)) :
    IsInitial (colimit F) :=
  IsInitial.ofUniqueHom
    (fun Y => colimit.desc F ⟨Y, ⟨fun j => (hF j).to Y, fun {j} _ _ => (hF j).hom_ext _ _⟩⟩)
    (fun _ _ => colimit.hom_ext fun j => (hF j).hom_ext _ _)

/-- The stalk of the presheaf extension by initial at a point outside U is initial. -/
private noncomputable def lan_stalk_isInitial' (X : TopCat.{u}) (U : Opens X) {C : Type u}
    [Category.{u} C] [HasColimits C] (P : TopCat.Presheaf C (TopCat.of (U : Type _))) (x : X)
    (hxU : x ∉ (U : Set X)) :
    IsInitial (TopCat.Presheaf.stalk ((opensFunctor X U).op.lan.obj P) x) := by
  change IsInitial (colimit ((OpenNhds.inclusion x).op ⋙ (opensFunctor X U).op.lan.obj P))
  exact isInitial_colimit_of_all_initial' _ fun ⟨V, hxV⟩ => lan_obj_isInitial' X U P V x hxV hxU

/-- Sheafification preserves stalks: the adjunction unit P → sheafToPresheaf(presheafToSheaf P)
induces an isomorphism on stalks. This is a fundamental property for the Opens topology
on a topological space with a type of algebraic structure. -/
noncomputable def sheafification_stalk_iso (S : AlgebraicStructureType.{u, u}) [HasColimits S.C]
    (X : TopCat.{u}) [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    (P : TopCat.Presheaf S.C X) (x : ↑X) :
    P.stalk x ≅
      TopCat.Presheaf.stalk
        ((sheafToPresheaf _ S.C).obj ((presheafToSheaf (Opens.grothendieckTopology X) S.C).obj P))
        x := by
  set J := Opens.grothendieckTopology X
  set η := (sheafificationAdjunction J S.C).unit.app P
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor S.C x).map η) := by
    rw [show η = toSheafify J P from sheafificationAdjunction_unit_app J P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x S.C P
  exact @asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor S.C x).map η) hiso

/-- A sheaf in the essential image of `jLowerShriek X U` has initial stalks at all points outside
`U`. -/
lemma essImage_imp_stalks_initial (S : AlgebraicStructureType.{u, u}) [HasColimits S.C]
    [HasInitial S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C]
    (G : TopCat.Sheaf S.C X) (hG : (jLowerShriek (C := S.C) X U).essImage G) :
    ∀ x : X, x ∉ (U : Set X) → Nonempty (IsInitial (G.presheaf.stalk x)) := by
  intro x hxU
  obtain ⟨F', ⟨iso⟩⟩ := hG
  have h : IsInitial ((jLowerShriek (C := S.C) X U |>.obj F').presheaf.stalk x) :=
    (lan_stalk_isInitial' X U F'.presheaf x hxU).ofIso (sheafification_stalk_iso S X _ x)
  exact ⟨h.ofIso ((TopCat.Presheaf.stalkFunctor S.C x).mapIso ((sheafToPresheaf _ S.C).mapIso iso))⟩

private lemma colimMap_whiskerRight_eq' {J : Type*} [Category J] {C : Type*} [Category C]
    {D : Type*} [Category D] (G : C ⥤ D) {F₁ F₂ : J ⥤ C} [HasColimit F₁] [HasColimit F₂]
    [HasColimit (F₁ ⋙ G)] [HasColimit (F₂ ⋙ G)] [PreservesColimit F₁ G] [PreservesColimit F₂ G]
    (β : F₁ ⟶ F₂) :
    colimMap (Functor.whiskerRight β G) =
      (preservesColimitIso G F₁).inv ≫ G.map (colimMap β) ≫ (preservesColimitIso G F₂).hom := by
  ext j
  rw [ι_colimMap, ι_preservesColimitIso_inv_assoc, ← G.map_comp_assoc, ι_colimMap,
    G.map_comp_assoc, ι_preservesColimitIso_hom, Functor.whiskerRight_app]

private lemma sheafIsIso_of_stalkwise_iso' {C : Type u} [Category.{u} C] [HasColimits C]
    [HasLimits C] (F : C ⥤ Type u) [F.Faithful] [PreservesLimits F] [F.ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} F] {X : TopCat.{u}} {P Q : TopCat.Sheaf C X}
    (f : P ⟶ Q) (hiso : ∀ x : ↑X, IsIso ((TopCat.Presheaf.stalkFunctor C x).map f.hom)) :
    IsIso f := by
  let J := Opens.grothendieckTopology (↑X : Type _)
  let PF : Sheaf J (Type u) :=
    ⟨P.obj ⋙ F, GrothendieckTopology.HasSheafCompose.isSheaf P.obj P.property⟩
  let QF : Sheaf J (Type u) :=
    ⟨Q.obj ⋙ F, GrothendieckTopology.HasSheafCompose.isSheaf Q.obj Q.property⟩
  let fF : PF ⟶ QF := ObjectProperty.homMk (((Functor.whiskeringRight _ _ _).obj F).map f.hom)
  have hfF_stalk : ∀ x : ↑X, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map fF.hom) := by
    intro x
    show IsIso (colimMap (Functor.whiskerRight ((OpenNhds.inclusion x).op.whiskerLeft f.hom) F))
    rw [colimMap_whiskerRight_eq']
    have : IsIso (colimMap ((OpenNhds.inclusion x).op.whiskerLeft f.hom)) := hiso x
    exact IsIso.comp_isIso
  have hfF_iso : IsIso fF := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fF
  have hfF_hom_iso : IsIso fF.hom := inferInstance
  refine (ObjectProperty.isIso_hom_iff f).mp ?_
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  have : IsIso (F.map (f.hom.app U)) := (NatTrans.isIso_iff_isIso_app fF.hom).mp hfF_hom_iso U
  exact isIso_of_reflects_iso _ F

/-- Restricted to `U`, the counit of `j_! ⊣ j^*` is an isomorphism of presheaves. -/
private lemma isIso_sheafPushforwardContinuous_map_counit_hom (S : AlgebraicStructureType.{u, u})
    [HasColimits S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C]
    (G : TopCat.Sheaf S.C X) :
    IsIso ((opensFunctor X U |>.sheafPushforwardContinuous S.C
      (Opens.grothendieckTopology (TopCat.of (U : Type _))) (Opens.grothendieckTopology X)).map
        ((jLowerShriekAdjunction S X U).counit.app G)).hom := by
  set Gf := opensFunctor X U
  set J_X := Opens.grothendieckTopology X
  set J_U := Opens.grothendieckTopology (TopCat.of (U : Type _))
  set adj := jLowerShriekAdjunction S X U
  have : IsIso adj.unit := isIso_jLowerShriekAdjunction_unit S X U
  have hRcounit :
      IsIso ((Gf.sheafPushforwardContinuous S.C J_U J_X).map (adj.counit.app G)) := by
    have :
        IsIso
          (adj.unit.app ((Gf.sheafPushforwardContinuous S.C J_U J_X).obj G) ≫
            (Gf.sheafPushforwardContinuous S.C J_U J_X).map (adj.counit.app G)) :=
      adj.right_triangle_components G ▸ IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  infer_instance

/-- The functor on open neighbourhoods induced by the inclusion of an open `U ⊆ X`, at a point
`x ∈ U`. -/
private noncomputable def openNhdsFunctor (X : TopCat.{u}) (U : Opens X) (x : X)
    (hxU : x ∈ (U : Set X)) : @OpenNhds (TopCat.of (U : Type _)) ⟨x, hxU⟩ ⥤ @OpenNhds X x where
  obj V := ⟨(opensFunctor X U).obj V.1, ⟨⟨x, hxU⟩, V.2, rfl⟩⟩
  map f := homOfLE ((opensFunctor X U).monotone (leOfHom f))

/-- `openNhdsFunctor` is initial, being left adjoint to taking preimages along the inclusion. -/
private instance openNhdsFunctor_initial (X : TopCat.{u}) (U : Opens X) (x : X)
    (hxU : x ∈ (U : Set X)) : (openNhdsFunctor X U x hxU).Initial := by
  let R : @OpenNhds X x ⥤ @OpenNhds (TopCat.of (U : Type _)) ⟨x, hxU⟩ :=
    { obj := fun W => ⟨(Opens.map (openInclusion X U)).obj W.1, W.2⟩
      map := fun f => homOfLE ((Opens.map (openInclusion X U)).monotone (leOfHom f)) }
  have adj : openNhdsFunctor X U x hxU ⊣ R :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun V W =>
          { toFun := fun h => homOfLE fun z hz => leOfHom h ⟨z, hz, rfl⟩
            invFun := fun h => homOfLE <| by
              rintro _ ⟨a, haV, rfl⟩
              exact leOfHom h haV
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _ } }
  exact Functor.initial_of_adjunction adj

/-- At a point `x ∈ U`, the counit of `j_! ⊣ j^*` induces an isomorphism on stalks. -/
private lemma isIso_stalkFunctor_map_counit_of_mem (S : AlgebraicStructureType.{u, u})
    [HasColimits S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C]
    (G : TopCat.Sheaf S.C X) (x : X) (hxU : x ∈ (U : Set X)) :
    IsIso ((TopCat.Presheaf.stalkFunctor S.C x).map
      ((jLowerShriekAdjunction S X U).counit.app G).hom) := by
  set Gf := opensFunctor X U
  set J_X := Opens.grothendieckTopology X
  set J_U := Opens.grothendieckTopology (TopCat.of (U : Type _))
  set adj := jLowerShriekAdjunction S X U
  have hRcounit_hom :
      IsIso ((Gf.sheafPushforwardContinuous S.C J_U J_X).map (adj.counit.app G)).hom :=
    isIso_sheafPushforwardContinuous_map_counit_hom S X U G
  let y : ↑(TopCat.of (U : Type _) : TopCat.{u}) := ⟨x, hxU⟩
  let L_nhds : @OpenNhds (TopCat.of (U : Type _)) y ⥤ @OpenNhds X x := openNhdsFunctor X U x hxU
  have : L_nhds.Initial := openNhdsFunctor_initial X U x hxU
  have : L_nhds.op.Final := Functor.final_op_of_initial L_nhds
  have heq_nat :
      (OpenNhds.inclusion y).op.whiskerLeft
          ((Gf.sheafPushforwardContinuous S.C J_U J_X).map (adj.counit.app G)).hom =
        L_nhds.op.whiskerLeft ((OpenNhds.inclusion x).op.whiskerLeft (adj.counit.app G).hom) := by
    ext ⟨V⟩
    rfl
  have hstalk_y : IsIso (colimMap (L_nhds.op.whiskerLeft
      ((OpenNhds.inclusion x).op.whiskerLeft (adj.counit.app G).hom))) := by
    rw [← heq_nat]
    exact Functor.map_isIso (TopCat.Presheaf.stalkFunctor S.C y)
      ((Gf.sheafPushforwardContinuous S.C J_U J_X).map (adj.counit.app G)).hom
  have pre_map_eq :=
    colimit.pre_map ((OpenNhds.inclusion x).op.whiskerLeft (adj.counit.app G).hom) L_nhds.op
  rw [colim_map, colim_map] at pre_map_eq
  have :
      IsIso
        (colimit.pre _ L_nhds.op ≫
          colimMap ((OpenNhds.inclusion x).op.whiskerLeft (adj.counit.app G).hom)) := by
    rw [pre_map_eq]
    exact IsIso.comp_isIso
  exact
    IsIso.of_isIso_comp_left (colimit.pre _ L_nhds.op)
      (colimMap ((OpenNhds.inclusion x).op.whiskerLeft (adj.counit.app G).hom))

/-- A sheaf `G` on `X` whose stalks at all points outside `U` are initial lies in the essential
image of `jLowerShriek X U`. -/
lemma stalks_initial_imp_essImage (S : AlgebraicStructureType.{u, u}) [HasColimits S.C]
    [HasInitial S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C]
    (G : TopCat.Sheaf S.C X)
    (hG : ∀ x : X, x ∉ (U : Set X) → Nonempty (IsInitial (G.presheaf.stalk x))) :
    (jLowerShriek (C := S.C) X U).essImage G := by
  have : IsIso ((jLowerShriekAdjunction S X U).counit.app G) := by
    apply sheafIsIso_of_stalkwise_iso' S.F
    intro x
    by_cases hxU : x ∈ (U : Set X)
    · exact isIso_stalkFunctor_map_counit_of_mem S X U G x hxU
    · have hLRG_init :
          IsInitial
            ((jLowerShriek (C := S.C) X U |>.obj
                ((opensFunctor X U).sheafPushforwardContinuous S.C
                  (Opens.grothendieckTopology (TopCat.of (U : Type _)))
                  (Opens.grothendieckTopology X) |>.obj G)).presheaf.stalk x) :=
        (essImage_imp_stalks_initial S X U _ (Functor.obj_mem_essImage _ _) x hxU).some
      exact isIso_of_isInitial hLRG_init (hG x hxU).some _
  exact Adjunction.mem_essImage_of_counit_isIso (jLowerShriekAdjunction S X U) G

/-- Essential image characterization combined. -/
lemma jLowerShriek_essImage_iff (S : AlgebraicStructureType.{u, u}) [HasColimits S.C]
    [HasInitial S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C]
    (G : TopCat.Sheaf S.C X) :
    (jLowerShriek (C := S.C) X U).essImage G ↔
      ∀ x : X, x ∉ (U : Set X) → Nonempty (IsInitial (G.presheaf.stalk x)) :=
  ⟨essImage_imp_stalks_initial S X U G, stalks_initial_imp_essImage S X U G⟩

/-- **Stacks 00AA.** For `S = (C, F)` a type of algebraic structure whose category
`C` has an initial object, and `j : U → X` the inclusion of an open subset, the
extension-by-initial functor `j_! : Sh(U, C) ⥤ Sh(X, C)` is full and faithful, and
a sheaf `G ∈ Sh(X, C)` lies in its essential image exactly when the stalk `G_x` is
an initial object of `C` for every `x ∈ X ∖ U`. -/
@[stacks 00AA]
theorem full_and_faithful_and_essImage_jLowerShriek (S : AlgebraicStructureType.{u, u})
    [HasColimits S.C] [HasInitial S.C] (X : TopCat.{u}) (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) S.C]
    [HasWeakSheafify (Opens.grothendieckTopology (TopCat.of (U : Type _))) S.C] :
    (jLowerShriek (C := S.C) X U).Full ∧
      (jLowerShriek (C := S.C) X U).Faithful ∧
      ∀ G : TopCat.Sheaf S.C X,
        (jLowerShriek (C := S.C) X U).essImage G ↔
          ∀ x : X, x ∉ (U : Set X) → Nonempty (IsInitial (G.presheaf.stalk x)) :=
  ⟨jLowerShriek_full S X U, jLowerShriek_faithful S X U, jLowerShriek_essImage_iff S X U⟩

end Stacks
