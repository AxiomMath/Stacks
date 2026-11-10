module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.OpenSubspace
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks tag 0CAH (Lemma 17.19.1).

Let `X` be a topological space, let `B` be a basis for the topology on `X`, and let `F`
be a sheaf of *sets* on `X`.  Then there exist:

* an index set `I`,
* for each `i ∈ I` an element `U i ∈ B`,
* for each `i ∈ I` a finite set `S i`,

together with a morphism of sheaves of sets

  `φ : ∐_{i ∈ I} j_{U i !} (constant sheaf S i on U i)  ⟶  F`

that is a surjection (epimorphism in `Sh(X)`).

Here `constant sheaf (S i) on (U i)` is the constant sheaf with value `S i` on the open
subspace `U i` (Stacks 006W), `j_{U i !}` is extension by the empty set to `X`
(Stacks 00A1/00A2), the coproduct is taken in the category of sheaves of sets on `X`
(Definition 5), and "surjection" means epimorphism in `Sh(X)` (Definition 6).

## Notes on the formalization

Sheaves of sets on a space `Y` are `TopCat.Sheaf (Type u) Y` (with the Grothendieck topology
`Opens.grothendieckTopology Y`).  We model the constructions of the source in three explicitly
separated steps, matching the three sub-constructions of `j_{U!}(constant sheaf)`:

* **Step 1 — Constant sheaf on `U` (Def. 3, Stacks 006W).**
  For an open `U ⊆ X` we regard `U` as a topological space (the subspace `subspace X U`,
  i.e. `(Opens.toTopCat X).obj U`).  The constant sheaf with value `S` on this space is
  `constSheafOn X U S`, defined using Mathlib's `CategoryTheory.constantSheaf`, i.e. the
  *sheafification of the constant presheaf* `V ↦ S`.  This is exactly the parenthetical
  characterization in Definition 3.

* **Step 2 — The presheaf `j_{U,p!}` (Def. 4, first bullet, Stacks 00A1).**
  For a presheaf `G` on the subspace `U`, the presheaf `jpExtend X U G` on `X` assigns to an
  open `V ⊆ X` the sections `G(V)` when `V ⊆ U` (here `V` is viewed as an open of `U` via
  `Opens.map U.inclusion'`) and the empty set when `V ⊄ U`.  We encode this with the subtype
  `{ _s : G.obj (op ((Opens.map U.inclusion').obj V)) // V ≤ U }`, which is `G(V)` when `V ≤ U`
  (the witness being a `Prop`) and is empty otherwise.

* **Step 3 — Extension by the empty set `j_{U!}` (Def. 4, second bullet, Stacks 00A2).**
  For a *sheaf* `G` on the subspace `U`, `jExtend X U G` is the sheafification of
  `jpExtend X U G.presheaf`.  This is a sheaf of sets on `X`.  Composing Steps 1–3 we obtain
  `jExtendConst X U S = jExtend X U (constSheafOn X U S)`, which is `j_{U!}(constant sheaf S)`.

  The separation of these three steps directly mirrors the construction in the source; in
  particular the constant sheaf step (Step 1) and the `j_!` step (Steps 2–3) are not conflated.
  We record (as unproved correctness statements) the stalk characterization of `jExtend`
  (Stacks 00A3(3)), which uniquely pins down the construction.

* **Coproduct (Def. 5).**  We use the genuine categorical coproduct `∐` in the category
  `TopCat.Sheaf (Type u) X` of sheaves of sets on `X`.  The sheaf category has these coproducts
  because `Type u` has coproducts and the sheaf category has sheafification; we record the
  `HasColimitsOfShape (Discrete I)` instance below so the `∐` notation resolves.

* **Surjection (Def. 6).**  A morphism of sheaves of sets is a surjection iff it is an
  epimorphism in `Sh(X)`.  We state the conclusion as the existence of a morphism `φ` out of the
  categorical coproduct together with `Epi φ`.
-/

open TopCat CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace Stacks.Sheaves.ConstantSheafGenerators

/-- The category of sheaves of sets on `X` has coproducts indexed by any type `I : Type u`.
This follows from `CategoryTheory.Sheaf.instHasColimitsOfShape` (the sheaf category inherits
colimits from the value category `Type u` via sheafification); we record it as a global instance
so that the coproduct notation `∐` resolves for these sheaves. -/
instance topCatSheafHasColimitsOfShapeDiscrete (X : TopCat.{u}) (I : Type u) :
    HasColimitsOfShape (Discrete I) (TopCat.Sheaf (Type u) X) :=
  CategoryTheory.Sheaf.instHasColimitsOfShape

variable (X : TopCat.{u}) (U : Opens X)

/-! ## Main Definitions -/

/-- An open subset `U ⊆ X`, regarded as a topological space (the subspace) in its own right.
This is `Stacks.Topology.openSubspace` under the name this file uses, with `X` explicit. -/
abbrev subspace : TopCat.{u} := Stacks.Topology.openSubspace U

/-- **Step 1 (Def. 3, Stacks 006W).**  The constant sheaf with value `S` on the open subspace
`U`.  We use Mathlib's `CategoryTheory.constantSheaf`, namely the sheafification of the constant
presheaf `V ↦ S`; this is exactly the characterization of the constant sheaf in Definition 3. -/
noncomputable def constSheafOn (S : Type u) : TopCat.Sheaf (Type u) (subspace X U) :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology (subspace X U)) (Type u)).obj S

/-- Sections over an open `V ⊆ X` of the presheaf `j_{U,p!} G`: a section of `G` over `V`
(viewed as an open of the subspace `U`) together with a witness that `V ⊆ U`.  When `V ⊄ U`
this type is empty, encoding "extension by the empty set". -/
abbrev JpSection (G : TopCat.Presheaf (Type u) (subspace X U)) (V : Opens X) : Type u :=
  { _s : G.obj (op ((Opens.map U.inclusion').obj V)) // V ≤ U }

/-- **Step 2 (Def. 4, first bullet, Stacks 00A1).**  The presheaf `j_{U,p!} G` on `X` associated
to a presheaf `G` on the subspace `U`: over an open `V ⊆ X` it is `G(V)` if `V ⊆ U` and is the
empty set otherwise, with restriction maps given by the restriction maps of `G`. -/
noncomputable def jpExtend (G : TopCat.Presheaf (Type u) (subspace X U)) :
    TopCat.Presheaf (Type u) X where
  obj V := JpSection X U G V.unop
  map {V W} i := TypeCat.ofHom (fun (p : JpSection X U G V.unop) =>
    (⟨G.map ((Opens.map U.inclusion').op.map i) p.1,
        le_trans (leOfHom i.unop) p.2⟩ : JpSection X U G W.unop))
  map_id V := by
    ext p
    simp only [CategoryTheory.Functor.map_id]
    rfl
  map_comp {V W Z} i j := by
    ext p
    simp only [CategoryTheory.Functor.map_comp]
    rfl

/-- **Step 3 (Def. 4, second bullet, Stacks 00A2).**  The extension by the empty set `j_{U!} G`
of a *sheaf* `G` on the subspace `U`: the sheafification of the presheaf `j_{U,p!} G`.  This is a
sheaf of sets on `X`. -/
@[sga "4 III 1.9.2"]
noncomputable def jExtend (G : TopCat.Sheaf (Type u) (subspace X U)) :
    TopCat.Sheaf (Type u) X :=
  (jpExtend X U G.presheaf).sheafify

/-- The extension by the empty set of the constant sheaf with value `S` on `U`, i.e.
`j_{U!}(constant sheaf S)` (Steps 1–3 composed). -/
noncomputable def jExtendConst (S : Type u) : TopCat.Sheaf (Type u) X :=
  jExtend X U (constSheafOn X U S)

/-! ## Correctness statement for `jExtend` (Stacks 00A3(3)) -/

/-- **Correctness of `jExtend` via stalks (Stacks 00A3(3)).**  For a sheaf `G` on the subspace
`U` and a point `x : X` with `x ∈ U`, the stalk of `j_{U!} G` at `x` agrees with the stalk of
`G` at the corresponding point of `U`; and for `x ∉ U` the stalk of `j_{U!} G` at `x` is empty
(`IsEmpty`).  This uniquely characterizes the extension-by-empty construction, and in particular
confirms that our direct construction `jExtend`/`jExtendConst` agrees with the intended
`j_{U!}(constant sheaf)` of the source. -/
theorem jExtend_stalk_isEmpty_of_not_mem
    (G : TopCat.Sheaf (Type u) (subspace X U)) (x : X) (hx : x ∉ U) :
    IsEmpty ((jExtend X U G).presheaf.stalk x) := by
  -- SANITY CHECK PASSED (no counterexample; faithful encoding of Stacks 00A3(3), empty-stalk case)
  have : IsEmpty ((jpExtend X U G.presheaf).stalk x) := ⟨fun t => by
    obtain ⟨V, m, s, _⟩ := TopCat.Presheaf.exists_germ_eq (jpExtend X U G.presheaf) t
    exact hx (s.2 m)⟩
  exact Function.isEmpty
    ((TopCat.Presheaf.sheafifyStalkIso (jpExtend X U G.presheaf) x).hom)

/-- Every open of the subspace `U` is the preimage of an open `V ≤ U` of `X`. -/
private theorem exists_le_map_inclusion'_eq (W : Opens (subspace X U)) :
    ∃ V : Opens X, V ≤ U ∧ (Opens.map U.inclusion').obj V = W ∧
      ∀ (z : subspace X U), (Subtype.val z : X) ∈ V ↔ z ∈ W := by
  have hmemV : ∀ (z : subspace X U), (Subtype.val z : X) ∈
      (⟨Subtype.val '' W.carrier, U.isOpenEmbedding'.isOpenMap W.carrier W.2⟩ : Opens X) ↔
        z ∈ W := by
    intro z
    change (Subtype.val z) ∈ Subtype.val '' W.carrier ↔ z ∈ W
    exact Subtype.val_injective.mem_set_image
  refine ⟨⟨Subtype.val '' W.carrier, U.isOpenEmbedding'.isOpenMap W.carrier W.2⟩, ?_, ?_, hmemV⟩
  · rintro _ ⟨b, -, rfl⟩
    exact b.2
  · ext z
    exact hmemV z

/-- The cocone over the neighbourhoods of `x ∈ U` for `jpExtend X U G`, with point the stalk of
`G` at `x`. -/
private noncomputable def jpExtendStalkCocone (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) : Limits.Cocone ((OpenNhds.inclusion x).op ⋙ jpExtend X U G) where
  pt := G.stalk (⟨x, hx⟩ : subspace X U)
  ι :=
  { app := fun (W : (OpenNhds x)ᵒᵖ) =>
      TypeCat.ofHom (fun (p : JpSection X U G W.unop.1) =>
        G.germ ((Opens.map U.inclusion').obj W.unop.1) ⟨x, hx⟩ W.unop.2 p.1)
    naturality := by
      intro W W' i
      ext p
      change (CategoryTheory.ConcreteCategory.hom
              (G.germ ((Opens.map U.inclusion').obj W'.unop.1) ⟨x, hx⟩ W'.unop.2))
          (((jpExtend X U G).map ((OpenNhds.inclusion x).op.map i) p).1)
          = (CategoryTheory.ConcreteCategory.hom
              (G.germ ((Opens.map U.inclusion').obj W.unop.1) ⟨x, hx⟩ W.unop.2)) p.1
      rw [show ((jpExtend X U G).map ((OpenNhds.inclusion x).op.map i) p).1
          = (CategoryTheory.ConcreteCategory.hom (G.map
              ((Opens.map U.inclusion').map ((OpenNhds.inclusion x).map i.unop)).op)) p.1 from
                  rfl]
      exact TopCat.Presheaf.germ_res_apply G
        ((Opens.map U.inclusion').map ((OpenNhds.inclusion x).map i.unop)) ⟨x, hx⟩ W'.unop.2
        p.1 }

/-- The map from the stalk of `jpExtend X U G` at `x ∈ U` to the stalk of `G` at `x`. -/
private noncomputable def jpExtendStalkToStalk (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) : (jpExtend X U G).stalk x ⟶ G.stalk (⟨x, hx⟩ : subspace X U) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ jpExtend X U G) (jpExtendStalkCocone X U G x hx)

/-- `jpExtendStalkToStalk` sends the germ of a section to the germ of its underlying section. -/
private theorem jpExtendStalkToStalk_germ (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) (V : Opens X) (hxV : x ∈ V) (p : JpSection X U G V) :
    (CategoryTheory.ConcreteCategory.hom (jpExtendStalkToStalk X U G x hx))
      ((CategoryTheory.ConcreteCategory.hom ((jpExtend X U G).germ V x hxV)) p)
    = (CategoryTheory.ConcreteCategory.hom
        (G.germ ((Opens.map U.inclusion').obj V) ⟨x, hx⟩ hxV)) p.1 := by
  have happ := congrArg (fun (g : (jpExtend X U G).obj (op V) ⟶ G.stalk ⟨x, hx⟩) =>
    (CategoryTheory.ConcreteCategory.hom g) p)
    (colimit.ι_desc (jpExtendStalkCocone X U G x hx) (op (⟨V, hxV⟩ : OpenNhds x)))
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at happ
  exact happ

/-- `jpExtendStalkToStalk` is injective. -/
private theorem jpExtendStalkToStalk_injective (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) :
    Function.Injective (CategoryTheory.ConcreteCategory.hom (jpExtendStalkToStalk X U G x hx)) := by
  set y : subspace X U := ⟨x, hx⟩
  intro a b hab
  obtain ⟨Va, hxVa, pa, rfl⟩ := TopCat.Presheaf.exists_germ_eq (jpExtend X U G) a
  obtain ⟨Vb, hxVb, pb, rfl⟩ := TopCat.Presheaf.exists_germ_eq (jpExtend X U G) b
  rw [jpExtendStalkToStalk_germ X U G x hx Va hxVa pa,
    jpExtendStalkToStalk_germ X U G x hx Vb hxVb pb] at hab
  obtain ⟨W, hyW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq G y hxVa hxVb pa.1 pb.1 hab
  obtain ⟨V, hVU, rfl, hmem⟩ := exists_le_map_inclusion'_eq X U W
  have hxV : x ∈ V := (hmem y).mpr hyW
  have hle : ∀ {Vc : Opens X}
      (i : (Opens.map U.inclusion').obj V ⟶ (Opens.map U.inclusion').obj Vc),
      ∃ h : V ≤ Vc, (Opens.map U.inclusion').op.map (homOfLE h).op = i.op := fun {Vc} i =>
    ⟨fun a ha => leOfHom i
      (show (⟨a, hVU ha⟩ : subspace X U) ∈ (Opens.map U.inclusion').obj V from ha),
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  obtain ⟨hVa, e1⟩ := hle iU
  obtain ⟨hVb, e2⟩ := hle iV
  rw [← TopCat.Presheaf.germ_res_apply (jpExtend X U G) (homOfLE hVa) x hxV pa,
    ← TopCat.Presheaf.germ_res_apply (jpExtend X U G) (homOfLE hVb) x hxV pb]
  congr 1
  apply Subtype.ext
  change (CategoryTheory.ConcreteCategory.hom (G.map
          ((Opens.map U.inclusion').op.map (homOfLE hVa).op)) pa.1)
      = (CategoryTheory.ConcreteCategory.hom (G.map
          ((Opens.map U.inclusion').op.map (homOfLE hVb).op)) pb.1)
  rw [e1, e2]
  exact heq

/-- `jpExtendStalkToStalk` is surjective. -/
private theorem jpExtendStalkToStalk_surjective (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) :
    Function.Surjective
      (CategoryTheory.ConcreteCategory.hom (jpExtendStalkToStalk X U G x hx)) := by
  set y : subspace X U := ⟨x, hx⟩
  intro b
  obtain ⟨W, hyW, t, htb⟩ := TopCat.Presheaf.exists_germ_eq G b
  obtain ⟨V, hVU, rfl, hmem⟩ := exists_le_map_inclusion'_eq X U W
  have hxV : x ∈ V := (hmem y).mpr hyW
  exact ⟨(CategoryTheory.ConcreteCategory.hom ((jpExtend X U G).germ V x hxV)) ⟨t, hVU⟩,
    (jpExtendStalkToStalk_germ X U G x hx V hxV ⟨t, hVU⟩).trans htb⟩

/-- `jpExtendStalkToStalk` is bijective. -/
private theorem jpExtendStalkToStalk_bijective (G : TopCat.Presheaf (Type u) (subspace X U))
    (x : X) (hx : x ∈ U) :
    Function.Bijective (CategoryTheory.ConcreteCategory.hom (jpExtendStalkToStalk X U G x hx)) :=
  ⟨jpExtendStalkToStalk_injective X U G x hx, jpExtendStalkToStalk_surjective X U G x hx⟩

/-- For a sheaf `G` on the subspace `U` and a point `x ∈ U`, the stalk of `jExtend X U G` at `x`
is isomorphic to the stalk of `G` at the corresponding point of `U`. -/
theorem jExtend_stalk_of_mem
    (G : TopCat.Sheaf (Type u) (subspace X U)) (x : X) (hx : x ∈ U) :
    Nonempty ((jExtend X U G).presheaf.stalk x ≅
      G.presheaf.stalk (⟨x, hx⟩ : subspace X U)) := by
  -- SANITY CHECK PASSED (no counterexample; faithful encoding of Stacks 00A3(3), nonempty-stalk
  -- case)
  have : IsIso (jpExtendStalkToStalk X U G.presheaf x hx) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
      (jpExtendStalkToStalk_bijective X U G.presheaf x hx)
  exact ⟨(TopCat.Presheaf.sheafifyStalkIso (jpExtend X U G.presheaf) x).trans
    (asIso (jpExtendStalkToStalk X U G.presheaf x hx))⟩

/-- The map induced on stalks by the concrete sheafification unit `toSheafify` is an isomorphism.
(This is the "future work" remark in `Mathlib.Topology.Sheaves.Sheafify`: it is the inverse of
`stalkToFiber`.) -/
theorem stalkFunctor_map_toSheafify_isIso (P : TopCat.Presheaf (Type u) X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map P.toSheafify) := by
  have hcomp : CategoryTheory.CategoryStruct.comp
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map P.toSheafify) (P.stalkToFiber x) =
      CategoryTheory.CategoryStruct.id _ := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    change (CategoryTheory.ConcreteCategory.hom (P.stalkToFiber x))
        ((CategoryTheory.ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor (Type u) x).map P.toSheafify))
          ((CategoryTheory.ConcreteCategory.hom (P.germ U x hxU)) s)) =
        (CategoryTheory.ConcreteCategory.hom (P.germ U x hxU)) s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact TopCat.stalkToFiber_germ (TopCat.Presheaf.Sheafify.isLocallyGerm P) U x hxU
        (CategoryTheory.ConcreteCategory.hom (P.toSheafify.app (op U)) s)
  have hiso : IsIso (P.stalkToFiber x) := (P.sheafifyStalkIso x).isIso_hom
  exact isIso_of_comp_hom_eq_id (P.stalkToFiber x) hcomp

/-! ## Sub-lemmas for the main theorem (decomposition of Stacks 0CAH) -/

/-- The comparison map from the categorical sheafification of `P` to `P.sheafify` composes with
the categorical unit to give `P.toSheafify`. -/
private theorem toSheafify_comp_homEquiv_symm_toSheafify (P : TopCat.Presheaf (Type u) X) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
      (((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
        (Type u)).homEquiv P P.sheafify).symm P.toSheafify).hom = P.toSheafify :=
  (((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
    (Type u)).homEquiv P P.sheafify)).apply_symm_apply P.toSheafify

/-- The comparison map from the categorical sheafification of `P` to the concrete sheafification
`P.sheafify` is an isomorphism. -/
private theorem isIso_homEquiv_symm_toSheafify (P : TopCat.Presheaf (Type u) X) :
    IsIso (((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      (Type u)).homEquiv P P.sheafify).symm P.toSheafify) := by
  set J := Opens.grothendieckTopology X
  set adj := CategoryTheory.sheafificationAdjunction J (Type u)
  set θ : (CategoryTheory.presheafToSheaf J (Type u)).obj P ⟶ P.sheafify :=
    (adj.homEquiv P P.sheafify).symm P.toSheafify with hθ
  have hall : ∀ x0 : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x0).map θ.hom) := by
    intro x0
    have htri := toSheafify_comp_homEquiv_symm_toSheafify X P
    -- apply the stalk functor to the triangle
    have hst : CategoryTheory.CategoryStruct.comp
        ((TopCat.Presheaf.stalkFunctor (Type u) x0).map (CategoryTheory.toSheafify J P))
        ((TopCat.Presheaf.stalkFunctor (Type u) x0).map θ.hom) =
        (TopCat.Presheaf.stalkFunctor (Type u) x0).map P.toSheafify := by
      rw [← Functor.map_comp, htri]
    -- the unit stalk map (categorical) is iso; the concrete one is iso (helper_0cah); cancel.
    have : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x0).map (CategoryTheory.toSheafify J
        P)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x0 (Type u) P
    have : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x0).map P.toSheafify) :=
      stalkFunctor_map_toSheafify_isIso X P x0
    have : IsIso (CategoryTheory.CategoryStruct.comp
        ((TopCat.Presheaf.stalkFunctor (Type u) x0).map (CategoryTheory.toSheafify J P))
        ((TopCat.Presheaf.stalkFunctor (Type u) x0).map θ.hom)) := by
      rw [hst]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((TopCat.Presheaf.stalkFunctor (Type u) x0).map (CategoryTheory.toSheafify J P)) _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso θ

/-- A morphism of presheaves from `P` to a sheaf `F` lifts along `P.toSheafify`. -/
private theorem exists_sheafify_hom_toSheafify_comp (P : TopCat.Presheaf (Type u) X)
    (F : TopCat.Sheaf (Type u) X) (fp : P ⟶ F.presheaf) :
    ∃ ψ : P.sheafify ⟶ F, CategoryTheory.CategoryStruct.comp P.toSheafify ψ.hom = fp := by
  set J := Opens.grothendieckTopology X
  set adj := CategoryTheory.sheafificationAdjunction J (Type u)
  set θ : (CategoryTheory.presheafToSheaf J (Type u)).obj P ⟶ P.sheafify :=
    (adj.homEquiv P P.sheafify).symm P.toSheafify with hθ
  have : IsIso θ := isIso_homEquiv_symm_toSheafify X P
  set catLift : (CategoryTheory.presheafToSheaf J (Type u)).obj P ⟶ F :=
    (adj.homEquiv P F).symm fp
  have htri := toSheafify_comp_homEquiv_symm_toSheafify X P
  have hcatTri : CategoryTheory.CategoryStruct.comp
      (CategoryTheory.toSheafify J P) catLift.hom = fp := by
    have h := (adj.homEquiv P F).apply_symm_apply fp
    rw [CategoryTheory.Adjunction.homEquiv_unit] at h
    exact h
  have hθinv : CategoryTheory.CategoryStruct.comp P.toSheafify (CategoryTheory.inv θ).hom
      = CategoryTheory.toSheafify J P := by
    rw [← htri, Category.assoc]
    -- θ.hom ≫ (inv θ).hom = (θ ≫ inv θ).hom = 𝟙
    have hcancel : CategoryTheory.CategoryStruct.comp θ.hom (CategoryTheory.inv θ).hom
        = CategoryTheory.CategoryStruct.id _ := by
      simp
    rw [hcancel, Category.comp_id]
  refine ⟨CategoryTheory.inv θ ≫ catLift, ?_⟩
  calc CategoryTheory.CategoryStruct.comp P.toSheafify (CategoryTheory.inv θ ≫ catLift).hom
      = CategoryTheory.CategoryStruct.comp P.toSheafify
          (CategoryTheory.CategoryStruct.comp (CategoryTheory.inv θ).hom catLift.hom) := rfl
    _ = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp P.toSheafify (CategoryTheory.inv
              θ).hom) catLift.hom := by
        rw [← Category.assoc]
    _ = CategoryTheory.CategoryStruct.comp (CategoryTheory.toSheafify J P) catLift.hom := by
        rw [hθinv]
    _ = fp := hcatTri

/-- **Sub-lemma 1 — the `j_!` adjunction packaged as "a section produces a morphism that hits its
germ" (Stacks 00A3(2) + the constant-singleton adjunction).**

Let `F` be a sheaf of sets on `X`, `U ⊆ X` an open, `x ∈ U`, and `σ ∈ F(U)` a section.  Then
there is a morphism of sheaves `ψ : j_{U!}(constant sheaf PUnit) ⟶ F` together with a stalk
element `t` of `j_{U!}(constant sheaf PUnit)` at `x` whose image under the induced stalk map of
`ψ` is the germ `σ_x ∈ F_x`.

INFORMAL ARGUMENT.  Because `PUnit` is a singleton, a morphism out of the constant sheaf
`underline{PUnit}` on `U` to any sheaf `H` on `U` is the same as a single global... no — precisely,
`Mor_{Sh(U)}(underline{PUnit}, H)` is in natural bijection with the sections `H(U)` (the constant
singleton sheaf is the terminal-indexed free sheaf on one generator: the unit `PUnit ⟶ Γ(U,H)`,
i.e. a choice of one section of `H` over `U`).  Apply this with `H = F|_U = j_U^{-1}F`: the section
`σ ∈ F(U) = (F|_U)(U)` gives a morphism `underline{PUnit} ⟶ F|_U`.  By the `j_!`-adjunction
(Stacks 00A3(2)), `Mor_{Sh(X)}(j_{U!}underline{PUnit}, F) ≅ Mor_{Sh(U)}(underline{PUnit}, F|_U)`,
so this transposes to a morphism `ψ : j_{U!}underline{PUnit} ⟶ F`.

For the germ-hitting statement: by Stacks 00A3(3) (recorded here as `jExtend_stalk_of_mem`), at
`x ∈ U` the stalk `(j_{U!}underline{PUnit})_x ≅ (underline{PUnit})_x`, which is the singleton; let
`t` be its unique element (the germ at `x` of the generating section `* : PUnit` of the constant
sheaf).  Unwinding the adjunction (the counit `j_{U!}j_U^{-1}F ⟶ F` on stalks at `x ∈ U` is the
identity `F_x → F_x`, Stacks 00A3), the stalk map of `ψ` sends `t` to the germ at `x` of `σ`,
i.e. `σ_x`.  This is the standard "the transpose of a section restricts to that section on the
relevant stalk" computation.

FORMALIZATION HINT.  The cleanest route in Mathlib avoids reconstructing the bespoke `j_!`
adjunction from scratch: build `ψ` as the sheafification (`presheafToSheaf` / `.sheafify`
adjunction, `TopCat.Presheaf.toSheafify`) of a morphism of *presheaves* `jpExtend X U _ ⟶
F.presheaf`.
A presheaf map out of `jpExtend X U G` is determined by, for each open `V ≤ U`, a map
`G(V) → F(V)` natural in `V` — and over `V ⊆ U` one takes the composite "value in `G(V)` ↦ section
of `F` over `V`" given by restricting `σ` along `V ≤ U` (note `JpSection` over `V ⊄ U` is empty, so
nothing to define there).  Concretely `σ` restricts to `σ|_V ∈ F(V)` for every `V ≤ U`, and the
constant-`PUnit` presheaf has a canonical generator, giving the presheaf transformation; sheafify
to get `ψ`.  For the stalk element `t`, use `jExtend_stalk_of_mem` (or directly the germ at `x` of
the generator over `U`); the equation `stalkMap ψ t = σ_x` then follows by
`TopCat.Presheaf.stalkFunctor_map_germ_apply` and `germ_res_apply` chasing `σ` through the
restriction maps.  This sub-lemma is the analytic core of the construction and may itself need to
be decomposed in the formal phase. -/
theorem exists_jExtendConst_hom_germ
    (F : TopCat.Sheaf (Type u) X) (V : Opens X) (x : X) (hx : x ∈ V)
    (σ : F.presheaf.obj (op V)) :
    ∃ (ψ : jExtendConst X V PUnit.{u + 1} ⟶ F)
      (t : (jExtendConst X V PUnit.{u + 1}).presheaf.stalk x),
      (TopCat.Presheaf.stalkFunctor (Type u) x).map ψ.hom t =
        (F.presheaf.germ V x hx σ) := by
  -- SANITY CHECK PASSED (no counterexample; faithful encoding of Stacks 00A3(2)/(3))
  classical
  set G : TopCat.Presheaf (Type u) (subspace X V) := (constSheafOn X V PUnit.{u+1}).presheaf with hG
  set P : TopCat.Presheaf (Type u) X := jpExtend X V G with hP
  -- The presheaf morphism fp : P ⟶ F.presheaf, sending the generator over W ≤ V to σ|_W.
  set fp : P ⟶ F.presheaf :=
    { app := fun W => TypeCat.ofHom (fun (p : JpSection X V G W.unop) =>
        F.presheaf.map (homOfLE p.2).op σ)
      naturality := by
        intro W W' i
        ext p
        change F.presheaf.map (homOfLE _).op σ
            = (CategoryTheory.ConcreteCategory.hom (F.presheaf.map i.unop.op))
                (F.presheaf.map (homOfLE _).op σ)
        rw [← CategoryTheory.ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
        rfl } with hfp
  obtain ⟨ψ, hlift⟩ := exists_sheafify_hom_toSheafify_comp X P F fp
  -- the generator section over V of P
  have hTterm : IsTerminal (⊤ : Opens (subspace X V)) := IsTerminal.ofUnique _
  set gen0 : G.obj (op (⊤ : Opens (subspace X V))) :=
    (CategoryTheory.constantSheafAdj (Opens.grothendieckTopology (subspace X V)) (Type u)
      hTterm).unit.app PUnit.{u+1} PUnit.unit with hgen0
  set genW : G.obj (op ((Opens.map V.inclusion').obj V)) :=
    G.map (homOfLE le_top).op gen0 with hgenW
  set p₀ : JpSection X V G V := ⟨genW, le_refl V⟩ with hp₀
  -- the stalk element t = germ of (toSheafify p₀) at x
  refine ⟨ψ, P.sheafify.presheaf.germ V x hx (P.toSheafify.app (op V) p₀), ?_⟩
  -- compute the stalk map
  change (CategoryTheory.ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor (Type u) x).map ψ.hom))
      ((CategoryTheory.ConcreteCategory.hom (P.sheafify.presheaf.germ V x hx))
        (CategoryTheory.ConcreteCategory.hom (P.toSheafify.app (op V)) p₀)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  -- ψ.hom.app (op V) (toSheafify.app p₀) = fp.app (op V) p₀
  have happ : CategoryTheory.ConcreteCategory.hom (ψ.hom.app (op V))
      (CategoryTheory.ConcreteCategory.hom (P.toSheafify.app (op V)) p₀)
      = CategoryTheory.ConcreteCategory.hom (fp.app (op V)) p₀ :=
    congrArg (fun (η : P ⟶ F.presheaf) => CategoryTheory.ConcreteCategory.hom (η.app (op V)) p₀)
      hlift
  rw [happ]
  -- fp.app (op V) p₀ = F.map (homOfLE (le_refl V)).op σ ; germ of that = germ σ
  change (CategoryTheory.ConcreteCategory.hom (F.presheaf.germ V x hx))
      (CategoryTheory.ConcreteCategory.hom (F.presheaf.map (homOfLE p₀.2).op) σ) = _
  rw [TopCat.Presheaf.germ_res_apply]

/-! ## Main Statement -/

/-- **Stacks 0CAH (Lemma 17.19.1).**  Let `X` be a topological space, `B` a basis for the
topology on `X`, and `F` a sheaf of sets on `X`.  Then there is an index set `I`, a family of
basis opens `U i ∈ B`, a family of finite sets `S i`, and a *surjection* (epimorphism in
`Sh(X)`)

  `φ : ∐_i j_{U i !}(constant sheaf S i on U i) ⟶ F`

from the categorical coproduct (Def. 5) of the extensions-by-empty-set `jExtendConst X (U i) (S i)`
of the constant sheaves `constant sheaf (S i)` on `U i`.  Here `Epi φ` expresses that `φ` is a
surjection in the sense of Definition 6.

INFORMAL PROOF (Stacks 0CAH).
Take the index set `I = Σ x : X, F_x = {(x,s) : x ∈ X, s ∈ F_x}`, every `S i = PUnit` (a singleton,
hence finite).  For each `i = (x,s)`, since `B` is a basis and the stalk is a colimit over open
neighborhoods, `germ_exist_of_isBasis hB` provides a basis open `U i ∈ B` with `x ∈ U i` and a
section `σ i ∈ F(U i)` with germ `(σ i)_x = s`.  By Sub-lemma 1 (`exists_jExtendConst_hom_germ`),
the section `σ i` yields a morphism `ψ i : j_{U i !}underline{PUnit} ⟶ F` together with a stalk
element `t i` of `j_{U i !}underline{PUnit}` at `x` with `stalkMap (ψ i) (t i) = s`.  Assemble the
`ψ i` via the coproduct universal property (`Sigma.desc`) into
`φ : ∐_i j_{U i !}underline{PUnit} ⟶ F`.

For `Epi φ` we use the criterion (Def. 6): `φ` is epi iff stalkwise surjective
(`TopCat.Sheaf.isLocallySurjective_iff_epi` ∘ `locally_surjective_iff_surjective_on_stalks`).
Fix `x : X` and `s ∈ F_x`; let `i = ⟨x, s⟩`.  Since `Sigma.ι i ≫ φ = ψ i`
(`Sigma.ι_desc`), applying the stalk functor and functoriality gives
`stalkMap φ (stalkMap (Sigma.ι i) (t i)) = stalkMap (ψ i) (t i) = s`.  Hence `s` is in the image of
`stalkMap φ`, so `φ` is surjective on every stalk, therefore `Epi`. ∎ -/
@[stacks 0CAH]
theorem exists_epi_from_coproduct_jExtendConst
    (F : TopCat.Sheaf (Type u) X) (B : Set (Opens X)) (hB : Opens.IsBasis B) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u),
      (∀ i, U i ∈ B) ∧
      (∀ i, Finite (S i)) ∧
      ∃ φ : (∐ fun i => jExtendConst X (U i) (S i)) ⟶ F, Epi φ := by
  classical
  choose U hxU hUB σ hσ using fun i : (Σ x : X, F.presheaf.stalk x) =>
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB F.presheaf i.1 i.2
  choose ψ t ht using fun i => exists_jExtendConst_hom_germ X F (U i) i.1 (hxU i) (σ i)
  refine ⟨_, U, fun _ => PUnit.{u + 1}, hUB, fun _ => inferInstance, Limits.Sigma.desc ψ, ?_⟩
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi,
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x s
  refine ⟨(TopCat.Presheaf.stalkFunctor (Type u) x).map
    (Limits.Sigma.ι (fun i => jExtendConst X (U i) PUnit.{u + 1}) ⟨x, s⟩).hom (t ⟨x, s⟩), ?_⟩
  have key : (TopCat.Presheaf.stalkFunctor (Type u) x).map
        (Limits.Sigma.ι (fun i => jExtendConst X (U i) PUnit.{u + 1}) ⟨x, s⟩).hom ≫
      (TopCat.Presheaf.stalkFunctor (Type u) x).map (Limits.Sigma.desc ψ).hom =
      (TopCat.Presheaf.stalkFunctor (Type u) x).map (ψ ⟨x, s⟩).hom := by
    rw [← Functor.map_comp]
    congr 1
    change (Limits.Sigma.ι (fun i => jExtendConst X (U i) PUnit.{u + 1}) ⟨x, s⟩ ≫
        Limits.Sigma.desc ψ).hom = (ψ ⟨x, s⟩).hom
    rw [Limits.Sigma.ι_comp_desc]
  have happ := congrArg (fun (g : (jExtendConst X (U ⟨x, s⟩) PUnit.{u + 1}).presheaf.stalk x ⟶ _)
      => (CategoryTheory.ConcreteCategory.hom g) (t ⟨x, s⟩)) key
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at happ
  exact happ.trans ((ht ⟨x, s⟩).trans (hσ ⟨x, s⟩))

end Stacks.Sheaves.ConstantSheafGenerators
