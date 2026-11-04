module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing maps of sheaves of sets over an open covering (Stacks 04TN)

Let `X` be a topological space with an open covering `X = ⋃ i, U i`, and let `F` and `G` be sheaves
of sets on `X`. Given maps of sheaves `φ i : F|_{U i} ⟶ G|_{U i}` agreeing on the overlaps
`U i ∩ U j`, there is a unique map of sheaves `ψ : F ⟶ G` restricting to `φ i` on each `U i`.

The restricted sheaves `F|_{U i}` are not formed here. Instead a map of sheaves on an open `U` is
recorded directly as presheaf-level data on the opens of `X` lying below `U`: this is the structure
`LocalSheafHom`, a family of functions `F(V) → G(V)` for `V ≤ U` compatible with the restriction
maps of `F` and `G`. Under the order isomorphism between the opens of the subspace `U` and the
opens of `X` contained in `U`, this is exactly the data of a morphism `F|_U ⟶ G|_U`, and it has the
practical advantage that `U i ∩ U j` has only one incarnation — the open `U i ⊓ U j` of `X` —
rather than two (as an open of `U i` and as an open of `U j`), so the compatibility hypothesis
needs no transport. Correspondingly, compatibility is stated as: for every open `V` of `X`
contained in both `U i` and `U j`, the components of `φ i` and `φ j` at `V` agree.

The glued morphism is built section by section: for an open `V`, the family
`{V ⊓ U i}` covers `V`, the sections `(φ i) (s|_{V ⊓ U i})` are compatible on that cover, and the
sheaf condition for `G` (`TopCat.Sheaf.existsUnique_gluing'`) produces a unique section of `G` over
`V`. Naturality, the restriction property and uniqueness all reduce to the separation half of the
sheaf axiom for `G` (`TopCat.Sheaf.eq_of_locally_eq'`) on the same covers.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

/-- A *local map of sheaves* `F → G` on an open subset `U` of `X`: the presheaf-level
natural-transformation data of a family of functions `F(V) → G(V)`, one for each open `V ≤ U`,
compatible with all restriction maps.

This is equivalent to a morphism of sheaves `F|_U ⟶ G|_U` on the open subspace `U`, via the
canonical order isomorphism between the opens of the subspace `U` and the opens of `X` contained in
`U`. -/
structure LocalSheafHom {X : TopCat.{u}} (F G : TopCat.Sheaf (Type u) X)
    (U : Opens X) where
  /-- Component on an open `V ≤ U`. -/
  app : ∀ (V : Opens X), V ≤ U → F.obj.obj (op V) → G.obj.obj (op V)
  /-- Naturality with respect to the restriction maps of `F` and `G`. -/
  naturality : ∀ (V W : Opens X) (hV : V ≤ U) (hW : W ≤ U) (i : W ⟶ V)
      (s : F.obj.obj (op V)),
    G.obj.map i.op (app V hV s) = app W hW (F.obj.map i.op s)

/-- Every open `V` is covered by the opens `V ⊓ U i`, since the `U i` cover `X`. -/
private lemma cover_of_iSup_eq_top {ι : Type*} {X : TopCat.{u}} {U : ι → Opens X}
    (hU : ⨆ i, U i = ⊤) (V : Opens X) : V ≤ ⨆ i, V ⊓ U i := by
  have h : V ⊓ ⨆ i, U i = ⨆ i, V ⊓ U i := inf_iSup_eq V U
  rw [hU, inf_top_eq] at h
  exact h ▸ le_refl _

/-- Restricting a section along two different factorisations through the same open agrees. -/
private lemma map_map_eq {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ Type u) {A B B' C : Opens X}
    (g : B ⟶ A) (f : C ⟶ B) (g' : B' ⟶ A) (f' : C ⟶ B') (s : P.obj (op A)) :
    P.map f.op (P.map g.op s) = P.map f'.op (P.map g'.op s) := by
  rw [← types_comp_apply (P.map g.op) (P.map f.op) s,
    ← types_comp_apply (P.map g'.op) (P.map f'.op) s, ← P.map_comp, ← P.map_comp]
  congr 1

/-- Two sections of `G` over `V` that agree on every `V ⊓ U i` are equal. -/
private lemma eq_of_eq_inf {ι : Type*} {X : TopCat.{u}} {U : ι → Opens X}
    (hU : ⨆ i, U i = ⊤) (G : TopCat.Sheaf (Type u) X) {V : Opens X}
    {t t' : G.obj.obj (op V)}
    (h : ∀ i, G.obj.map (Opens.infLELeft V (U i)).op t =
      G.obj.map (Opens.infLELeft V (U i)).op t') :
    t = t' :=
  Sheaf.eq_of_locally_eq' G (fun i => V ⊓ U i) V (fun i => Opens.infLELeft V (U i))
    (cover_of_iSup_eq_top hU V) _ _ h

/-- The images of a section `s : F(V)` under the local maps `φ i` form a compatible family for `G`
on the cover `{V ⊓ U i}` of `V`: on `(V ⊓ U i) ⊓ (V ⊓ U j)` both are computed from `s` by a single
restriction followed by the common value of `φ i` and `φ j` there. -/
private lemma local_sections_compatible {ι : Type*} {X : TopCat.{u}}
    {U : ι → Opens X} {F G : TopCat.Sheaf (Type u) X}
    {φ : (i : ι) → LocalSheafHom F G (U i)}
    (hφ : ∀ i j (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (φ i).app V hVi = (φ j).app V hVj)
    (V : Opens X) (s : F.obj.obj (op V)) :
    Presheaf.IsCompatible G.obj (fun i => V ⊓ U i)
      (fun i => (φ i).app (V ⊓ U i) inf_le_right (F.obj.map (Opens.infLELeft V (U i)).op s)) := by
  intro i j
  dsimp only
  rw [(φ i).naturality (V ⊓ U i) ((V ⊓ U i) ⊓ (V ⊓ U j)) inf_le_right
    (inf_le_left.trans inf_le_right) (Opens.infLELeft (V ⊓ U i) (V ⊓ U j)),
    (φ j).naturality (V ⊓ U j) ((V ⊓ U i) ⊓ (V ⊓ U j)) inf_le_right
    (inf_le_right.trans inf_le_right) (Opens.infLERight (V ⊓ U i) (V ⊓ U j)),
    hφ i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)]
  congr 1
  exact map_map_eq F.obj _ _ _ _ s

/-- The sheaf condition for `G` glues the local images of a section `s : F(V)` into a unique
section of `G` over `V`. This section is the value at `s` of the morphism being constructed. -/
private lemma glue_local_sections {ι : Type*} {X : TopCat.{u}}
    {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) {F G : TopCat.Sheaf (Type u) X}
    {φ : (i : ι) → LocalSheafHom F G (U i)}
    (hφ : ∀ i j (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (φ i).app V hVi = (φ j).app V hVj)
    (V : Opens X) (s : F.obj.obj (op V)) :
    ∃! t : G.obj.obj (op V), ∀ i, G.obj.map (Opens.infLELeft V (U i)).op t =
      (φ i).app (V ⊓ U i) inf_le_right (F.obj.map (Opens.infLELeft V (U i)).op s) :=
  Sheaf.existsUnique_gluing' G (fun i => V ⊓ U i) V
    (fun i => Opens.infLELeft V (U i))
    (cover_of_iSup_eq_top hU V)
    _ (local_sections_compatible hφ V s)

/-- Any family of maps `F(V) → G(V)` characterised by the gluing property is automatically
compatible with restriction: both sides of the naturality square restrict to the same section on
each `W ⊓ U i`, so they agree by separation for `G` on the cover `{W ⊓ U i}` of `W`. -/
private lemma glued_morphism_natural {ι : Type*} {X : TopCat.{u}}
    {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) {F G : TopCat.Sheaf (Type u) X}
    {φ : (i : ι) → LocalSheafHom F G (U i)}
    (ψApp : ∀ V : Opens X, F.obj.obj (op V) → G.obj.obj (op V))
    (hψGlue : ∀ (V : Opens X) (s : F.obj.obj (op V)) (i : ι),
      G.obj.map (Opens.infLELeft V (U i)).op (ψApp V s) =
        (φ i).app (V ⊓ U i) inf_le_right (F.obj.map (Opens.infLELeft V (U i)).op s))
    (V W : Opens X) (h : W ⟶ V) (s : F.obj.obj (op V)) :
    G.obj.map h.op (ψApp V s) = ψApp W (F.obj.map h.op s) := by
  refine eq_of_eq_inf hU G fun i => ?_
  rw [hψGlue W (F.obj.map h.op s) i,
    ← types_comp_apply (G.obj.map h.op) (G.obj.map (Opens.infLELeft W (U i)).op) (ψApp V s),
    ← G.obj.map_comp]
  let k : W ⊓ U i ⟶ V ⊓ U i := homOfLE (inf_le_inf_right _ (Quiver.Hom.le h))
  have hfactor : h.op ≫ (Opens.infLELeft W (U i)).op = (Opens.infLELeft V (U i)).op ≫ k.op :=
    Subsingleton.elim _ _
  rw [hfactor, G.obj.map_comp, types_comp_apply, hψGlue V s i,
    (φ i).naturality (V ⊓ U i) (W ⊓ U i) inf_le_right inf_le_right k]
  congr 1
  exact map_map_eq F.obj _ _ _ _ s

/-- On an open `V` contained in some `U i`, the glued map agrees with `φ i`: the section
`(φ i) s` satisfies the same gluing characterisation, so uniqueness of the glued section
applies. -/
private lemma glued_morphism_restricts {ι : Type*} {X : TopCat.{u}}
    {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) {F G : TopCat.Sheaf (Type u) X}
    {φ : (i : ι) → LocalSheafHom F G (U i)}
    (hφ : ∀ i j (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (φ i).app V hVi = (φ j).app V hVj)
    (ψApp : ∀ V : Opens X, F.obj.obj (op V) → G.obj.obj (op V))
    (hψGlue : ∀ (V : Opens X) (s : F.obj.obj (op V)) (i : ι),
      G.obj.map (Opens.infLELeft V (U i)).op (ψApp V s) =
        (φ i).app (V ⊓ U i) inf_le_right (F.obj.map (Opens.infLELeft V (U i)).op s))
    (i : ι) (V : Opens X) (hV : V ≤ U i) (s : F.obj.obj (op V)) :
    ψApp V s = (φ i).app V hV s := by
  have huniq := (glue_local_sections hU hφ V s).choose_spec.2
  have hφi_glues : ∀ j, G.obj.map (Opens.infLELeft V (U j)).op ((φ i).app V hV s) =
      (φ j).app (V ⊓ U j) inf_le_right (F.obj.map (Opens.infLELeft V (U j)).op s) := by
    intro j
    rw [(φ i).naturality V (V ⊓ U j) hV (inf_le_left.trans hV) (Opens.infLELeft V (U j))]
    exact congrFun (hφ i j (V ⊓ U j) (inf_le_left.trans hV) inf_le_right) _
  exact (huniq _ (fun j => hψGlue V s j)).trans (huniq _ hφi_glues).symm

/-- Two morphisms `F ⟶ G` that both restrict to `φ i` on every `U i` are equal: on any open `V`
their values agree after restriction to each `V ⊓ U i`, so separation for `G` applies. -/
private lemma glued_morphism_unique {ι : Type*} {X : TopCat.{u}}
    {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) {F G : TopCat.Sheaf (Type u) X}
    {φ : (i : ι) → LocalSheafHom F G (U i)}
    (ψ ψ' : F ⟶ G)
    (hψ : ∀ i (V : Opens X) (hV : V ≤ U i), ψ.1.app (op V) = (φ i).app V hV)
    (hψ' : ∀ i (V : Opens X) (hV : V ≤ U i), ψ'.1.app (op V) = (φ i).app V hV) :
    ψ = ψ' := by
  apply InducedCategory.Hom.ext
  apply NatTrans.ext
  funext V
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  refine eq_of_eq_inf hU G fun i => ?_
  rw [(NatTrans.naturality_apply ψ.1 (Opens.infLELeft V.unop (U i)).op s).symm,
    (NatTrans.naturality_apply ψ'.1 (Opens.infLELeft V.unop (U i)).op s).symm,
    congrFun (hψ i (V.unop ⊓ U i) inf_le_right), congrFun (hψ' i (V.unop ⊓ U i) inf_le_right)]

/-- **Stacks 04TN.** Gluing maps of sheaves. Given an open covering `U : ι → Opens X` of a
topological space `X`, sheaves of sets `F` and `G` on `X`, and local sheaf maps `φ i` on each `U i`
agreeing on all overlaps, there is a unique morphism of sheaves `ψ : F ⟶ G` whose restriction to
each `U i` is `φ i`. -/
@[stacks 04TN]
theorem existsUnique_hom_of_localHom {ι : Type*} {X : TopCat.{u}}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (F G : TopCat.Sheaf (Type u) X)
    (φ : (i : ι) → LocalSheafHom F G (U i))
    (hφ : ∀ i j (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (φ i).app V hVi = (φ j).app V hVj) :
    ∃! ψ : F ⟶ G, ∀ i (V : Opens X) (hV : V ≤ U i),
      ψ.1.app (op V) = (φ i).app V hV := by
  have hglue := glue_local_sections hU hφ
  set ψApp : ∀ V : Opens X, F.obj.obj (op V) → G.obj.obj (op V) :=
    fun V s => (hglue V s).choose
  have hψGlue : ∀ (V : Opens X) (s : F.obj.obj (op V)) (i : ι),
      G.obj.map (Opens.infLELeft V (U i)).op (ψApp V s) =
        (φ i).app (V ⊓ U i) inf_le_right (F.obj.map (Opens.infLELeft V (U i)).op s) :=
    fun V s i => (hglue V s).choose_spec.1 i
  have hψNat : ∀ ⦃V₁ V₂ : (Opens X)ᵒᵖ⦄ (f : V₁ ⟶ V₂),
      F.obj.map f ≫ (fun W => TypeCat.ofHom (ψApp W.unop)) V₂ =
        (fun W => TypeCat.ofHom (ψApp W.unop)) V₁ ≫ G.obj.map f := by
    intro V₁ V₂ f
    ext s
    exact (glued_morphism_natural hU ψApp hψGlue V₁.unop V₂.unop f.unop s).symm
  have hrestr : ∀ i (V : Opens X) (hV : V ≤ U i),
      (⟨⟨fun W => TypeCat.ofHom (ψApp W.unop), hψNat⟩⟩ : F ⟶ G).1.app (op V) =
        (φ i).app V hV := by
    intro i V hV
    funext s
    exact glued_morphism_restricts hU hφ ψApp hψGlue i V hV s
  exact ⟨⟨⟨fun W => TypeCat.ofHom (ψApp W.unop), hψNat⟩⟩, hrestr,
    fun ψ' hψ' => glued_morphism_unique hU ψ' _ hψ' hrestr⟩

end TopCat.Sheaf
