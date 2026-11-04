module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sets.Opens
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a sheaf of sets from a basis to the whole space (Stacks 009N)

Let `X` be a topological space and let `B : Set (Opens X)` be a basis for its topology, in the
sense of Mathlib's `TopologicalSpace.Opens.IsBasis`. A presheaf of sets on `B`
(`Stacks.BasisExtension.BasisPresheaf`) assigns a type of sections to each basis open together
with restriction maps for inclusions of basis opens, subject to the identity and composition
laws; it is a sheaf on `B` (`BasisPresheaf.IsSheaf`) when every family of sections over a basis
cover of a basis open glues uniquely, compatibility being tested on the basis opens
`W ≤ Uᵢ ⊓ Uⱼ` rather than on `Uᵢ ⊓ Uⱼ` itself, which need not be a basis open. Presheaves and
sheaves on all of `Opens X` are modelled the same way by `OpensPresheaf` and
`OpensPresheaf.IsSheaf`.

This file proves both halves of 009N.

* `sheaf_extension_exists`: a sheaf `F` on `B` extends to a sheaf on `X`. The extension is built
  explicitly as `extensionPresheaf F`, whose sections over an open `U` are the compatible
  families `CompatibleFamily F U` of sections of `F` over the basis opens contained in `U`. The
  bijections `extensionPresheaf F (U) ≃ F U` for basis opens `U`, together with their
  compatibility with restriction, are `basisEquiv` and `basisEquiv_naturality`.
* `sheaf_extension_unique`: any two sheaves on `X` restricting to `F` on `B` are related by a
  *unique* isomorphism intertwining the two comparison bijections. The isomorphism is
  `comparisonIso`, glued from the basis bijections using the sheaf property of both sides, and
  the uniqueness rests on `sheaf_sections_eq_of_basis_agree`: sections of a sheaf that agree on
  every basis open contained in `U` are equal, because those basis opens cover `U`
  (`eq_iSup_basis_le`).

Together these two statements are the Stacks Project's assertion that the extension exists and
is unique up to unique isomorphism, so the tag sits on both.

## Implementation notes

Everything lives in a single universe `u`: the space, the basis and the types of sections. The
Stacks statement makes no reference to universe levels, and using one universe throughout keeps
the index type of a cover in the same universe as `X`, which is what lets a cover indexed by
basis opens below `U` be fed to the sheaf condition.

Presheaves are modelled as plain structures with `map` fields rather than as `Opensᵒᵖ ⥤ Type u`
because the sheaf condition here is the elementwise gluing statement of the source, and the
comparison isomorphisms are families of `Equiv`s; no categorical machinery is used.
-/

@[expose] public section

open TopologicalSpace

namespace Stacks.BasisExtension

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A presheaf of sets on a basis `B` of opens: an assignment of a type
to each basis element together with restriction maps, satisfying the presheaf laws. -/
@[ega "0 3.2.1" "special case"]
structure BasisPresheaf (B : Set (Opens X)) where
  /-- The set of sections over a basis open. -/
  obj : B → Type u
  /-- The restriction map for an inclusion `V ⊆ U` of basis opens. -/
  map : ∀ {U V : B}, (V : Opens X) ≤ (U : Opens X) → obj U → obj V
  /-- `ρ^U_U = id`. -/
  map_id : ∀ U : B, map (le_refl (U : Opens X)) = id
  /-- `ρ^V_W ∘ ρ^U_V = ρ^U_W`. -/
  map_comp : ∀ {U V W : B}
      (hVU : (V : Opens X) ≤ (U : Opens X))
      (hWV : (W : Opens X) ≤ (V : Opens X)),
      map (hWV.trans hVU) = map hWV ∘ map hVU

/-- The sheaf condition for a presheaf on a basis: for any basis open `U` covered
by basis opens `Uᵢ` (indexed by a type in the same universe as `X`), any family of
sections `sᵢ ∈ F(Uᵢ)` that agree on every basis open `W ⊆ Uᵢ ∩ Uⱼ` glues uniquely. -/
def BasisPresheaf.IsSheaf {B : Set (Opens X)} (F : BasisPresheaf B) :
    Prop :=
  ∀ (U : B) {ι : Type u} (Uᵢ : ι → B)
    (hcov : (U : Opens X) = ⨆ i, ((Uᵢ i : B) : Opens X))
    (s : ∀ i, F.obj (Uᵢ i))
    (hagree : ∀ (i j : ι) (W : B)
      (hWi : (W : Opens X) ≤ (Uᵢ i : Opens X))
      (hWj : (W : Opens X) ≤ (Uᵢ j : Opens X)),
      F.map hWi (s i) = F.map hWj (s j)),
    ∃! t : F.obj U, ∀ i,
      F.map (show ((Uᵢ i : B) : Opens X) ≤ (U : Opens X) by
        rw [hcov]; exact le_iSup (fun j => ((Uᵢ j : B) : Opens X)) i) t = s i

/-- A morphism of presheaves of sets on a basis is a family of maps
indexed by basis opens commuting with the restriction maps. -/
@[ega "0 3.2.3" "special case"]
structure BasisPresheaf.Hom {B : Set (Opens X)} (F G : BasisPresheaf
    B) where
  /-- Component of the morphism at each basis open. -/
  app : ∀ U : B, F.obj U → G.obj U
  /-- Naturality: commutes with the restriction maps. -/
  naturality : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)),
    G.map h ∘ app U = app V ∘ F.map h

/-- An isomorphism of presheaves on a basis: a morphism whose every component is a
bijection. -/
structure BasisPresheaf.Iso {B : Set (Opens X)} (F G : BasisPresheaf
    B) where
  /-- The underlying family of equivalences. -/
  toEquiv : ∀ U : B, F.obj U ≃ G.obj U
  /-- Naturality with respect to restriction maps. -/
  naturality : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (s : F.obj U),
    G.map h (toEquiv U s) = toEquiv V (F.map h s)

/-- A presheaf of sets on the topological space `X`: an assignment of a type to
each open subset together with restriction maps for inclusions, satisfying the
presheaf laws. -/
structure OpensPresheaf (X : Type u) [TopologicalSpace X] where
  /-- The set of sections over an open subset. -/
  obj : Opens X → Type u
  /-- The restriction map for an inclusion `V ≤ U`. -/
  map : ∀ {U V : Opens X}, V ≤ U → obj U → obj V
  /-- `ρ^U_U = id`. -/
  map_id : ∀ U : Opens X, map (le_refl U) = id
  /-- `ρ^V_W ∘ ρ^U_V = ρ^U_W`. -/
  map_comp : ∀ {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V),
    map (hWV.trans hVU) = map hWV ∘ map hVU

/-- The sheaf condition for a presheaf on `X`: for every open `U` with open
covering `U = ⋃ᵢ Uᵢ` (indexed by a type in the same universe as `X`), any
compatible family `sᵢ ∈ G(Uᵢ)` glues uniquely. -/
def OpensPresheaf.IsSheaf (G : OpensPresheaf X) : Prop :=
  ∀ (U : Opens X) {ι : Type u} (Uᵢ : ι → Opens X) (hcov : U = ⨆ i, Uᵢ i)
    (s : ∀ i, G.obj (Uᵢ i))
    (hagree : ∀ i j,
      G.map (inf_le_left : Uᵢ i ⊓ Uᵢ j ≤ Uᵢ i) (s i)
        = G.map (inf_le_right : Uᵢ i ⊓ Uᵢ j ≤ Uᵢ j) (s j)),
    ∃! t : G.obj U, ∀ i,
      G.map (show Uᵢ i ≤ U by rw [hcov]; exact le_iSup _ i) t = s i

/-- A morphism of presheaves of sets on `X`. -/
structure OpensPresheaf.Hom (G H : OpensPresheaf X) where
  /-- Component of the morphism on each open. -/
  app : ∀ U : Opens X, G.obj U → H.obj U
  /-- Naturality with respect to restrictions. -/
  naturality : ∀ {U V : Opens X} (h : V ≤ U),
    H.map h ∘ app U = app V ∘ G.map h

/-- An isomorphism of presheaves on `X`. -/
structure OpensPresheaf.Iso (G H : OpensPresheaf X) where
  /-- The underlying family of equivalences. -/
  toEquiv : ∀ U : Opens X, G.obj U ≃ H.obj U
  /-- Naturality with respect to restrictions. -/
  naturality : ∀ {U V : Opens X} (h : V ≤ U) (s : G.obj U),
    H.map h (toEquiv U s) = toEquiv V (G.map h s)

/-- The restriction of a presheaf on `X` to a basis `B`. -/
@[implicit_reducible]
def OpensPresheaf.restrictToBasis (G : OpensPresheaf X) (B : Set (Opens X)) :
    BasisPresheaf B where
  obj U := G.obj (U : Opens X)
  map h := G.map h
  map_id U := G.map_id (U : Opens X)
  map_comp h₁ h₂ := G.map_comp h₁ h₂

/-- Restricting twice along inclusions of opens is restricting along the composite. -/
private theorem OpensPresheaf.map_map (G : OpensPresheaf X) {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : G.obj U) :
    G.map hWV (G.map hVU s) = G.map (hWV.trans hVU) s :=
  (congr_fun (G.map_comp hVU hWV) s).symm

/-! ## Key helper lemmas for the existence proof -/

/-- Every open is the supremum of basis opens contained in it. -/
lemma eq_iSup_basis_le {B : Set (Opens X)} (hB : Opens.IsBasis B) (U : Opens X) :
    U = ⨆ (V : { W : B // (W : Opens X) ≤ U }), ((V.1 : B) : Opens X) := by
  apply le_antisymm
  · intro x hx
    simp only [Opens.mem_iSup]
    obtain ⟨S, ⟨⟨W, hW, rfl⟩, hxS, hSU⟩⟩ := hB.mem_nhds_iff.mp (IsOpen.mem_nhds U.isOpen hx)
    exact ⟨⟨⟨W, hW⟩, hSU⟩, hxS⟩
  · exact iSup_le (fun V => V.2)

/-- The type of compatible families of sections over basis opens contained in `U`.
An element assigns to each basis open `V ≤ U` a section in `F(V)`, compatible with
restrictions. -/
@[implicit_reducible]
def CompatibleFamily {B : Set (Opens X)} (F : BasisPresheaf B)
    (U : Opens X) : Type u :=
  { f : ∀ (V : B), ((V : Opens X) ≤ U) → F.obj V //
    ∀ (V W : B) (hV : (V : Opens X) ≤ U) (hW : (W : Opens X) ≤ U)
      (hVW : (V : Opens X) ≤ (W : Opens X)),
      F.map hVW (f W hW) = f V hV }

/-- Restriction of compatible families: given `V ≤ U`, restrict a compatible family
from `U` to `V` by composing the containment proofs. -/
def CompatibleFamily.restrict {B : Set (Opens X)} (F : BasisPresheaf B)
    {U V : Opens X} (hVU : V ≤ U) (fam : CompatibleFamily F U) :
    CompatibleFamily F V :=
  ⟨fun W hW => fam.val W (hW.trans hVU), fun V' W' hV' hW' hV'W' =>
    fam.property V' W' (hV'.trans hVU) (hW'.trans hVU) hV'W'⟩

/-- The restriction of a compatible family from `U` to `V` takes the value of the original
family at each basis open `W ≤ V`. -/
@[simp]
lemma CompatibleFamily.restrict_val {B : Set (Opens X)} (F : BasisPresheaf B)
    {U V : Opens X} (hVU : V ≤ U) (fam : CompatibleFamily F U) (W : B)
    (hW : (W : Opens X) ≤ V) :
    (CompatibleFamily.restrict F hVU fam).val W hW = fam.val W (hW.trans hVU) :=
  rfl

/-- Restriction of compatible families along `le_refl` is the identity. -/
lemma CompatibleFamily.restrict_id {B : Set (Opens X)} (F :
    BasisPresheaf B)
    (U : Opens X) (fam : CompatibleFamily F U) :
    CompatibleFamily.restrict F (le_refl U) fam = fam :=
  Subtype.ext rfl

/-- Restriction of compatible families composes. -/
lemma CompatibleFamily.restrict_comp {B : Set (Opens X)} (F :
    BasisPresheaf B)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (fam : CompatibleFamily F U) :
    CompatibleFamily.restrict F (hWV.trans hVU) fam =
      CompatibleFamily.restrict F hWV (CompatibleFamily.restrict F hVU
          fam) :=
  Subtype.ext rfl

/-- The extension presheaf: a presheaf on `X` whose sections over `U` are
compatible families over basis opens in `U`. -/
@[implicit_reducible]
def extensionPresheaf {B : Set (Opens X)}
    (F : BasisPresheaf B) : OpensPresheaf X where
  obj U := CompatibleFamily F U
  map {_ _} hVU s := CompatibleFamily.restrict F hVU s
  map_id U := funext (CompatibleFamily.restrict_id F U)
  map_comp {_ _ _} hVU hWV := funext (CompatibleFamily.restrict_comp F hVU hWV)

/-- The restriction map of the extension presheaf along `V ≤ U` is restriction of compatible
families. -/
lemma extensionPresheaf_map {B : Set (Opens X)} (F : BasisPresheaf B) {U V : Opens X}
    (h : V ≤ U) (s : (extensionPresheaf F).obj U) :
    (extensionPresheaf F).map h s = CompatibleFamily.restrict F h s :=
  rfl

/-- The extension presheaf is a sheaf. -/
lemma extensionPresheaf_isSheaf {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B) (hF : F.IsSheaf) :
    (extensionPresheaf F).IsSheaf := by
  intro U ι Uᵢ hcov s hagree
  -- The sections `s i : Fext.obj (Uᵢ i)` are already compatible families on `Uᵢ i`.
  let sᵢ (i : ι) : CompatibleFamily F (Uᵢ i) := s i
  -- Pointwise compatibility of sections
  have hagree' : ∀ (i j : ι) (W : B) (hWi : (W : Opens X) ≤ Uᵢ i) (hWj : (W : Opens X) ≤ Uᵢ j),
      (sᵢ i).val W hWi = (sᵢ j).val W hWj := by
    intro i j W hWi hWj
    have key := congr_fun (congr_fun (congr_arg Subtype.val (hagree i j)) W) (le_inf hWi hWj)
    rw [extensionPresheaf_map, extensionPresheaf_map, CompatibleFamily.restrict_val,
      CompatibleFamily.restrict_val] at key
    convert key using 2
  -- Index type for cover of basis V ≤ U
  let CIdx (V : B) := { W : B // (W : Opens X) ≤ (V : Opens X) ∧ ∃ i, (W : Opens X) ≤ Uᵢ i }
  -- Cover V by basis opens in CIdx V
  have cover_V : ∀ (V : B) (hV : (V : Opens X) ≤ U),
      (V : Opens X) = ⨆ (p : CIdx V), ((p.1 : B) : Opens X) := by
    intro V hV
    apply le_antisymm
    · intro x hx
      simp only [Opens.mem_iSup]
      have hxU : x ∈ (⨆ i, Uᵢ i : Opens X) := hcov ▸ (hV hx)
      rw [Opens.mem_iSup] at hxU
      obtain ⟨i, hxi⟩ := hxU
      obtain ⟨S, ⟨⟨W, hWB, rfl⟩, hxW, hWint⟩⟩ :=
        hB.mem_nhds_iff.mp (IsOpen.mem_nhds ((V : Opens X) ⊓ Uᵢ i).isOpen ⟨hx, hxi⟩)
      exact ⟨⟨⟨W, hWB⟩, ⟨hWint.trans inf_le_left, ⟨i, hWint.trans inf_le_right⟩⟩⟩, hxW⟩
    · exact iSup_le (fun p => p.2.1)
  -- Over each basis `V ≤ U`, the `sᵢ` glue (choosing for each `W ∈ CIdx V` an `i` with
  -- `W ≤ Uᵢ i`) to a unique section `t_V`
  have hglue (V : B) (hV : (V : Opens X) ≤ U) :
      ∃! t : F.obj V, ∀ (W : B) (hWV : (W : Opens X) ≤ V) (i : ι) (hWi : (W : Opens X) ≤ Uᵢ i),
        F.map hWV t = (sᵢ i).val W hWi := by
    obtain ⟨t, ht, huniq⟩ := hF V (fun p : CIdx V => p.1) (cover_V V hV)
      (fun p => (sᵢ p.2.2.choose).val p.1 p.2.2.choose_spec) fun p q Z hZp hZq =>
        ((sᵢ p.2.2.choose).property Z p.1 (hZp.trans p.2.2.choose_spec) _ hZp).trans <|
          (hagree' _ _ Z (hZp.trans p.2.2.choose_spec) (hZq.trans q.2.2.choose_spec)).trans
            ((sᵢ q.2.2.choose).property Z q.1 (hZq.trans q.2.2.choose_spec) _ hZq).symm
    exact ⟨t, fun W hWV i hWi => (ht ⟨W, hWV, i, hWi⟩).trans (hagree' _ i W _ hWi),
      fun t' ht' => huniq t' fun p => ht' p.1 p.2.1 p.2.2.choose p.2.2.choose_spec⟩
  -- The `t_V` form a compatible family, which restricts to each `sᵢ` and is unique
  let t : CompatibleFamily F U := ⟨fun V hV => (hglue V hV).choose,
    fun V W hV hW hVW => (hglue V hV).choose_spec.2 _ fun Z hZV i hZi => by
      rw [← Function.comp_apply (f := F.map hZV), ← F.map_comp hVW hZV]
      exact (hglue W hW).choose_spec.1 Z _ i hZi⟩
  refine ⟨t, fun i => Subtype.ext <| funext fun W => funext fun hW => ?_,
    fun t' ht' => Subtype.ext <| funext fun V => funext fun hV =>
      (hglue V hV).choose_spec.2 _ fun W hWV i hWi => ?_⟩
  · have key := (hglue W (hW.trans ((le_iSup Uᵢ i).trans hcov.ge))).choose_spec.1 W
      (le_refl _) i hW
    rw [F.map_id W, id_eq] at key
    exact key
  · let t'_fam : CompatibleFamily F U := t'
    exact (t'_fam.property W V (hWV.trans hV) hV hWV).trans
      (congr_fun (congr_fun (congr_arg Subtype.val (ht' i)) W) hWi)

/-- The basis isomorphism: for each `U ∈ B`, `Fext(U) ≃ F(U)`. -/
@[simps apply]
def basisEquiv {B : Set (Opens X)}
    (F : BasisPresheaf B) (U : B) :
    (extensionPresheaf F).obj (U : Opens X) ≃ F.obj U where
  toFun := fun fam => fam.val U (le_refl _)
  invFun := fun s => ⟨fun V hV => F.map hV s, fun V W hV hW hVW => by
    dsimp only
    rw [← Function.comp_apply (f := F.map hVW), ← F.map_comp hW hVW]⟩
  left_inv := fun fam => Subtype.ext <| funext fun V => funext fun hV =>
    fam.property V U hV (le_refl _) hV
  right_inv := fun s => congr_fun (F.map_id U) s

/-- Naturality of the basis isomorphism with respect to basis restrictions. -/
lemma basisEquiv_naturality {B : Set (Opens X)}
    (F : BasisPresheaf B)
    {U V : B} (h : (V : Opens X) ≤ (U : Opens X))
    (s : (extensionPresheaf F).obj (U : Opens X)) :
    F.map h (basisEquiv F U s) =
      basisEquiv F V ((extensionPresheaf F).map h s) := by
  rw [basisEquiv_apply, basisEquiv_apply, extensionPresheaf_map, CompatibleFamily.restrict_val]
  exact s.property V U h (le_refl _) h

/-! ## Existence theorem -/

/-- **Stacks 009N.** *Existence.* Given a sheaf `F` of sets on a basis `B`, there exists a sheaf
`Fext` of sets on `X` together with bijections `Fext(U) ≃ F(U)` for `U ∈ B`, compatible with the
restriction maps.

Uniqueness of the extension is `sheaf_extension_unique`. -/
@[stacks 009N]
theorem sheaf_extension_exists {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B) (hF : F.IsSheaf) :
    ∃ (Fext : OpensPresheaf X) (_ : Fext.IsSheaf),
      Nonempty (BasisPresheaf.Iso (Fext.restrictToBasis B) F) :=
  ⟨extensionPresheaf F, extensionPresheaf_isSheaf hB F hF,
    ⟨{ toEquiv := fun U => basisEquiv F U
       naturality := fun h s => basisEquiv_naturality F h s }⟩⟩

/-! ## Key helper lemmas for the uniqueness proof -/

/-- Two sections of a sheaf that agree on a basis cover of `U` are equal. -/
lemma sheaf_sections_eq_of_basis_agree {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (U : Opens X) (t₁ t₂ : G.obj U)
    (heq : ∀ (V : { W : B // (W : Opens X) ≤ U }), G.map V.2 t₁ = G.map V.2 t₂) :
    t₁ = t₂ := by
  obtain ⟨_, _, huniq⟩ := hG U (fun V : { W : B // (W : Opens X) ≤ U } => ((V.1 : B) : Opens X))
    (eq_iSup_basis_le hB U) (fun V => G.map V.2 t₁) (fun i j => by
      rw [OpensPresheaf.map_map, OpensPresheaf.map_map])
  exact (huniq t₁ (fun _ => rfl)).trans (huniq t₂ (fun V => (heq V).symm)).symm

/-- Given two sheaf extensions `Fext` and `G` with basis isomorphisms to `F`,
construct the comparison isomorphism `Φ : Fext ≃ G` using sheaf gluing. -/
noncomputable def comparisonIso {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B)
    (Fext : OpensPresheaf X) (hFext : Fext.IsSheaf)
    (ι : BasisPresheaf.Iso (Fext.restrictToBasis B) F)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (ι' : BasisPresheaf.Iso (G.restrictToBasis B) F) :
    OpensPresheaf.Iso Fext G := by
  have ι'_inv_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (x : F.obj U),
      G.map h ((ι'.toEquiv U).symm x) = (ι'.toEquiv V).symm (F.map h x) := by
    intro U V h x
    apply (ι'.toEquiv V).injective
    rw [Equiv.apply_symm_apply]
    have nat := ι'.naturality h ((ι'.toEquiv U).symm x)
    conv at nat => lhs; rw [Equiv.apply_symm_apply]
    exact nat.symm
  have ι_inv_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (x : F.obj U),
      Fext.map h ((ι.toEquiv U).symm x) = (ι.toEquiv V).symm (F.map h x) := by
    intro U V h x
    apply (ι.toEquiv V).injective
    rw [Equiv.apply_symm_apply]
    have nat := ι.naturality h ((ι.toEquiv U).symm x)
    conv at nat => lhs; rw [Equiv.apply_symm_apply]
    exact nat.symm
  have ι_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (s : Fext.obj (U : Opens X)),
      F.map h (ι.toEquiv U s) = ι.toEquiv V (Fext.map h s) :=
    fun h s => ι.naturality h s
  have ι'_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (s : G.obj (U : Opens X)),
      F.map h (ι'.toEquiv U s) = ι'.toEquiv V (G.map h s) :=
    fun h s => ι'.naturality h s
  let gV (U : Opens X) (s : Fext.obj U) (V : { W : B // (W : Opens X) ≤ U }) :
      G.obj ((V.1 : B) : Opens X) :=
    (ι'.toEquiv V.1).symm (ι.toEquiv V.1 (Fext.map V.2 s))
  have gV_compat : ∀ (U : Opens X) (s : Fext.obj U)
      (i j : { W : B // (W : Opens X) ≤ U }),
      G.map (inf_le_left : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _) (gV U s i) =
      G.map (inf_le_right : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _) (gV U s j) := by
    intro U s ⟨Vi, hVi⟩ ⟨Vj, hVj⟩
    simp only [gV]
    apply sheaf_sections_eq_of_basis_agree hB G hG ((Vi : Opens X) ⊓ (Vj : Opens X))
    intro ⟨W, hW⟩
    have hWVi : (W : Opens X) ≤ (Vi : Opens X) := hW.trans inf_le_left
    have hWVj : (W : Opens X) ≤ (Vj : Opens X) := hW.trans inf_le_right
    rw [← Function.comp_apply (f := G.map hW) (g := G.map inf_le_left),
        ← G.map_comp (hVU := inf_le_left) (hWV := hW)]
    rw [← Function.comp_apply (f := G.map hW) (g := G.map inf_le_right),
        ← G.map_comp (hVU := inf_le_right) (hWV := hW)]
    rw [ι'_inv_nat hWVi _, ι'_inv_nat hWVj _]
    congr 1
    rw [ι_nat hWVi (Fext.map hVi s), ι_nat hWVj (Fext.map hVj s)]
    congr 1
    rw [← Function.comp_apply (f := Fext.map hWVi), ← Fext.map_comp hVi hWVi]
    rw [← Function.comp_apply (f := Fext.map hWVj), ← Fext.map_comp hVj hWVj]
  let fV (U : Opens X) (t : G.obj U) (V : { W : B // (W : Opens X) ≤ U }) :
      Fext.obj ((V.1 : B) : Opens X) :=
    (ι.toEquiv V.1).symm (ι'.toEquiv V.1 (G.map V.2 t))
  have fV_compat : ∀ (U : Opens X) (t : G.obj U)
      (i j : { W : B // (W : Opens X) ≤ U }),
      Fext.map (inf_le_left : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _) (fV U t i) =
      Fext.map (inf_le_right : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _) (fV U t j) := by
    intro U t ⟨Vi, hVi⟩ ⟨Vj, hVj⟩
    simp only [fV]
    apply sheaf_sections_eq_of_basis_agree hB Fext hFext ((Vi : Opens X) ⊓ (Vj : Opens X))
    intro ⟨W, hW⟩
    have hWVi : (W : Opens X) ≤ (Vi : Opens X) := hW.trans inf_le_left
    have hWVj : (W : Opens X) ≤ (Vj : Opens X) := hW.trans inf_le_right
    rw [← Function.comp_apply (f := Fext.map hW) (g := Fext.map inf_le_left),
        ← Fext.map_comp (hVU := inf_le_left) (hWV := hW)]
    rw [← Function.comp_apply (f := Fext.map hW) (g := Fext.map inf_le_right),
        ← Fext.map_comp (hVU := inf_le_right) (hWV := hW)]
    rw [ι_inv_nat hWVi _, ι_inv_nat hWVj _]
    congr 1
    rw [ι'_nat hWVi (G.map hVi t), ι'_nat hWVj (G.map hVj t)]
    congr 1
    rw [← Function.comp_apply (f := G.map hWVi), ← G.map_comp hVi hWVi]
    rw [← Function.comp_apply (f := G.map hWVj), ← G.map_comp hVj hWVj]
  let Φ (U : Opens X) (s : Fext.obj U) : G.obj U :=
    (hG U _ (eq_iSup_basis_le hB U) (gV U s) (gV_compat U s)).choose
  have Φ_spec : ∀ (U : Opens X) (s : Fext.obj U) (V : { W : B // (W : Opens X) ≤ U }),
      G.map V.2 (Φ U s) = gV U s V :=
    fun U s V => (hG U _ (eq_iSup_basis_le hB U) (gV U s) (gV_compat U s)).choose_spec.1 V
  let Ψ (U : Opens X) (t : G.obj U) : Fext.obj U :=
    (hFext U _ (eq_iSup_basis_le hB U) (fV U t) (fV_compat U t)).choose
  have Ψ_spec : ∀ (U : Opens X) (t : G.obj U) (V : { W : B // (W : Opens X) ≤ U }),
      Fext.map V.2 (Ψ U t) = fV U t V :=
    fun U t V => (hFext U _ (eq_iSup_basis_le hB U) (fV U t) (fV_compat U t)).choose_spec.1 V
  exact {
    toEquiv := fun U => {
      toFun := Φ U
      invFun := Ψ U
      left_inv := by
        intro s
        apply sheaf_sections_eq_of_basis_agree hB Fext hFext U
        intro ⟨V, hVU⟩
        rw [Ψ_spec U (Φ U s) ⟨V, hVU⟩]
        simp only [fV]
        rw [Φ_spec U s ⟨V, hVU⟩]
        simp only [gV]
        simp [Equiv.symm_apply_apply]
      right_inv := by
        intro t
        apply sheaf_sections_eq_of_basis_agree hB G hG U
        intro ⟨V, hVU⟩
        rw [Φ_spec U (Ψ U t) ⟨V, hVU⟩]
        simp only [gV]
        rw [Ψ_spec U t ⟨V, hVU⟩]
        simp only [fV]
        simp [Equiv.symm_apply_apply]
    }
    naturality := by
      intro U V hVU s
      apply sheaf_sections_eq_of_basis_agree hB G hG V
      intro ⟨W, hWV⟩
      rw [Equiv.coe_fn_mk, Equiv.coe_fn_mk,
        ← Function.comp_apply (f := G.map hWV) (g := G.map hVU), ← G.map_comp hVU hWV,
        Φ_spec U s ⟨W, hWV.trans hVU⟩, Φ_spec V (Fext.map hVU s) ⟨W, hWV⟩]
      simp only [gV]
      congr 1
      congr 1
      rw [← Function.comp_apply (f := Fext.map hWV), ← Fext.map_comp hVU hWV]
  }

/-- Specification of the comparison isomorphism on basis-cover restrictions. -/
lemma comparisonIso_spec {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B)
    (Fext : OpensPresheaf X) (hFext : Fext.IsSheaf)
    (ι : BasisPresheaf.Iso (Fext.restrictToBasis B) F)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (ι' : BasisPresheaf.Iso (G.restrictToBasis B) F)
    (U : Opens X) (s : Fext.obj U) (V : { W : B // (W : Opens X) ≤ U }) :
    G.map V.2 ((comparisonIso hB F Fext hFext ι G hG ι').toEquiv U s) =
      (ι'.toEquiv V.1).symm (ι.toEquiv V.1 (Fext.map V.2 s)) := by
  delta comparisonIso
  have hagree : ∀ (i j : { W : B // (W : Opens X) ≤ U }),
      G.map (inf_le_left : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _)
        ((ι'.toEquiv i.1).symm (ι.toEquiv i.1 (Fext.map i.2 s))) =
      G.map (inf_le_right : ((i.1 : B) : Opens X) ⊓ ((j.1 : B) : Opens X) ≤ _)
        ((ι'.toEquiv j.1).symm (ι.toEquiv j.1 (Fext.map j.2 s))) := by
    intro ⟨Vi, hVi⟩ ⟨Vj, hVj⟩
    apply sheaf_sections_eq_of_basis_agree hB G hG ((Vi : Opens X) ⊓ (Vj : Opens X))
    intro ⟨W, hW⟩
    have hWVi : (W : Opens X) ≤ (Vi : Opens X) := hW.trans inf_le_left
    have hWVj : (W : Opens X) ≤ (Vj : Opens X) := hW.trans inf_le_right
    rw [OpensPresheaf.map_map, OpensPresheaf.map_map]
    have ι'_inv_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (x : F.obj U),
        G.map h ((ι'.toEquiv U).symm x) = (ι'.toEquiv V).symm (F.map h x) := by
      intro U V h x
      apply (ι'.toEquiv V).injective
      rw [Equiv.apply_symm_apply]
      have nat := ι'.naturality h ((ι'.toEquiv U).symm x)
      conv at nat => lhs; rw [Equiv.apply_symm_apply]
      exact nat.symm
    rw [ι'_inv_nat hWVi _, ι'_inv_nat hWVj _]
    congr 1
    have ι_nat : ∀ {U V : B} (h : (V : Opens X) ≤ (U : Opens X)) (t : Fext.obj (U : Opens X)),
        F.map h (ι.toEquiv U t) = ι.toEquiv V (Fext.map h t) :=
      fun h t => ι.naturality h t
    rw [ι_nat hWVi (Fext.map hVi s), ι_nat hWVj (Fext.map hVj s)]
    congr 1
    rw [OpensPresheaf.map_map, OpensPresheaf.map_map]
  exact (hG U
    (fun V : { W : B // (W : Opens X) ≤ U } => ((V.1 : B) : Opens X))
    (eq_iSup_basis_le hB U)
    (fun V => (ι'.toEquiv V.1).symm (ι.toEquiv V.1 (Fext.map V.2 s)))
    hagree).choose_spec.1 V

/-- The comparison isomorphism satisfies the intertwining condition. -/
lemma comparisonIso_intertwines {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B)
    (Fext : OpensPresheaf X) (hFext : Fext.IsSheaf)
    (ι : BasisPresheaf.Iso (Fext.restrictToBasis B) F)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (ι' : BasisPresheaf.Iso (G.restrictToBasis B) F) :
    ∀ (U : B) (s : Fext.obj (U : Opens X)),
      ι'.toEquiv U ((comparisonIso hB F Fext hFext ι G hG ι').toEquiv (U : Opens X) s) =
        ι.toEquiv U s := by
  intro U s
  have key := comparisonIso_spec hB F Fext hFext ι G hG ι' (U : Opens X) s ⟨U, le_refl _⟩
  rw [congr_fun (G.map_id (U : Opens X)) _, congr_fun (Fext.map_id (U : Opens X)) _] at key
  simp only [id_eq] at key
  rw [key, Equiv.apply_symm_apply]

/-- Any isomorphism satisfying the intertwining condition equals the comparison iso. -/
lemma comparisonIso_unique {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B)
    (Fext : OpensPresheaf X) (hFext : Fext.IsSheaf)
    (ι : BasisPresheaf.Iso (Fext.restrictToBasis B) F)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (ι' : BasisPresheaf.Iso (G.restrictToBasis B) F)
    (Φ : OpensPresheaf.Iso Fext G)
    (hΦ : ∀ (U : B) (s : Fext.obj (U : Opens X)),
      ι'.toEquiv U (Φ.toEquiv (U : Opens X) s) = ι.toEquiv U s) :
    Φ = comparisonIso hB F Fext hFext ι G hG ι' := by
  have h : ∀ (U : Opens X) (s : Fext.obj U),
      Φ.toEquiv U s = (comparisonIso hB F Fext hFext ι G hG ι').toEquiv U s := by
    intro U s
    apply sheaf_sections_eq_of_basis_agree hB G hG U
    intro ⟨V, hVU⟩
    rw [Φ.naturality hVU s, (comparisonIso hB F Fext hFext ι G hG ι').naturality hVU s]
    exact (ι'.toEquiv V).injective ((hΦ V (Fext.map hVU s)).trans
      (comparisonIso_intertwines hB F Fext hFext ι G hG ι' V (Fext.map hVU s)).symm)
  cases Φ with | mk te nat =>
  congr 1
  ext U s
  exact h U s

/-! ## Uniqueness theorem -/

/-- **Stacks 009N.** *Uniqueness.* Any two sheaves on `X` extending the same sheaf `F` on the
basis `B` are isomorphic by a unique isomorphism intertwining the comparison bijections.

Existence of an extension is `sheaf_extension_exists`. -/
@[stacks 009N]
theorem sheaf_extension_unique {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (F : BasisPresheaf B)
    (Fext : OpensPresheaf X) (hFext : Fext.IsSheaf)
    (ι : BasisPresheaf.Iso (Fext.restrictToBasis B) F)
    (G : OpensPresheaf X) (hG : G.IsSheaf)
    (ι' : BasisPresheaf.Iso (G.restrictToBasis B) F) :
    ∃! Φ : OpensPresheaf.Iso Fext G,
      ∀ (U : B) (s : Fext.obj (U : Opens X)),
        ι'.toEquiv U (Φ.toEquiv (U : Opens X) s) = ι.toEquiv U s :=
  ⟨comparisonIso hB F Fext hFext ι G hG ι', comparisonIso_intertwines hB F Fext hFext ι G hG ι',
    comparisonIso_unique hB F Fext hFext ι G hG ι'⟩

end Stacks.BasisExtension
