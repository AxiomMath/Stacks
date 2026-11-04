module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel

/-!
# A morphism out of a subsheaf, prescribed only on a locally generating family of sections

Let `X` be a scheme, let `F` and `G` be `𝒪_X`-modules and let `P` be a submodule sheaf of `F`.
Suppose given, over every open `V` of `X`, a submodule `D V` of `Γ(F, V)` contained in
`Γ(P, V)`, stable under restriction, together with a map `μ_V : D V → Γ(G, V)` which is additive,
`Γ(X, V)`-linear and compatible with restriction. Suppose moreover that every section of `P` is
*locally* in `D`. Then `μ` comes from a unique morphism of `𝒪_X`-modules `P ⟶ G`.

This is the glueing step that a morphism out of an ideal-power subsheaf needs. The subsheaf
`I ^ k F` of [Stacks, Tag 0EH6] is the least subsheaf containing the products `g · m` over every
affine open, so a section of it is only *locally* such a product
(`Stacks.Algebraization.mem_idealPowerMultiple_iff`); a formula prescribing the values of a
morphism on those products therefore determines the morphism, but does not define it. The values
have to be glued first, and that is what happens here: the value on a section `s` over `V` is
the unique section of `G` over `V` restricting to `μ_W (s|_W)` on every open `W ≤ V` with
`s|_W ∈ D W`, and `G` is a sheaf, so there is one.

## Main definitions

* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData` — the data above.
* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.SpanOpens` — the opens on which a given section is
  in `D`; these cover the section's domain, and they are the cover the glueing is performed on.
* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.gluedValue` — the glued value.
* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.gluedHom` — the glued morphism.

## Main results

* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.gluedHom_app_of_mem` — the glued morphism
  takes the prescribed value on a section of `D`.
* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.hom_ext` — a morphism out of `P` is
  determined by its values on the prescribed sections.
* `Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.existsUnique_hom` — the two together:
  there is exactly one morphism `P ⟶ G` with the prescribed values.

## Implementation notes

`μ` is given in the "function with a membership proof" form `μ V s hs` rather than as a linear
map on the submodule `D V`. Proof irrelevance is definitional in Lean, so `μ V s hs` and
`μ V s hs'` are definitionally equal, and two values `μ V s hs`, `μ V t ht` with `s = t` agree by
`Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.μ_congr`. That is how the compatibility on an
intersection `W ⊓ W'` of two witnessing opens, each of which supplies its own proof, is closed
once the restriction maps have been composed.

The index type of the glueing is `SpanOpens D V s`, a subtype of `{W : X.Opens // W ≤ V}`; it
lands in `Type u`, the universe of the scheme, which is what
`TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf` asks of a cover. The containment proof is
carried as a component of the index rather than extracted from an existential, so no choice is
used to see it.

Only the sheaf condition of the *target* `G` is used, through
`TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf` and
`TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`; `P` enters only through its sections and
through the locality hypothesis.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules.Submodule (asModules)

universe u

namespace Stacks.AlgebraicGeometry.SubmoduleHomGlue

variable {X : Scheme.{u}} {F G : X.Modules}

/-! ### Restriction, composed -/

/-- Restricting twice is restricting once, in the `AlgebraicGeometry.Scheme.Modules.presheaf`
spelling. -/
public lemma presheaf_map_map {M : X.Modules} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op s) =
      M.presheaf.map (homOfLE (h2.trans h1)).op s :=
  (M.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm.trans
    (M.val.congr_map_apply (Subsingleton.elim _ _) s)

/-- Restriction along the identity containment does nothing. -/
public lemma presheaf_map_self {M : X.Modules} {V : X.Opens} (h : V ≤ V) (s : Γ(M, V)) :
    M.presheaf.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op V) from Subsingleton.elim _ _, M.presheaf.map_id]
  rfl

/-! ### The data -/

/-- **A morphism out of a submodule sheaf, prescribed on a locally generating family.**

The submodules `D V` of the sections of `F` are contained in those of `P` and stable under
restriction; `μ` assigns a section of `G` to each member of each `D V`, additively,
`Γ(X, V)`-linearly and compatibly with restriction; and every section of `P` lies in `D` near
every point of its domain. -/
public structure LocalData (F G : X.Modules) (P : F.Submodule) where
  /-- The submodule of sections on which the morphism is prescribed. -/
  D : ∀ V : X.Opens, Submodule Γ(X, V) Γ(F, V)
  /-- The prescription happens inside `P`. -/
  le_P : ∀ (V : X.Opens) {s : Γ(F, V)}, s ∈ D V → s ∈ P.toSubmodule.obj (op V)
  /-- The family is stable under restriction. -/
  map_mem : ∀ {V W : X.Opens} (h : W ≤ V) {s : Γ(F, V)}, s ∈ D V →
    F.presheaf.map (homOfLE h).op s ∈ D W
  /-- The prescribed value. -/
  μ : ∀ (V : X.Opens) (s : Γ(F, V)), s ∈ D V → Γ(G, V)
  /-- The prescription is additive. -/
  μ_add : ∀ (V : X.Opens) (s t : Γ(F, V)) (hs : s ∈ D V) (ht : t ∈ D V),
    μ V (s + t) (Submodule.add_mem _ hs ht) = μ V s hs + μ V t ht
  /-- The prescription is `Γ(X, V)`-linear. -/
  μ_smul : ∀ (V : X.Opens) (r : Γ(X, V)) (s : Γ(F, V)) (hs : s ∈ D V),
    μ V (r • s) (Submodule.smul_mem _ r hs) = r • μ V s hs
  /-- The prescription is compatible with restriction. -/
  μ_map : ∀ {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V)) (hs : s ∈ D V),
    μ W (F.presheaf.map (homOfLE h).op s) (map_mem h hs) =
      G.presheaf.map (homOfLE h).op (μ V s hs)
  /-- Every section of `P` lies in `D` near every point of its domain. -/
  loc : ∀ (V : X.Opens) (s : Γ(F, V)), s ∈ P.toSubmodule.obj (op V) → ∀ x ∈ V,
    ∃ W : X.Opens, ∃ h : W ≤ V, x ∈ W ∧ F.presheaf.map (homOfLE h).op s ∈ D W

/-- The opens inside `V` on which the section `s` lies in the prescribed family. These are the
members of the cover over which the value of the glued morphism on `s` is assembled. -/
public def SpanOpens (D : ∀ V : X.Opens, Submodule Γ(X, V) Γ(F, V)) (V : X.Opens)
    (s : Γ(F, V)) : Type u :=
  { W : { W : X.Opens // W ≤ V } // F.presheaf.map (homOfLE W.2).op s ∈ D W.1 }

namespace LocalData

variable {P : F.Submodule} (E : LocalData F G P)

/-- The prescribed value depends on the section, not on the proof that it is prescribed. -/
public lemma μ_congr {V : X.Opens} {s t : Γ(F, V)} (hs : s ∈ E.D V) (ht : t ∈ E.D V)
    (h : s = t) : E.μ V s hs = E.μ V t ht := by
  subst h
  rfl

/-- The open underlying a member of `Stacks.AlgebraicGeometry.SubmoduleHomGlue.SpanOpens`. -/
public abbrev spanOpen {V : X.Opens} {s : Γ(F, V)} (W : SpanOpens E.D V s) : X.Opens := W.1.1

/-- A section of `P` lies in `D` on a family of opens covering its domain. -/
public lemma le_iSup_spanOpens {V : X.Opens} {s : Γ(F, V)}
    (hs : s ∈ P.toSubmodule.obj (op V)) :
    V ≤ ⨆ W : SpanOpens E.D V s, E.spanOpen W := by
  intro x hx
  obtain ⟨W, h, hxW, hmem⟩ := E.loc V s hs x hx
  exact Opens.mem_iSup.2 ⟨⟨⟨W, h⟩, hmem⟩, hxW⟩

/-- The restriction of a section to a smaller open inside a witnessing open is again in `D`, and
the restricted section is the restriction from the original domain. -/
public lemma map_mem_of_le {V : X.Opens} {s : Γ(F, V)} (W : SpanOpens E.D V s) {Z : X.Opens}
    (hZ : Z ≤ E.spanOpen W) :
    F.presheaf.map (homOfLE (hZ.trans W.1.2)).op s ∈ E.D Z :=
  presheaf_map_map W.1.2 hZ s ▸ E.map_mem hZ W.2

/-- The local values of a section on two witnessing opens agree on their intersection. -/
public lemma μ_inf_compat {V : X.Opens} {s : Γ(F, V)} (W W' : SpanOpens E.D V s) :
    G.presheaf.map (homOfLE (inf_le_left : E.spanOpen W ⊓ E.spanOpen W' ≤ E.spanOpen W)).op
        (E.μ (E.spanOpen W) _ W.2) =
      G.presheaf.map
        (homOfLE (inf_le_right : E.spanOpen W ⊓ E.spanOpen W' ≤ E.spanOpen W')).op
        (E.μ (E.spanOpen W') _ W'.2) := by
  rw [← E.μ_map (inf_le_left : E.spanOpen W ⊓ E.spanOpen W' ≤ E.spanOpen W) _ W.2,
    ← E.μ_map (inf_le_right : E.spanOpen W ⊓ E.spanOpen W' ≤ E.spanOpen W') _ W'.2]
  exact E.μ_congr _ _ (by rw [presheaf_map_map, presheaf_map_map])

/-! ### The glued value -/

/-- **The glued value of the prescribed morphism on a section of `P`.** The unique section of `G`
over `V` restricting to `μ_W (s|_W)` on every open `W ≤ V` carrying `s` into `D`. -/
public def gluedValue (V : X.Opens) (s : Γ(F, V)) (hs : s ∈ P.toSubmodule.obj (op V)) :
    Γ(G, V) :=
  (TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf G.isSheaf
    (ι := SpanOpens E.D V s) (fun W => E.spanOpen W) (fun W => W.1.2)
    (E.le_iSup_spanOpens hs) (fun W => E.μ (E.spanOpen W) _ W.2)
    (fun W W' => E.μ_inf_compat W W')).choose

/-- The glued value restricts to the prescribed value on every open carrying the section into
`D`. -/
public lemma map_gluedValue {V : X.Opens} {s : Γ(F, V)} (hs : s ∈ P.toSubmodule.obj (op V))
    {W : X.Opens} (hW : W ≤ V) (hmem : F.presheaf.map (homOfLE hW).op s ∈ E.D W) :
    G.presheaf.map (homOfLE hW).op (E.gluedValue V s hs) =
      E.μ W (F.presheaf.map (homOfLE hW).op s) hmem :=
  (TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf G.isSheaf
    (ι := SpanOpens E.D V s) (fun W => E.spanOpen W) (fun W => W.1.2)
    (E.le_iSup_spanOpens hs) (fun W => E.μ (E.spanOpen W) _ W.2)
    (fun W W' => E.μ_inf_compat W W')).choose_spec.1 ⟨⟨W, hW⟩, hmem⟩

/-- Two sections of `G` over `V` agreeing on a cover of `V` are equal; stated with the index type
the glueing uses. -/
public lemma eq_of_locally_eq {V : X.Opens} {ι : Type u} (W : ι → X.Opens)
    (hWV : ∀ k, W k ≤ V) (hcov : V ≤ ⨆ k, W k) {a b : Γ(G, V)}
    (h : ∀ k, G.presheaf.map (homOfLE (hWV k)).op a =
      G.presheaf.map (homOfLE (hWV k)).op b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf G.isSheaf W hWV hcov h

/-- Two sections of `G` over `V` agreeing on every open of `SpanOpens` of a section of `P` are
equal. -/
private lemma eq_of_spanOpens_eq {V : X.Opens} {s : Γ(F, V)}
    (hs : s ∈ P.toSubmodule.obj (op V)) {a b : Γ(G, V)}
    (h : ∀ W : SpanOpens E.D V s, G.presheaf.map (homOfLE W.1.2).op a =
      G.presheaf.map (homOfLE W.1.2).op b) : a = b :=
  eq_of_locally_eq (ι := SpanOpens E.D V s) (fun W => E.spanOpen W) (fun W => W.1.2)
    (E.le_iSup_spanOpens hs) h

/-- On an open carrying the section into `D` the glued value *is* the prescribed value. -/
public lemma gluedValue_eq_μ (V : X.Opens) (s : Γ(F, V)) (hs : s ∈ E.D V) :
    E.gluedValue V s (E.le_P V hs) = E.μ V s hs := by
  have hres : F.presheaf.map (homOfLE (le_refl V)).op s = s := presheaf_map_self _ s
  have hmem : F.presheaf.map (homOfLE (le_refl V)).op s ∈ E.D V := by rwa [hres]
  exact (presheaf_map_self (le_refl V) _).symm.trans
    ((E.map_gluedValue (E.le_P V hs) (le_refl V) hmem).trans (E.μ_congr hmem hs hres))

/-! ### The glued value is a morphism -/

/-- The restriction of a section of `P` is a section of `P`. -/
public lemma map_mem_P {V W : X.Opens} (h : W ≤ V) {s : Γ(F, V)}
    (hs : s ∈ P.toSubmodule.obj (op V)) :
    F.presheaf.map (homOfLE h).op s ∈ P.toSubmodule.obj (op W) :=
  P.toSubmodule.map_mem (homOfLE h).op hs

/-- Two sections of `P` over `V` lie in `D` on a common family of opens covering `V`. -/
public lemma le_iSup_spanOpens_inf {V : X.Opens} {s t : Γ(F, V)}
    (hs : s ∈ P.toSubmodule.obj (op V)) (ht : t ∈ P.toSubmodule.obj (op V)) :
    V ≤ ⨆ W : SpanOpens E.D V s × SpanOpens E.D V t, E.spanOpen W.1 ⊓ E.spanOpen W.2 := by
  intro x hx
  obtain ⟨W, h, hxW, hmem⟩ := E.loc V s hs x hx
  obtain ⟨W', h', hxW', hmem'⟩ := E.loc V t ht x hx
  exact Opens.mem_iSup.2 ⟨(⟨⟨W, h⟩, hmem⟩, ⟨⟨W', h'⟩, hmem'⟩), hxW, hxW'⟩

/-- The glued value is additive. -/
public lemma gluedValue_add (V : X.Opens) (s t : Γ(F, V))
    (hs : s ∈ P.toSubmodule.obj (op V)) (ht : t ∈ P.toSubmodule.obj (op V)) :
    E.gluedValue V (s + t) (Submodule.add_mem _ hs ht) =
      E.gluedValue V s hs + E.gluedValue V t ht := by
  refine eq_of_locally_eq (ι := SpanOpens E.D V s × SpanOpens E.D V t)
    (fun W => E.spanOpen W.1 ⊓ E.spanOpen W.2)
    (fun W => le_trans inf_le_left W.1.1.2) (E.le_iSup_spanOpens_inf hs ht) fun W => ?_
  have hZ : E.spanOpen W.1 ⊓ E.spanOpen W.2 ≤ V := le_trans inf_le_left W.1.1.2
  have hsZ : F.presheaf.map (homOfLE hZ).op s ∈ E.D (E.spanOpen W.1 ⊓ E.spanOpen W.2) :=
    E.map_mem_of_le W.1 inf_le_left
  have htZ : F.presheaf.map (homOfLE hZ).op t ∈ E.D (E.spanOpen W.1 ⊓ E.spanOpen W.2) :=
    E.map_mem_of_le W.2 inf_le_right
  have hadd : F.presheaf.map (homOfLE hZ).op (s + t) =
      F.presheaf.map (homOfLE hZ).op s + F.presheaf.map (homOfLE hZ).op t :=
    map_add _ s t
  have hstZ : F.presheaf.map (homOfLE hZ).op (s + t) ∈
      E.D (E.spanOpen W.1 ⊓ E.spanOpen W.2) := by
    rw [hadd]; exact Submodule.add_mem _ hsZ htZ
  refine (E.map_gluedValue (Submodule.add_mem _ hs ht) hZ hstZ).trans
    (((E.μ_congr hstZ (Submodule.add_mem _ hsZ htZ) hadd).trans
      (E.μ_add _ _ _ hsZ htZ)).trans ?_)
  rw [map_add, E.map_gluedValue hs hZ hsZ, E.map_gluedValue ht hZ htZ]

/-- The glued value is `Γ(X, V)`-linear. -/
public lemma gluedValue_smul (V : X.Opens) (r : Γ(X, V)) (s : Γ(F, V))
    (hs : s ∈ P.toSubmodule.obj (op V)) :
    E.gluedValue V (r • s) (Submodule.smul_mem _ r hs) = r • E.gluedValue V s hs := by
  refine E.eq_of_spanOpens_eq hs fun W => ?_
  have hsmul : F.presheaf.map (homOfLE W.1.2).op (r • s) =
      X.presheaf.map (homOfLE W.1.2).op r • F.presheaf.map (homOfLE W.1.2).op s :=
    F.map_smul (homOfLE W.1.2) r s
  have hrsZ : F.presheaf.map (homOfLE W.1.2).op (r • s) ∈ E.D (E.spanOpen W) := by
    rw [hsmul]; exact Submodule.smul_mem _ _ W.2
  refine (E.map_gluedValue (Submodule.smul_mem _ r hs) W.1.2 hrsZ).trans
    (((E.μ_congr hrsZ (Submodule.smul_mem _ _ W.2) hsmul).trans
      (E.μ_smul _ _ _ W.2)).trans ?_)
  rw [G.map_smul (homOfLE W.1.2) r _, E.map_gluedValue hs W.1.2 W.2]

/-- The glued value commutes with restriction. -/
public lemma gluedValue_map {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V))
    (hs : s ∈ P.toSubmodule.obj (op V)) :
    E.gluedValue W (F.presheaf.map (homOfLE h).op s) (map_mem_P h hs) =
      G.presheaf.map (homOfLE h).op (E.gluedValue V s hs) := by
  refine E.eq_of_spanOpens_eq (map_mem_P h hs) fun Z => ?_
  have hcomp : F.presheaf.map (homOfLE Z.1.2).op (F.presheaf.map (homOfLE h).op s) =
      F.presheaf.map (homOfLE (Z.1.2.trans h)).op s :=
    presheaf_map_map h Z.1.2 s
  have hZV : F.presheaf.map (homOfLE (Z.1.2.trans h)).op s ∈ E.D (E.spanOpen Z) := by
    rw [← hcomp]; exact Z.2
  have e2 : G.presheaf.map (homOfLE Z.1.2).op
        (G.presheaf.map (homOfLE h).op (E.gluedValue V s hs)) =
      E.μ (E.spanOpen Z) (F.presheaf.map (homOfLE (Z.1.2.trans h)).op s) hZV := by
    rw [presheaf_map_map h Z.1.2 (E.gluedValue V s hs)]
    exact E.map_gluedValue hs (Z.1.2.trans h) hZV
  exact (E.map_gluedValue (map_mem_P h hs) Z.1.2 Z.2).trans
    ((E.μ_congr Z.2 hZV hcomp).trans e2.symm)

/-- The glued value as local morphism data on the whole of `X`, which is the shape the glueing of
morphisms of sheaves of modules consumes. -/
public def gluedLocal : TopCat.Sheaf.LocalModuleHom (asModules P).val G.val ⊤ where
  app V _ := ModuleCat.ofHom
    { toFun := fun t => E.gluedValue V t.1 t.2
      map_add' := fun t u => E.gluedValue_add V t.1 u.1 t.2 u.2
      map_smul' := fun r t => E.gluedValue_smul V r t.1 t.2 }
  naturality _ hWV t := E.gluedValue_map hWV t.1 t.2

/-- **The glued morphism out of `P`.** -/
public def gluedHom : asModules P ⟶ G :=
  (Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover
    (M := asModules P) (N := G) (ι := PUnit.{u + 1}) (U := fun _ => (⊤ : X.Opens)) (by simp)
    (fun _ => E.gluedLocal) (fun _ _ _ _ _ => rfl)).choose

/-- The glued morphism acts on sections by the glued value. -/
public lemma gluedHom_app (V : X.Opens) (t : Γ(asModules P, V)) :
    Scheme.Modules.Hom.app E.gluedHom V t = E.gluedValue V t.1 t.2 :=
  congr($((Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover
    (M := asModules P) (N := G) (ι := PUnit.{u + 1}) (U := fun _ => (⊤ : X.Opens)) (by simp)
    (fun _ => E.gluedLocal) (fun _ _ _ _ _ => rfl)).choose_spec.1 PUnit.unit V le_top) t)

/-- **The glued morphism takes the prescribed value on a prescribed section.** -/
public lemma gluedHom_app_of_mem (V : X.Opens) (s : Γ(F, V)) (hs : s ∈ E.D V) :
    Scheme.Modules.Hom.app E.gluedHom V ⟨s, E.le_P V hs⟩ = E.μ V s hs :=
  (E.gluedHom_app V ⟨s, E.le_P V hs⟩).trans (E.gluedValue_eq_μ V s hs)

/-- **A morphism out of `P` is determined by its values on the prescribed sections.** -/
public lemma hom_ext (q q' : asModules P ⟶ G)
    (h : ∀ (V : X.Opens) (s : Γ(F, V)) (hs : s ∈ E.D V),
      Scheme.Modules.Hom.app q V ⟨s, E.le_P V hs⟩ =
        Scheme.Modules.Hom.app q' V ⟨s, E.le_P V hs⟩) :
    q = q' := by
  refine Scheme.Modules.hom_ext q q' fun V => ?_
  ext t
  refine E.eq_of_spanOpens_eq t.2 fun Z => ?_
  have hn : ∀ Q : asModules P ⟶ G,
      Scheme.Modules.Hom.app Q (E.spanOpen Z)
          ((asModules P).presheaf.map (homOfLE Z.1.2).op t) =
        G.presheaf.map (homOfLE Z.1.2).op (Scheme.Modules.Hom.app Q V t) :=
    fun Q => NatTrans.naturality_apply Q.mapPresheaf (homOfLE Z.1.2).op t
  rw [← hn q, ← hn q']
  exact h (E.spanOpen Z) _ Z.2

/-- **The morphism out of `P` prescribed by the local data, and the only one.** -/
public theorem existsUnique_hom :
    ∃! q : asModules P ⟶ G, ∀ (V : X.Opens) (s : Γ(F, V)) (hs : s ∈ E.D V),
      Scheme.Modules.Hom.app q V ⟨s, E.le_P V hs⟩ = E.μ V s hs :=
  ⟨E.gluedHom, fun V s hs => E.gluedHom_app_of_mem V s hs, fun q hq =>
    E.hom_ext q E.gluedHom fun V s hs =>
      (hq V s hs).trans (E.gluedHom_app_of_mem V s hs).symm⟩

end LocalData

end Stacks.AlgebraicGeometry.SubmoduleHomGlue

end
