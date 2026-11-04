module

public import Mathlib.Geometry.RingedSpace.Stalks

public import StacksFrontier.Topology.Sheaves.Limits.PullbackSections
public import StacksFrontier.Topology.Sheaves.Limits.SpectralCovers

/-!
# Sections of a colimit of sheaves on a cofiltered limit of spectral spaces (Stacks 0A33)

Let `J` be a cofiltered category, `X_j` a diagram of spectral spaces over `J` with spectral
transition maps `f_a`, and `X = lim_j X_j` the limit with projections `p_j`.  Give each `X_j` a
sheaf of sets `F_j` and each `a : j ⟶ i` an `f_a`-map `φ_a : F_i → F_j`, subject to the cocycle
condition; this is exactly a functor `E : J ⥤ PresheafedSpace` whose spaces are the `X_j`, and it
is packaged as `SpectralSheafSystem`.  Write `F = colim_j p_j⁻¹F_j` on `X`.

**Stacks 0A33** asserts that for `U ⊆ X_i` a quasi-compact open the canonical map
`colim_{a : j → i} F_j(f_a⁻¹U) → F(p_i⁻¹U)` is bijective.

The proof is the source's own.  `p_i⁻¹U` is a quasi-compact open of the spectral space `X` by
Stacks 0A2Z, so Stacks 009F (4) identifies `F(p_i⁻¹U)` with `colim_j (p_j⁻¹F_j)(p_i⁻¹U)`; a section
of `p_j⁻¹F_j` over `p_i⁻¹U` is a section over `p_k⁻¹(f_a⁻¹U)` for any stage `a : k ⟶ i` below `j`
and `i`, and Stacks 0A32 — applied to the single sheaf `F_k` and the quasi-compact open `f_a⁻¹U` —
writes it as coming from a section of `f_b⁻¹F_k` at a further stage, which the adjunction map turns
into a section of `F_{k'}`.  Injectivity runs the same identifications backwards, the equality of
two sections at a finite stage coming from the argument of Stacks 0A2W.

## Contents

* `SpectralSheafSystem`, and `diagram`/`sheafAt` presenting its underlying `SpectralDiagram`.
* The `f_a`-maps on sections and germs — `push`, `pushGerm`, `pushRes` — with the cocycle laws
  `germ_push_push`, `germ_push_id`, `pushRes_id`, `pushRes_pushRes`.
* `pullback j`, the germ-model `p_j⁻¹F_j`, and `pullbackSystem : Jᵒᵖ ⥤ Sheaf`, the system
  `j ↦ p_j⁻¹F_j`, strictly functorial.
* `exists_adj`: a section of `f_b⁻¹F_j` over `W ⊆ X_k` comes from a section of `F_k` over `W`.
  This is the surjectivity input for 0A33.
* `exists_stage_germ_eq` / `exists_stage_push_eq`: two sections of `F_k` over a quasi-compact
  `W` whose germs agree at every point of `X` over `W` become equal at a finite stage.  This is
  the Stacks 0A2W argument and the injectivity input for 0A33.
* `colimitPullback`, the sheaf `F = colim_j p_j⁻¹F_j`, and `bijective_colimitCanonicalMap`:
  `colim_j (p_j⁻¹F_j)(p_i⁻¹U) → F(p_i⁻¹U)` is bijective for `U` quasi-compact.  This is part (4)
  of Stacks 009F applied to `pullbackSystem`, its hypothesis supplied by
  `SpectralDiagram.hasFiniteCompactCofinalCovers_comapProj`.
* `comapProj_stageOpen` (`p_i⁻¹U = p_j⁻¹(f_a⁻¹U)`, which lets sections of the different `F_j` be
  compared over one open of the limit), and `stageFunctor`, the diagram `a ↦ F_j(f_a⁻¹U)` over
  `(Over i)ᵒᵖ` that is the left-hand side of 0A33.
* `stageColimitMap`, the canonical map of 0A33, and `bijective_stageColimitMap`, which is the
  lemma.

Note that `bijective_colimitCanonicalMap` is **not** 0A33: it concerns `(p_j⁻¹F_j)(p_i⁻¹U)`,
whereas the tag concerns `F_j(f_a⁻¹U)`.  The reindexing along `comapProj_stageOpen` is a required
step, not a formality, and the two must not be conflated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open AlgebraicGeometry

universe v u w
universe v'

noncomputable section

/-- A cofiltered system of spectral spaces together with a sheaf of sets on each member and a
compatible system of `f_a`-maps between them.

The data of Stacks 0A33 — a sheaf `F_i` on `X_i` for every `i`, an `f_a`-map
`φ_a : F_i → F_j` for every `a : j ⟶ i`, and the cocycle condition
`φ_{a ∘ b} = φ_b ∘ φ_a` — is exactly a functor into presheafed spaces: a morphism
`E.obj j ⟶ E.obj i` of presheafed spaces is a continuous map `f_a : X_j → X_i` together with a
map `F_i ⟶ (f_a)_* F_j`, which is an `f_a`-map, and the cocycle condition is functoriality.  The
remaining fields say that each `F_i` is a sheaf and that the underlying diagram of spaces is a
diagram of spectral spaces with spectral transition maps, i.e. a `SpectralDiagram`. -/
structure SpectralSheafSystem (J : Type v) [Category.{v'} J] [IsCofiltered J] where
  /-- The diagram of spaces together with their sheaves and the `f_a`-maps between them. -/
  E : J ⥤ PresheafedSpace.{_, _, max v u} (Type max v u)
  /-- Each member of the system is a sheaf, not merely a presheaf. -/
  isSheaf : ∀ j : J, (E.obj j).presheaf.IsSheaf
  /-- Each space of the diagram is spectral. -/
  isSpectralSpace : ∀ j : J, SpectralSpace (E.obj j).carrier
  /-- Each transition map of the diagram is spectral. -/
  isSpectralMap : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (E.map a).base

namespace SpectralSheafSystem

variable {J : Type v} [Category.{v'} J] [IsCofiltered J] (S : SpectralSheafSystem.{v, u} J)

/-- The underlying diagram of spectral spaces of the system, obtained by forgetting the
sheaves. -/
def diagram : SpectralDiagram.{v, u} J where
  F := S.E ⋙ PresheafedSpace.forget _
  isSpectralSpace := S.isSpectralSpace
  isSpectralMap := S.isSpectralMap

/-- The sheaf of the system at the object `j`, as a sheaf on the `j`-th space of the underlying
diagram. -/
def sheafAt (j : J) : (S.diagram.F.obj j).Sheaf (Type max v u) :=
  ⟨(S.E.obj j).presheaf, S.isSheaf j⟩

/-- Two sections of `F_j` over `V` with the same germ at every point of `V` are equal.  This is
`TopCat.Presheaf.section_ext` for `sheafAt j`, restated with `(E.obj j).presheaf` in place of
`(sheafAt j).presheaf` so that the germ lemmas below apply to the goals it produces. -/
lemma section_ext {j : J} (V : Opens (S.diagram.F.obj j))
    (s t : (S.E.obj j).presheaf.obj (op V))
    (h : ∀ (y : S.diagram.F.obj j) (hy : y ∈ V),
      (S.E.obj j).presheaf.germ V y hy s = (S.E.obj j).presheaf.germ V y hy t) : s = t :=
  Presheaf.section_ext (S.sheafAt j) V s t h

/-! ### The `f_a`-maps on sections and on germs -/

/-- The `f_a`-map of the system on sections: the map `F_i(V) → F_j(f_a⁻¹V)` given by the
component of `φ_a : F_i ⟶ (f_a)_*F_j` at `V`. -/
def push {j i : J} (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)}
    (t : (S.E.obj i).presheaf.obj (op V)) :
    (S.E.obj j).presheaf.obj (op ((Opens.map (S.diagram.F.map a)).obj V)) :=
  (S.E.map a).c.app (op V) t

/-- The `f_a`-map of the system on germs: a germ of `F_i` at the image of `y : X_j` is carried to
a germ of `F_j` at `y`.  The germ is presented as an element of the total space
`GermPullback.Germs F_i` together with the identification of its base point with `f_a(y)`, which
is the form in which the values of a section of `p_i⁻¹F_i` come. -/
def pushGerm {j i : J} (a : j ⟶ i) (y : S.diagram.F.obj j) :
    (γ : GermPullback.Germs (S.E.obj i).presheaf) → γ.1 = S.diagram.mapFun a y →
      GermPullback.Germs (S.E.obj j).presheaf
  | ⟨_, ξ⟩, h => ⟨y, (S.E.map a).stalkMap y
      (h ▸ ξ : (S.E.obj i).presheaf.stalk (S.diagram.mapFun a y))⟩

/-- `pushGerm` on a germ presented at the base point `f_a(y)` itself is the stalk map of `φ_a`. -/
lemma pushGerm_mk {j i : J} (a : j ⟶ i) (y : S.diagram.F.obj j)
    (ξ : (S.E.obj i).presheaf.stalk (S.diagram.mapFun a y))
    (h : (⟨S.diagram.mapFun a y, ξ⟩ : GermPullback.Germs (S.E.obj i).presheaf).1 =
      S.diagram.mapFun a y) :
    S.pushGerm a y ⟨S.diagram.mapFun a y, ξ⟩ h = ⟨y, (S.E.map a).stalkMap y ξ⟩ := rfl

/-- `pushGerm` depends only on the germ, not on the proof identifying its base point. -/
lemma pushGerm_congr {j i : J} (a : j ⟶ i) (y : S.diagram.F.obj j)
    {γ γ' : GermPullback.Germs (S.E.obj i).presheaf} (e : γ = γ')
    (h : γ.1 = S.diagram.mapFun a y) (h' : γ'.1 = S.diagram.mapFun a y) :
    S.pushGerm a y γ h = S.pushGerm a y γ' h' := by
  subst e; rfl

/-- The base point of a pushed germ is the point it is pushed to. -/
lemma pushGerm_fst {j i : J} (a : j ⟶ i) (y : S.diagram.F.obj j)
    (γ : GermPullback.Germs (S.E.obj i).presheaf) (h : γ.1 = S.diagram.mapFun a y) :
    (S.pushGerm a y γ h).1 = y := by
  obtain ⟨y', ξ⟩ := γ; rfl

/-- Germs at the same point are equal as elements of the total space when their stalk components
are equal. -/
private lemma germs_mk_congr {Y : TopCat.{w}} {𝒢 : Y.Presheaf (Type w)} {y : Y} {ξ ζ : 𝒢.stalk y}
    (h : ξ = ζ) : (⟨y, ξ⟩ : GermPullback.Germs 𝒢) = ⟨y, ζ⟩ :=
  congrArg (fun ζ ↦ (⟨y, ζ⟩ : GermPullback.Germs 𝒢)) h

/-- The `f_a`-map carries the germ of a section `t` of `F_i` at `f_a(y)` to the germ at `y` of the
section `φ_a t` of `F_j`.  This is `AlgebraicGeometry.PresheafedSpace.stalkMap_germ`. -/
lemma pushGerm_germ {j i : J} (a : j ⟶ i) (y : S.diagram.F.obj j)
    {V : Opens (S.diagram.F.obj i)} (t : (S.E.obj i).presheaf.obj (op V))
    (hy : S.diagram.mapFun a y ∈ V)
    (h : (⟨S.diagram.mapFun a y, (S.E.obj i).presheaf.germ V _ hy t⟩ :
      GermPullback.Germs (S.E.obj i).presheaf).1 = S.diagram.mapFun a y) :
    S.pushGerm a y ⟨S.diagram.mapFun a y, (S.E.obj i).presheaf.germ V _ hy t⟩ h =
      ⟨y, (S.E.obj j).presheaf.germ ((Opens.map (S.diagram.F.map a)).obj V) y hy (S.push a t)⟩ := by
  rw [S.pushGerm_mk a y]
  exact germs_mk_congr (PresheafedSpace.stalkMap_germ_apply (S.E.map a) V y hy t)

/-- The `f_a`-maps of the system compose, read on germs: the germ at `z` of `φ_{b ≫ a} t` is the
germ at `z` of `φ_b (φ_a t)`.  This is functoriality of `E`, the identification
`f_{b ≫ a}⁻¹V = f_b⁻¹(f_a⁻¹V)` of the opens involved being absorbed into the germ. -/
lemma germ_push_push {k j i : J} (b : k ⟶ j) (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)}
    (t : (S.E.obj i).presheaf.obj (op V)) (z : S.diagram.F.obj k)
    (h₁ : z ∈ (Opens.map (S.diagram.F.map (b ≫ a))).obj V)
    (h₂ : z ∈ (Opens.map (S.diagram.F.map b)).obj ((Opens.map (S.diagram.F.map a)).obj V)) :
    (S.E.obj k).presheaf.germ _ z h₁ (S.push (b ≫ a) t) =
      (S.E.obj k).presheaf.germ _ z h₂ (S.push b (S.push a t)) := by
  have h := ConcreteCategory.congr_hom
    (PresheafedSpace.congr_app (S.E.map_comp b a) (op V)) t
  rw [ConcreteCategory.comp_apply] at h
  rw [show S.push (b ≫ a) t = _ from h]
  exact (S.E.obj k).presheaf.germ_res_apply _ z h₁ _

/-- The `f`-map of the identity is the identity, read on germs. -/
lemma germ_push_id {j : J} {V : Opens (S.diagram.F.obj j)}
    (t : (S.E.obj j).presheaf.obj (op V)) (z : S.diagram.F.obj j)
    (h₁ : z ∈ (Opens.map (S.diagram.F.map (𝟙 j))).obj V) (h₂ : z ∈ V) :
    (S.E.obj j).presheaf.germ _ z h₁ (S.push (𝟙 j) t) =
      (S.E.obj j).presheaf.germ V z h₂ t := by
  have h := ConcreteCategory.congr_hom
    (PresheafedSpace.congr_app (S.E.map_id j) (op V)) t
  rw [ConcreteCategory.comp_apply] at h
  rw [show S.push (𝟙 j) t = _ from h]
  exact (S.E.obj j).presheaf.germ_res_apply _ z h₁ _

/-! ### The pullback of the system to the limit -/

/-- The value at a point `z` of a section of a germ-model pullback `g⁻¹𝒢` is a germ based at
`g z`. -/
lemma germs_fst {Z Y : TopCat.{w}} {g : Z → Y} {𝒢 : Y.Presheaf (Type w)}
    {W : Opens Z} (σ : (GermPullback.sheaf g 𝒢).presheaf.obj (op W)) (z : W) :
    (σ.1 z).1 = g z.1 := by
  obtain ⟨W₀, hz₀, i₀, V, hV, s, hs⟩ := GermPullback.exists_repr σ z.2
  calc (σ.1 z).1 = (σ.1 (i₀ ⟨z.1, hz₀⟩)).1 := by
        rw [show i₀ ⟨z.1, hz₀⟩ = z from Subtype.ext rfl]
    _ = g z.1 := by rw [hs ⟨z.1, hz₀⟩]

/-- The pullback `p_j⁻¹F_j` to the limit `X` of the `j`-th sheaf of the system, in the germ model
of `GermPullback`. -/
def pullback (j : J) : (S.diagram.invLimit).Sheaf (Type max v u) :=
  GermPullback.sheaf (S.diagram.projFun j) (S.E.obj j).presheaf

/-- The underlying function of the transition map `p_i⁻¹F_i → p_j⁻¹F_j` of the pullback system:
at a point `z` of the limit it applies the stalk map of `φ_a` to the germ that `σ` has there. -/
def pullbackMapFun {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) (z : W) :
    GermPullback.Germs (S.E.obj j).presheaf :=
  S.pushGerm a (S.diagram.projFun j z.1) (σ.1 z)
    ((germs_fst σ z).trans (S.diagram.projFun_eq_mapFun a z.1))

/-- The transition map of the pullback system, computed at a point where `σ` is given by the germs
of a section `s` of `F_i`: it is there the germ of `φ_a s`. -/
private lemma pullbackMapFun_of_germ {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) (z : W) {V : Opens (S.diagram.F.obj i)}
    (hV : S.diagram.projFun i z.1 ∈ V) (s : (S.E.obj i).presheaf.obj (op V))
    (hσ : σ.1 z = ⟨S.diagram.projFun i z.1, (S.E.obj i).presheaf.germ V _ hV s⟩)
    (hV' : S.diagram.mapFun a (S.diagram.projFun j z.1) ∈ V) :
    S.pullbackMapFun a σ z =
      ⟨S.diagram.projFun j z.1, (S.E.obj j).presheaf.germ
        ((Opens.map (S.diagram.F.map a)).obj V) _ hV' (S.push a s)⟩ := by
  have he : σ.1 z = ⟨S.diagram.mapFun a (S.diagram.projFun j z.1),
      (S.E.obj i).presheaf.germ V _ hV' s⟩ := by
    rw [hσ]
    exact GermPullback.Germs.mk_eq_mk s (S.diagram.projFun_eq_mapFun a z.1) hV hV'
  exact (S.pushGerm_congr a _ he _ (by rfl)).trans
    (S.pushGerm_germ a _ s hV' (by rfl))

/-- The transition map of the pullback system carries sections to sections: the germwise image of
a section given near a point by the germs of `t` is given there by the germs of `φ_a t`. -/
lemma pullbackMapFun_pred {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) :
    (GermPullback.pre (S.diagram.projFun j) (S.E.obj j).presheaf).sheafify.pred
      (S.pullbackMapFun a σ) := by
  intro z
  obtain ⟨W₀, hz₀, i₀, V, hV, s, hs⟩ := GermPullback.exists_repr σ z.2
  have hV' : ∀ x : W₀, S.diagram.projFun j (i₀ x).1 ∈ (Opens.map (S.diagram.F.map a)).obj V := by
    intro x
    have : S.diagram.mapFun a (S.diagram.projFun j (i₀ x).1) = S.diagram.projFun i x.1 :=
      (S.diagram.projFun_eq_mapFun a x.1).symm
    rw [S.diagram.mem_map_mapFun, this]
    exact hV x
  exact ⟨W₀, hz₀, i₀, (Opens.map (S.diagram.F.map a)).obj V, hV', S.push a s,
    fun x ↦ S.pullbackMapFun_of_germ a σ (i₀ x) (hV x) s (hs x) (hV' x)⟩

/-- The transition map `p_i⁻¹F_i → p_j⁻¹F_j` of the pullback system on sections over `W`. -/
def pullbackMap {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) : (S.pullback j).presheaf.obj (op W) :=
  ⟨S.pullbackMapFun a σ, S.pullbackMapFun_pred a σ⟩

/-- The transition map of the pullback system is computed pointwise. -/
@[simp]
lemma pullbackMap_val {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) (z : W) :
    (S.pullbackMap a σ).1 z = S.pushGerm a (S.diagram.projFun j z.1) (σ.1 z)
      ((germs_fst σ z).trans (S.diagram.projFun_eq_mapFun a z.1)) := rfl

/-- At any single point, a section of `p_j⁻¹F_j` is the germ of a section of `F_j` on an open
containing the image of that point.  This is `GermPullback.exists_repr`, read at the point
itself. -/
lemma exists_germ_repr {j : J} {W : Opens S.diagram.invLimit}
    (σ : (S.pullback j).presheaf.obj (op W)) (z : W) :
    ∃ (V : Opens (S.diagram.F.obj j)) (hV : S.diagram.projFun j z.1 ∈ V)
      (s : (S.E.obj j).presheaf.obj (op V)),
      σ.1 z = ⟨S.diagram.projFun j z.1, (S.E.obj j).presheaf.germ V _ hV s⟩ := by
  obtain ⟨W₀, hz₀, i₀, V, hV, s, hs⟩ := GermPullback.exists_repr σ z.2
  exact ⟨V, hV ⟨z.1, hz₀⟩, s, hs ⟨z.1, hz₀⟩⟩

/-- The transition map of the pullback system, computed on a section presented near a point as
the germs of a section `s` of `F_i`: it is there the germ of `φ_a s`. -/
lemma pullbackMap_val_of_germ {j i : J} (a : j ⟶ i) {W : Opens S.diagram.invLimit}
    (σ : (S.pullback i).presheaf.obj (op W)) (z : W) {V : Opens (S.diagram.F.obj i)}
    (hV : S.diagram.projFun i z.1 ∈ V) (s : (S.E.obj i).presheaf.obj (op V))
    (hσ : σ.1 z = ⟨S.diagram.projFun i z.1, (S.E.obj i).presheaf.germ V _ hV s⟩)
    (hV' : S.diagram.mapFun a (S.diagram.projFun j z.1) ∈ V) :
    (S.pullbackMap a σ).1 z =
      ⟨S.diagram.projFun j z.1, (S.E.obj j).presheaf.germ
        ((Opens.map (S.diagram.F.map a)).obj V) _ hV' (S.push a s)⟩ :=
  S.pullbackMapFun_of_germ a σ z hV s hσ hV'

/-- **The system `j ↦ p_j⁻¹F_j` of sheaves on the limit `X`, indexed by `Jᵒᵖ`.**  The transition
map along `a : j ⟶ i` is the germwise action of the `f_a`-map `φ_a`, so the system is strictly
functorial: no coherence isomorphism between iterated pullbacks is involved. -/
def pullbackSystem : Jᵒᵖ ⥤ (S.diagram.invLimit).Sheaf (Type max v u) where
  obj A := S.pullback A.unop
  map {_ _} α := ⟨{ app := fun _ ↦ ↾fun σ ↦ S.pullbackMap α.unop σ
                    naturality := by
                      intro _ _ _
                      refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
                      exact GermPullback.ext fun _ ↦ rfl }⟩
  map_id A := by
    refine InducedCategory.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    refine GermPullback.ext fun z ↦ ?_
    obtain ⟨V, hV, s, hσ⟩ := S.exists_germ_repr (W := W.unop) σ z
    have hV' : S.diagram.mapFun (𝟙 A.unop) (S.diagram.projFun A.unop z.1) ∈ V := by
      rw [S.diagram.mapFun_id]; exact hV
    simp only [TypeCat.ofHom_apply, TopCat.Sheaf.id_app, ConcreteCategory.id_apply, unop_id]
    rw [S.pullbackMap_val_of_germ (𝟙 A.unop) σ z hV s hσ hV', hσ]
    exact congrArg (fun ζ ↦ (⟨S.diagram.projFun A.unop z.1, ζ⟩ :
      GermPullback.Germs (S.E.obj A.unop).presheaf))
      (S.germ_push_id s (S.diagram.projFun A.unop z.1) hV' hV)
  map_comp {A B C} α β := by
    refine InducedCategory.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    refine GermPullback.ext fun z ↦ ?_
    obtain ⟨V, hV, s, hσ⟩ := S.exists_germ_repr (W := W.unop) σ z
    have hVa : S.diagram.mapFun α.unop (S.diagram.projFun B.unop z.1) ∈ V := by
      rw [← S.diagram.projFun_eq_mapFun]; exact hV
    have hVba : S.diagram.mapFun (β.unop ≫ α.unop) (S.diagram.projFun C.unop z.1) ∈ V := by
      rw [← S.diagram.projFun_eq_mapFun]; exact hV
    have hVb : S.diagram.mapFun β.unop (S.diagram.projFun C.unop z.1) ∈
        (Opens.map (S.diagram.F.map α.unop)).obj V := by
      rw [S.diagram.mem_map_mapFun, ← S.diagram.mapFun_comp]; exact hVba
    have hstep := S.pullbackMap_val_of_germ α.unop σ z hV s hσ hVa
    change (S.pullbackMap (β.unop ≫ α.unop) σ).1 z =
      (S.pullbackMap β.unop (S.pullbackMap α.unop σ)).1 z
    rw [S.pullbackMap_val_of_germ (β.unop ≫ α.unop) σ z hV s hσ hVba,
      S.pullbackMap_val_of_germ β.unop (S.pullbackMap α.unop σ) z hVa (S.push α.unop s)
        hstep hVb]
    exact congrArg (fun ζ ↦ (⟨S.diagram.projFun C.unop z.1, ζ⟩ :
      GermPullback.Germs (S.E.obj C.unop).presheaf))
      (S.germ_push_push β.unop α.unop s (S.diagram.projFun C.unop z.1) hVba hVb)

/-- The transition map of the pullback system is `pullbackMap`, pointwise. -/
@[simp]
lemma pullbackSystem_map_val {A B : Jᵒᵖ} (α : A ⟶ B) (W : Opens S.diagram.invLimit)
    (σ : (S.pullback A.unop).presheaf.obj (op W)) :
    ((S.pullbackSystem.map α).hom.app (op W)) σ = S.pullbackMap α.unop σ := rfl

/-! ### Two general facts about sheaves of sets -/

/-- Two germs of a sheaf at the same point are equal as soon as they are equal as elements of the
total space of germs. -/
lemma germs_snd_eq {Y : TopCat.{w}} {𝒢 : Y.Presheaf (Type w)} {y : Y} {ξ ζ : 𝒢.stalk y}
    (h : (⟨y, ξ⟩ : GermPullback.Germs 𝒢) = ⟨y, ζ⟩) : ξ = ζ :=
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h).2

/-- The locus where two sections of a presheaf have the same germ is open. -/
lemma isOpen_germ_agree {Y : TopCat.{w}} (𝒢 : Y.Presheaf (Type w)) (V : Opens Y)
    (s t : 𝒢.obj (op V)) :
    IsOpen {y : Y | ∃ hy : y ∈ V, 𝒢.germ V y hy s = 𝒢.germ V y hy t} := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨hyV, he⟩ := hy
  obtain ⟨V', hyV', i₁, i₂, he'⟩ := 𝒢.germ_eq y hyV hyV s t he
  refine ⟨(V' ⊓ V : Opens Y), fun x hx ↦ ⟨hx.2, ?_⟩, (V' ⊓ V).isOpen, hyV', hyV⟩
  rw [← 𝒢.germ_res_apply i₁ x hx.1 s, ← 𝒢.germ_res_apply i₂ x hx.1 t, he']

/-- A family of sections of a sheaf on a covering of `U`, any two of which have the same germ at
every common point, comes from a section over `U` with those germs. -/
lemma exists_section_of_germ_agree {Y : TopCat.{w}} (𝒢 : Y.Sheaf (Type w)) (U : Opens Y)
    {ι : Type w} (A : ι → Opens Y) (hA : ∀ l, A l ≤ U) (hcov : ∀ x ∈ U, ∃ l, x ∈ A l)
    (s : ∀ l, 𝒢.presheaf.obj (op (A l)))
    (hagree : ∀ (l l' : ι) (x : Y) (hx : x ∈ A l) (hx' : x ∈ A l'),
      𝒢.presheaf.germ (A l) x hx (s l) = 𝒢.presheaf.germ (A l') x hx' (s l')) :
    ∃ t : 𝒢.presheaf.obj (op U), ∀ (l : ι) (x : Y) (hx : x ∈ A l) (hxU : x ∈ U),
      𝒢.presheaf.germ U x hxU t = 𝒢.presheaf.germ (A l) x hx (s l) := by
  have hcompat : Presheaf.IsCompatible 𝒢.presheaf A s := by
    intro l l'
    refine Presheaf.section_ext 𝒢 (A l ⊓ A l') _ _ fun x hx ↦ ?_
    rw [𝒢.presheaf.germ_res_apply, 𝒢.presheaf.germ_res_apply]
    exact hagree l l' x hx.1 hx.2
  obtain ⟨t, ht, -⟩ := 𝒢.existsUnique_gluing' A U (fun l ↦ homOfLE (hA l))
    (fun x hx ↦ Opens.mem_iSup.mpr (hcov x hx)) s hcompat
  refine ⟨t, fun l x hx hxU ↦ ?_⟩
  rw [← ht l]
  exact (𝒢.presheaf.germ_res_apply (homOfLE (hA l)) x hx t).symm

/-! ### The `f_a`-maps followed by a restriction -/

/-- The `f_a`-map of the system followed by restriction to an open `V'` of `X_j` contained in
`f_a⁻¹V`.  This is the transition map of the diagram whose colimit is the left-hand side of
Stacks 0A33. -/
def pushRes {j i : J} (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)} {V' : Opens (S.diagram.F.obj j)}
    (hV' : V' ≤ (Opens.map (S.diagram.F.map a)).obj V)
    (t : (S.E.obj i).presheaf.obj (op V)) : (S.E.obj j).presheaf.obj (op V') :=
  (S.E.obj j).presheaf.map (homOfLE hV').op (S.push a t)

/-- The germs of `pushRes` are the germs of `push`. -/
lemma germ_pushRes {j i : J} (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)}
    {V' : Opens (S.diagram.F.obj j)} (hV' : V' ≤ (Opens.map (S.diagram.F.map a)).obj V)
    (t : (S.E.obj i).presheaf.obj (op V)) (y : S.diagram.F.obj j) (hy : y ∈ V')
    (hy' : y ∈ (Opens.map (S.diagram.F.map a)).obj V) :
    (S.E.obj j).presheaf.germ V' y hy (S.pushRes a hV' t) =
      (S.E.obj j).presheaf.germ _ y hy' (S.push a t) :=
  (S.E.obj j).presheaf.germ_res_apply (homOfLE hV') y hy _

/-- The germ at `y` of `pushRes a hV' t` is the image under the stalk map of `φ_a` of the germ of
`t` at `f_a(y)`. -/
lemma pushGerm_germ_pushRes {j i : J} (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)}
    {V' : Opens (S.diagram.F.obj j)} (hV' : V' ≤ (Opens.map (S.diagram.F.map a)).obj V)
    (t : (S.E.obj i).presheaf.obj (op V)) (y : S.diagram.F.obj j) (hy : y ∈ V')
    (hy' : S.diagram.mapFun a y ∈ V) :
    (⟨y, (S.E.obj j).presheaf.germ V' y hy (S.pushRes a hV' t)⟩ :
        GermPullback.Germs (S.E.obj j).presheaf) =
      S.pushGerm a y ⟨S.diagram.mapFun a y, (S.E.obj i).presheaf.germ V _ hy' t⟩ (by rfl) := by
  rw [S.pushGerm_germ a y t hy']
  exact germs_mk_congr (S.germ_pushRes a hV' t y hy hy')

/-- `pushRes` along an identity is a restriction; in particular it is the identity when the two
opens agree. -/
lemma pushRes_id {j : J} {V V' : Opens (S.diagram.F.obj j)}
    (hV' : V' ≤ (Opens.map (S.diagram.F.map (𝟙 j))).obj V) (hle : V' ≤ V)
    (t : (S.E.obj j).presheaf.obj (op V)) :
    S.pushRes (𝟙 j) hV' t = (S.E.obj j).presheaf.map (homOfLE hle).op t := by
  refine S.section_ext V' _ _ fun y hy ↦ ?_
  exact (S.germ_pushRes (𝟙 j) hV' t y hy (hV' hy)).trans
    ((S.germ_push_id t y (hV' hy) (hle hy)).trans
      ((S.E.obj j).presheaf.germ_res_apply (homOfLE hle) y hy t).symm)

/-- `pushRes` composes: this is the cocycle condition on the `f_a`-maps, in the form in which the
diagram of the left-hand side of Stacks 0A33 is functorial. -/
lemma pushRes_pushRes {k j i : J} (b : k ⟶ j) (a : j ⟶ i) {V : Opens (S.diagram.F.obj i)}
    {V' : Opens (S.diagram.F.obj j)} {V'' : Opens (S.diagram.F.obj k)}
    (h₁ : V' ≤ (Opens.map (S.diagram.F.map a)).obj V)
    (h₂ : V'' ≤ (Opens.map (S.diagram.F.map b)).obj V')
    (h₃ : V'' ≤ (Opens.map (S.diagram.F.map (b ≫ a))).obj V)
    (t : (S.E.obj i).presheaf.obj (op V)) :
    S.pushRes b h₂ (S.pushRes a h₁ t) = S.pushRes (b ≫ a) h₃ t := by
  refine S.section_ext V'' _ _ fun y hy ↦ ?_
  have hyb : S.diagram.mapFun b y ∈ V' := h₂ hy
  have hyba : y ∈ (Opens.map (S.diagram.F.map b)).obj ((Opens.map (S.diagram.F.map a)).obj V) :=
    h₁ hyb
  have hmid : (⟨S.diagram.mapFun b y,
        (S.E.obj j).presheaf.germ V' _ hyb (S.pushRes a h₁ t)⟩ :
          GermPullback.Germs (S.E.obj j).presheaf) =
      ⟨S.diagram.mapFun b y, (S.E.obj j).presheaf.germ
        ((Opens.map (S.diagram.F.map a)).obj V) _ hyba (S.push a t)⟩ :=
    germs_mk_congr (S.germ_pushRes a h₁ t _ hyb hyba)
  have hstep : (⟨y, (S.E.obj k).presheaf.germ V'' y hy (S.pushRes b h₂ (S.pushRes a h₁ t))⟩ :
      GermPullback.Germs (S.E.obj k).presheaf) =
      ⟨y, (S.E.obj k).presheaf.germ _ y hyba (S.push b (S.push a t))⟩ :=
    (S.pushGerm_germ_pushRes b h₂ (S.pushRes a h₁ t) y hy hyb).trans
      ((S.pushGerm_congr b y hmid rfl rfl).trans
        (S.pushGerm_germ b y (S.push a t) hyba rfl))
  exact (germs_snd_eq hstep).trans
    ((S.germ_push_push b a t y (h₃ hy) hyba).symm.trans
      (S.germ_pushRes (b ≫ a) h₃ t y hy (h₃ hy)).symm)

/-! ### From a germ-model pullback back to the system -/

/-- **The adjunction map of an `f_b`-map, in the germ model.**  A section `ρ` of the germ-model
pullback `f_b⁻¹F_j` over an open `W` of `X_k` comes from a section of `F_k` over `W`: locally `ρ`
is the family of germs of a section `t` of `F_j`, and the local sections `φ_b t` glue because
their germs at every point are the image of the germ of `ρ` there.  No spectrality is used. -/
lemma exists_adj {k j : J} (b : k ⟶ j) {W : Opens (S.diagram.F.obj k)}
    (ρ : (GermPullback.sheaf (S.diagram.mapFun b) (S.E.obj j).presheaf).presheaf.obj (op W)) :
    ∃ t : (S.E.obj k).presheaf.obj (op W), ∀ (y : S.diagram.F.obj k) (hy : y ∈ W),
      (⟨y, (S.E.obj k).presheaf.germ W y hy t⟩ : GermPullback.Germs (S.E.obj k).presheaf) =
        S.pushGerm b y (ρ.1 ⟨y, hy⟩) (germs_fst ρ ⟨y, hy⟩) := by
  classical
  choose A hA i₀ V hV tt ht using fun y : W ↦ GermPullback.exists_repr ρ y.2
  have hAV : ∀ (y : W), A y ≤ (Opens.map (S.diagram.F.map b)).obj (V y) :=
    fun y x hx ↦ hV y ⟨x, hx⟩
  -- The local section of `F_k` attached to `y`, and its germs.
  have hkey : ∀ (y : W) (x : S.diagram.F.obj k) (hx : x ∈ A y),
      (⟨x, (S.E.obj k).presheaf.germ (A y) x hx (S.pushRes b (hAV y) (tt y))⟩ :
          GermPullback.Germs (S.E.obj k).presheaf) =
        S.pushGerm b x (ρ.1 ⟨x, (i₀ y).le hx⟩) (germs_fst ρ ⟨x, (i₀ y).le hx⟩) := by
    intro y x hx
    exact (S.pushGerm_germ_pushRes b (hAV y) (tt y) x hx (hV y ⟨x, hx⟩)).trans
      (S.pushGerm_congr b x (ht y ⟨x, hx⟩).symm _ _)
  obtain ⟨t, htg⟩ := exists_section_of_germ_agree (S.sheafAt k) W A (fun y ↦ (i₀ y).le)
    (fun x hx ↦ ⟨⟨x, hx⟩, hA ⟨x, hx⟩⟩) (fun y ↦ S.pushRes b (hAV y) (tt y))
    fun y y' x hx hx' ↦ germs_snd_eq ((hkey y x hx).trans (hkey y' x hx').symm)
  refine ⟨t, fun y hy ↦ ?_⟩
  refine Eq.trans (germs_mk_congr (htg ⟨y, hy⟩ y (hA ⟨y, hy⟩) hy)) ?_
  exact hkey ⟨y, hy⟩ y (hA ⟨y, hy⟩)

/-! ### Equalising two sections at a stage -/

/-- Two sections of `F_k` over a quasi-compact open `W ⊆ X_k` whose germs agree at every point of
`X` lying over `W` have germs agreeing at every point of `W` in the image of some stage
`c : m ⟶ k`.

This is the argument of Stacks 0A2W used in the injectivity half of Stacks 0A32: the locus in `W`
where the two germs differ is closed, and if it met every stage the limit of those loci would be
nonempty, producing a point of `X` over `W` at which the germs differ. -/
lemma exists_stage_germ_eq {k : J} (W : Opens (S.diagram.F.obj k))
    (hW : IsCompact (W : Set (S.diagram.F.obj k)))
    (s t : (S.E.obj k).presheaf.obj (op W))
    (h : ∀ (x : S.diagram.invLimit) (hx : S.diagram.projFun k x ∈ W),
      (S.E.obj k).presheaf.germ W _ hx s = (S.E.obj k).presheaf.germ W _ hx t) :
    ∃ (m : J) (c : m ⟶ k), ∀ (y : S.diagram.F.obj m) (hy : S.diagram.mapFun c y ∈ W),
      (S.E.obj k).presheaf.germ W _ hy s = (S.E.obj k).presheaf.germ W _ hy t := by
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨x, hxW, hxS⟩ := S.diagram.exists_projFun_mem_diff_of_forall_nonempty W.isOpen hW
    (isOpen_germ_agree (S.E.obj k).presheaf W s t) fun m c ↦ by
      have hne := hcon m c
      simp only [not_forall] at hne
      obtain ⟨y, hy, hneq⟩ := hne
      exact ⟨y, hy, fun hmem ↦ hneq hmem.2⟩
  exact hxS ⟨hxW, h x hxW⟩

/-- Two sections of `F_k` over a quasi-compact open `W ⊆ X_k` whose germs agree at every point of
`X` lying over `W` become equal after applying the `f_c`-map of some stage `c : m ⟶ k`.  Germwise
agreement over the image of `f_c` upgrades to equality because `F_m` is a sheaf. -/
lemma exists_stage_push_eq {k : J} (W : Opens (S.diagram.F.obj k))
    (hW : IsCompact (W : Set (S.diagram.F.obj k)))
    (s t : (S.E.obj k).presheaf.obj (op W))
    (h : ∀ (x : S.diagram.invLimit) (hx : S.diagram.projFun k x ∈ W),
      (S.E.obj k).presheaf.germ W _ hx s = (S.E.obj k).presheaf.germ W _ hx t) :
    ∃ (m : J) (c : m ⟶ k), S.push c s = S.push c t := by
  obtain ⟨m, c, hc⟩ := S.exists_stage_germ_eq W hW s t h
  refine ⟨m, c, ?_⟩
  refine S.section_ext _ _ _ fun y hy ↦ ?_
  refine germs_snd_eq (Eq.trans (S.pushGerm_germ c y s hy (by rfl)).symm ?_)
  refine Eq.trans ?_ (S.pushGerm_germ c y t hy (by rfl))
  refine S.pushGerm_congr c y ?_ _ _
  exact germs_mk_congr (hc y hy)

/-! ### The colimit `F = colim_j p_j⁻¹F_j` -/

omit [Category.{v'} J] [IsCofiltered J] in
/-- `Jᵒᵖ` is small relative to the universe `max v u` of the sheaves of the system, which is what
the colimit constructions of `DirectedColimitOfSheaves` require of their index category. -/
lemma small_indexOp : Small.{max v u} Jᵒᵖ := small_max.{u} _

attribute [local instance] small_indexOp

/-- **The colimit `F = colim_j p_j⁻¹F_j`**, taken in sheaves of sets on the limit `X`: the
sheafification of the colimit of the pullback system of presheaves. -/
def colimitPullback : (S.diagram.invLimit).Sheaf (Type max v u) :=
  DirectedColimitOfSheaves.colimitSheaf S.pullbackSystem

/-- **Step 1 of Stacks 0A33**: the canonical map
`colim_j (p_j⁻¹F_j)(p_i⁻¹U) → F(p_i⁻¹U)` is bijective when `U` is quasi-compact.  This is part
(4) of Stacks 009F applied to the pullback system, the hypothesis on `p_i⁻¹U` being supplied by
`SpectralDiagram.hasFiniteCompactCofinalCovers_comapProj`. -/
theorem bijective_colimitCanonicalMap {i : J} (U : Opens (S.diagram.F.obj i))
    (hU : IsCompact (U : Set (S.diagram.F.obj i))) :
    Function.Bijective (DirectedColimitOfSheaves.canonicalMap S.pullbackSystem
      (S.diagram.comapProj i U)) :=
  DirectedColimitOfSheaves.bijective_canonicalMap_of_hasFiniteCompactCofinalCovers
    S.pullbackSystem _ (S.diagram.hasFiniteCompactCofinalCovers_comapProj i U hU)

/-! ### The left-hand side of Stacks 0A33: the diagram of stage sections -/

section StageSections

variable {i : J} (U : Opens (S.diagram.F.obj i))

omit [IsCofiltered J] in
/-- The opposite slice `(Over i)ᵒᵖ`, the index shape of the left-hand side of Stacks 0A33, is
small relative to the universe `max v u` of the sheaves of the system.  Its objects live in
`Type (max v v')`, so this is exactly `UnivLE.{max v v', max v u}`; when the index morphisms
live in the same universe as the index objects it is automatic.

Stated and installed as a local instance of its own because the floating `small_indexOp` above
would otherwise be tried here with its universes undetermined, which leaves instance search
stuck on `max u v =?= max (max v v') ?u` rather than failing. -/
lemma small_sliceOp [UnivLE.{max v v', max v u}] : Small.{max v u} ((Over i)ᵒᵖ) :=
  UnivLE.small _

attribute [local instance 2000] small_sliceOp

/-- Along a morphism of stages the stage opens are nested, because `f_{a'} = f_a ∘ f_{g}`.  This
is `SpectralDiagram.slice_mem` read as an inclusion of opens. -/
lemma stageOpen_le {A A' : Over i} (g : A' ⟶ A) :
    S.diagram.slicePre U A' ≤
      (Opens.map (S.diagram.F.map g.left)).obj (S.diagram.slicePre U A) :=
  fun y hy ↦ S.diagram.slice_mem U g ⟨y, hy⟩

/-- **`p_i⁻¹U = p_j⁻¹(f_a⁻¹U)`**: the preimage of `U` in the limit is computed by any stage.
This is what lets the sections of the different `F_j` be compared over one and the same open of
the limit. -/
lemma comapProj_stageOpen (A : Over i) :
    S.diagram.comapProj A.left (S.diagram.slicePre U A) = S.diagram.comapProj i U := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, S.diagram.mem_comapProj, S.diagram.mem_comapProj,
    S.diagram.projFun_eq_mapFun A.hom x]
  rfl

/-- Every point of `p_i⁻¹U` lands in the stage open `f_a⁻¹U` under `p_j`. -/
lemma projFun_mem_stageOpen (A : Over i) (z : S.diagram.comapProj i U) :
    S.diagram.projFun A.left z.1 ∈ S.diagram.slicePre U A := by
  rw [S.diagram.mem_slicePre, ← S.diagram.projFun_eq_mapFun A.hom z.1]
  exact z.2

/-- **The diagram of the left-hand side of Stacks 0A33**: over the opposite of the slice category
`Over i`, the stage `a : j ⟶ i` is sent to the sections `F_j(f_a⁻¹U)`, and a morphism of stages
`g : a' ⟶ a` acts by the `f_g`-map followed by restriction.  Functoriality is the cocycle
condition on the `f`-maps, in the form `pushRes_pushRes`. -/
def stageFunctor : (Over i)ᵒᵖ ⥤ Type max v u where
  obj A := (S.E.obj A.unop.left).presheaf.obj (op (S.diagram.slicePre U A.unop))
  map {_ _} g := ↾fun t ↦ S.pushRes g.unop.left (S.stageOpen_le U g.unop) t
  map_id A := by
    refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
    simp only [TypeCat.ofHom_apply, ConcreteCategory.id_apply]
    refine S.section_ext _ _ _ fun y hy ↦ ?_
    refine Eq.trans (S.germ_pushRes _ (S.stageOpen_le U (𝟙 A.unop)) t y hy
      (S.stageOpen_le U (𝟙 A.unop) hy)) ?_
    exact S.germ_push_id t y (S.stageOpen_le U (𝟙 A.unop) hy) hy
  map_comp {_ _ _} g g' := by
    refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
    simp only [TypeCat.ofHom_apply, ConcreteCategory.comp_apply]
    exact (S.pushRes_pushRes g'.unop.left g.unop.left (S.stageOpen_le U g.unop)
      (S.stageOpen_le U g'.unop) (S.stageOpen_le U (g'.unop ≫ g.unop)) t).symm

/-- The transition map of the stage diagram is `pushRes`. -/
@[simp]
lemma stageFunctor_map {A A' : (Over i)ᵒᵖ} (g : A ⟶ A')
    (t : (S.stageFunctor U).obj A) :
    (S.stageFunctor U).map g t = S.pushRes g.unop.left (S.stageOpen_le U g.unop) t := rfl

/-- The germ-model image in `p_j⁻¹F_j` over `p_i⁻¹U` of a stage section `t ∈ F_j(f_a⁻¹U)`. -/
def stageToPullback (A : Over i) (t : (S.stageFunctor U).obj (op A)) :
    (S.pullback A.left).presheaf.obj (op (S.diagram.comapProj i U)) :=
  GermPullback.ofSection (S.projFun_mem_stageOpen U A) t

/-- **The compatibility making the stage sections a cocone.**  Transporting a stage section along
a morphism of stages and then taking germs agrees with taking germs and then applying the
transition map of the pullback system. -/
lemma pullbackMap_stageToPullback {A A' : Over i} (g : A' ⟶ A)
    (t : (S.stageFunctor U).obj (op A)) :
    S.pullbackMap g.left (S.stageToPullback U A t) =
      S.stageToPullback U A' (S.pushRes g.left (S.stageOpen_le U g) t) := by
  refine GermPullback.ext fun z ↦ ?_
  have hA : S.diagram.projFun A.left z.1 ∈ S.diagram.slicePre U A := S.projFun_mem_stageOpen U A z
  have hA' : S.diagram.projFun A'.left z.1 ∈ S.diagram.slicePre U A' :=
    S.projFun_mem_stageOpen U A' z
  have hmap : S.diagram.mapFun g.left (S.diagram.projFun A'.left z.1) ∈ S.diagram.slicePre U A := by
    rw [S.diagram.mem_slicePre, ← S.diagram.projFun_eq_mapFun g.left z.1]
    exact hA
  rw [S.pullbackMap_val_of_germ g.left (S.stageToPullback U A t) z hA t
    (GermPullback.ofSection_val _ _ z) hmap]
  refine Eq.trans ?_ (GermPullback.ofSection_val (S.projFun_mem_stageOpen U A')
    (S.pushRes g.left (S.stageOpen_le U g) t) z).symm
  exact germs_mk_congr (S.germ_pushRes g.left (S.stageOpen_le U g) t _ hA' hmap).symm

/-- The image of a stage section in `F(p_i⁻¹U)`: take germs into `p_j⁻¹F_j`, inject into the
colimit presheaf, then apply the canonical map of Stacks 009F. -/
def stageToColimit (A : Over i) (t : (S.stageFunctor U).obj (op A)) :
    (S.colimitPullback).obj.obj (op (S.diagram.comapProj i U)) :=
  DirectedColimitOfSheaves.canonicalMap S.pullbackSystem (S.diagram.comapProj i U)
    ((colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem) (op A.left)).app
      (op (S.diagram.comapProj i U)) (S.stageToPullback U A t))

/-- `stageToColimit` is constant on the stage diagram: this is `pullbackMap_stageToPullback`
followed by the compatibility `colimit.w` of the colimit injections. -/
lemma stageToColimit_map {A A' : Over i} (g : A' ⟶ A) (t : (S.stageFunctor U).obj (op A)) :
    S.stageToColimit U A' (S.pushRes g.left (S.stageOpen_le U g) t) =
      S.stageToColimit U A t := by
  have hw := congrArg (fun (η : (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem).obj
        (op A.left) ⟶ colimit (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)) ↦
      (η.app (op (S.diagram.comapProj i U))) (S.stageToPullback U A t))
    (colimit.w (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
      (show (op A.left : Jᵒᵖ) ⟶ op A'.left from (g.left).op))
  refine Eq.trans ?_ (congrArg (DirectedColimitOfSheaves.canonicalMap S.pullbackSystem
    (S.diagram.comapProj i U)) hw)
  refine congrArg (DirectedColimitOfSheaves.canonicalMap S.pullbackSystem
    (S.diagram.comapProj i U)) ?_
  refine congrArg ((colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
    (op A'.left)).app (op (S.diagram.comapProj i U))) ?_
  exact (S.pullbackMap_stageToPullback U g t).symm

/-- The cocone on the stage diagram with vertex `F(p_i⁻¹U)`. -/
def stageCocone : Cocone (S.stageFunctor U) where
  pt := (S.colimitPullback).obj.obj (op (S.diagram.comapProj i U))
  ι :=
    { app := fun A ↦ ↾fun t ↦ S.stageToColimit U A.unop t
      naturality := fun A A' g ↦ by
        refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
        simp only [TypeCat.ofHom_apply, ConcreteCategory.comp_apply,
          Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.id_apply,
          S.stageFunctor_map U]
        exact S.stageToColimit_map U g.unop t }

/-- **The canonical map of Stacks 0A33**, `colim_{a : j → i} F_j(f_a⁻¹U) → F(p_i⁻¹U)`. -/
@[stacks 0A33 "the canonical map"]
def stageColimitMap [UnivLE.{max v v', max v u}] : colimit (S.stageFunctor U) ⟶
    (S.colimitPullback).obj.obj (op (S.diagram.comapProj i U)) :=
  colimit.desc (S.stageFunctor U) (S.stageCocone U)

/-- The canonical map of 0A33 on the image of a stage section is `stageToColimit`. -/
@[simp]
lemma stageColimitMap_ι [UnivLE.{max v v', max v u}]
    (A : Over i) (t : (S.stageFunctor U).obj (op A)) :
    S.stageColimitMap U (colimit.ι (S.stageFunctor U) (op A) t) =
      S.stageToColimit U A t :=
  congrFun (congrArg (fun h ↦ (ConcreteCategory.hom h : _ → _))
    (colimit.ι_desc (S.stageCocone U) (op A))) t

/-- A stage open `f_a⁻¹U` is quasi-compact when `U` is, because the transition maps of the
diagram are spectral.  This is the hypothesis under which Stacks 0A32 applies at the stage. -/
lemma isCompact_stageOpen (hU : IsCompact (U : Set (S.diagram.F.obj i))) (A : Over i) :
    IsCompact ((S.diagram.slicePre U A : Opens (S.diagram.F.obj A.left)) :
      Set (S.diagram.F.obj A.left)) :=
  (S.isSpectralMap A.hom).isCompact_preimage_of_isOpen U.isOpen hU

/-- **The injectivity step of Stacks 0A33 at a single stage.**  Two sections of `F_j` over the
stage open `f_a⁻¹U` whose germ-sections over `p_i⁻¹U` agree become equal after passing to a
later stage.  This is `exists_stage_push_eq` — the Stacks 0A2W argument — read through the
identification `p_i⁻¹U = p_j⁻¹(f_a⁻¹U)`. -/
lemma exists_stage_pushRes_eq (hU : IsCompact (U : Set (S.diagram.F.obj i))) (A : Over i)
    (s t : (S.stageFunctor U).obj (op A))
    (h : S.stageToPullback U A s = S.stageToPullback U A t) :
    ∃ (m : J) (c : m ⟶ A.left), S.push c s = S.push c t := by
  refine S.exists_stage_push_eq (S.diagram.slicePre U A) (S.isCompact_stageOpen U hU A) s t ?_
  intro x hx
  have hz : x ∈ S.diagram.comapProj i U := by
    rw [S.diagram.mem_comapProj, S.diagram.projFun_eq_mapFun A.hom x]; exact hx
  have hval := congrArg (fun ρ ↦ ρ.1 ⟨x, hz⟩) h
  simp only [stageToPullback] at hval
  exact germs_snd_eq hval

/-- `comapProj` and the `limPre` of `PullbackSections` are the same open of the limit; this is
what lets Stacks 0A32, stated in terms of `limPre`, be applied at a stage. -/
lemma comapProj_eq_limPre {j : J} (V : Opens (S.diagram.F.obj j)) :
    S.diagram.comapProj j V = S.diagram.limPre V := by
  ext x
  exact Iff.rfl

/-- **0A32 applies at every stage.**  The target of the canonical map of Stacks 0A32 for the
sheaf `F_j` and the stage open `f_a⁻¹U` is the sections of `p_j⁻¹F_j` over `p_i⁻¹U`, which is
where the germ-images of the stage sections live. -/
lemma limPre_stageOpen (A : Over i) :
    S.diagram.limPre (S.diagram.slicePre U A) = S.diagram.comapProj i U := by
  rw [← S.comapProj_eq_limPre, S.comapProj_stageOpen U A]

/-- Transport a section of `p_j⁻¹F_j` from `p_i⁻¹U` to `p_j⁻¹(f_a⁻¹U)`, these being the same
open of the limit (`limPre_stageOpen`).  The transport is needed because the two descriptions are
equal only propositionally, through `projFun_eq_mapFun`. -/
def toLimPre (A : Over i)
    (ρ : (S.pullback A.left).presheaf.obj (op (S.diagram.comapProj i U))) :
    (S.pullback A.left).presheaf.obj (op (S.diagram.limPre (S.diagram.slicePre U A))) :=
  (S.pullback A.left).presheaf.map (eqToHom (congrArg op (S.limPre_stageOpen U A).symm)) ρ

/-- The transport does not move the values of a section: at a point of the limit the germ is
unchanged. -/
lemma toLimPre_val (A : Over i)
    (ρ : (S.pullback A.left).presheaf.obj (op (S.diagram.comapProj i U)))
    (z : S.diagram.limPre (S.diagram.slicePre U A)) :
    (S.toLimPre U A ρ).1 z =
      ρ.1 ⟨z.1, by
        have : S.diagram.projFun A.left z.1 ∈ S.diagram.slicePre U A := z.2
        rw [S.diagram.mem_comapProj]
        rw [S.diagram.projFun_eq_mapFun A.hom z.1]
        exact this⟩ := by
  simp only [toLimPre]
  exact GermPullback.val_map_apply _ ρ z

/-- Moving a section along a transition of the pullback system does not change its class in the
colimit.  This is `colimit.w`, read on sections over a fixed open. -/
lemma ι_pullbackMap {j k : J} (b : k ⟶ j) (W : Opens S.diagram.invLimit)
    (ρ : (S.pullback j).presheaf.obj (op W)) :
    (colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
        (op k)).app (op W) (S.pullbackMap b ρ) =
      (colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
        (op j)).app (op W) ρ := by
  have hw := colimit.w (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem) b.op
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hw (op W)) ρ

/-- Iterating the stage-open construction composes the stages: `f_c⁻¹(f_a⁻¹U) = f_{c ≫ a}⁻¹U`.
Proved by membership through `mapFun_comp`, so no transport of sections is needed. -/
lemma slicePre_slicePre (A : Over i) (B : Over A.left) :
    S.diagram.slicePre (S.diagram.slicePre U A) B =
      S.diagram.slicePre U (Over.mk (B.hom ≫ A.hom)) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, S.diagram.mem_slicePre, S.diagram.mem_slicePre,
    S.diagram.mem_slicePre]
  simp [S.diagram.mapFun_comp]

/-- Transport a stage section along the composition identity `f_c⁻¹(f_a⁻¹U) = f_{c ≫ a}⁻¹U`. -/
def stageRecast {A : Over i} (B : Over A.left)
    (t : (S.E.obj B.left).presheaf.obj (op (S.diagram.slicePre (S.diagram.slicePre U A) B))) :
    (S.stageFunctor U).obj (op (Over.mk (B.hom ≫ A.hom))) :=
  (S.E.obj B.left).presheaf.map
    (eqToHom (congrArg op (S.slicePre_slicePre U A B))) t

/-- The recast section has the same germs as the original. -/
lemma germ_stageRecast {A : Over i} (B : Over A.left)
    (t : (S.E.obj B.left).presheaf.obj (op (S.diagram.slicePre (S.diagram.slicePre U A) B)))
    (y : S.diagram.F.obj B.left)
    (hy : y ∈ S.diagram.slicePre U (Over.mk (B.hom ≫ A.hom)))
    (hy' : y ∈ S.diagram.slicePre (S.diagram.slicePre U A) B) :
    (S.E.obj B.left).presheaf.germ _ y hy (S.stageRecast U B t) =
      (S.E.obj B.left).presheaf.germ _ y hy' t := by
  simp only [stageRecast]
  exact (S.E.obj B.left).presheaf.germ_res_apply _ y hy t

/-! ### Injectivity of the canonical map of Stacks 0A33 -/

/-- The transition map of the presheaf system underlying `pullbackSystem` is `pullbackMap`. -/
lemma presheafSystem_map_app {A B : Jᵒᵖ} (α : A ⟶ B) (W : Opens S.diagram.invLimit)
    (σ : (S.pullback A.unop).presheaf.obj (op W)) :
    ((DirectedColimitOfSheaves.presheafSystem S.pullbackSystem).map α).app (op W) σ =
      S.pullbackMap α.unop σ := rfl

/-- The class of a stage section in the colimit is unchanged by transporting it further down the
slice.  This is `colimit.w` for `stageFunctor`. -/
lemma stageColimit_ι_map [UnivLE.{max v v', max v u}]
    (A B : (Over i)ᵒᵖ) (g : A ⟶ B) (s : (S.stageFunctor U).obj A) :
    colimit.ι (S.stageFunctor U) B ((S.stageFunctor U).map g s) =
      colimit.ι (S.stageFunctor U) A s := by
  rw [← ConcreteCategory.comp_apply, colimit.w]

/-- The class in the colimit of a stage section is unchanged by transporting it along a morphism
of stages, written with `pushRes` rather than with the transition map of `stageFunctor`.  The two
are definitionally equal, but the `pushRes` form is the one the germ lemmas produce. -/
lemma stageColimit_ι_pushRes [UnivLE.{max v v', max v u}]
    {A A' : Over i} (g : A' ⟶ A) (s : (S.stageFunctor U).obj (op A)) :
    colimit.ι (S.stageFunctor U) (op A') (S.pushRes g.left (S.stageOpen_le U g) s) =
      colimit.ι (S.stageFunctor U) (op A) s := by
  have h := S.stageColimit_ι_map U (op A) (op A') g.op s
  rwa [S.stageFunctor_map U] at h

/-- Two sections that the `f_a`-map identifies are identified by the `f_a`-map followed by a
restriction. -/
lemma pushRes_congr {j k : J} (a : k ⟶ j) {V : Opens (S.diagram.F.obj j)}
    {V' : Opens (S.diagram.F.obj k)} (hV' : V' ≤ (Opens.map (S.diagram.F.map a)).obj V)
    {s t : (S.E.obj j).presheaf.obj (op V)} (h : S.push a s = S.push a t) :
    S.pushRes a hV' s = S.pushRes a hV' t :=
  congrArg (fun x ↦ (S.E.obj k).presheaf.map (homOfLE hV').op x) h

/-- **The injectivity step of Stacks 0A33.**  Two sections of `F_j` over the stage open `f_a⁻¹U`
with the same image in `F(p_i⁻¹U)` already have the same class in `colim_{a : j → i} F_j(f_a⁻¹U)`.

Injectivity of the canonical map of Stacks 009F moves the hypothesis into the colimit of the
pullback system, where equality of two classes means that some transition map already identifies
the two germ-sections; that transition map is a stage of the slice, and there
`exists_stage_pushRes_eq` — the Stacks 0A2W argument — equalises the two sections themselves. -/
lemma colimit_ι_eq_of_stageToColimit_eq [UnivLE.{max v v', max v u}]
    (hU : IsCompact (U : Set (S.diagram.F.obj i)))
    (A : Over i) (s t : (S.stageFunctor U).obj (op A))
    (h : S.stageToColimit U A s = S.stageToColimit U A t) :
    colimit.ι (S.stageFunctor U) (op A) s = colimit.ι (S.stageFunctor U) (op A) t := by
  obtain ⟨M, β, hβ⟩ := (DirectedColimitOfSheaves.colimit_eq_iff_eventual S.pullbackSystem
    (S.diagram.comapProj i U) (op A.left) (S.stageToPullback U A s)
    (S.stageToPullback U A t)).mp ((S.bijective_colimitCanonicalMap U hU).injective h)
  have hβ' : S.pullbackMap β.unop (S.stageToPullback U A s) =
      S.pullbackMap β.unop (S.stageToPullback U A t) := hβ
  -- The stage of the slice at which the two germ-sections agree.
  obtain ⟨B, g, hB⟩ : Σ' (B : Over i) (g : B ⟶ A),
      S.pullbackMap g.left (S.stageToPullback U A s) =
        S.pullbackMap g.left (S.stageToPullback U A t) :=
    ⟨Over.mk (β.unop ≫ A.hom), Over.homMk β.unop, hβ'⟩
  have hstep : S.stageToPullback U B (S.pushRes g.left (S.stageOpen_le U g) s) =
      S.stageToPullback U B (S.pushRes g.left (S.stageOpen_le U g) t) :=
    (S.pullbackMap_stageToPullback U g s).symm.trans
      (hB.trans (S.pullbackMap_stageToPullback U g t))
  -- The Stacks 0A2W argument at that stage.
  obtain ⟨m, c, hc⟩ := S.exists_stage_pushRes_eq U hU B _ _ hstep
  obtain ⟨C, g₁, hc'⟩ : Σ' (C : Over i) (g₁ : C ⟶ B),
      S.push g₁.left (S.pushRes g.left (S.stageOpen_le U g) s) =
        S.push g₁.left (S.pushRes g.left (S.stageOpen_le U g) t) :=
    ⟨Over.mk (c ≫ B.hom), Over.homMk c, hc⟩
  calc colimit.ι (S.stageFunctor U) (op A) s
      = colimit.ι (S.stageFunctor U) (op B) (S.pushRes g.left (S.stageOpen_le U g) s) :=
        (S.stageColimit_ι_pushRes U g s).symm
    _ = colimit.ι (S.stageFunctor U) (op C) (S.pushRes g₁.left (S.stageOpen_le U g₁)
          (S.pushRes g.left (S.stageOpen_le U g) s)) :=
        (S.stageColimit_ι_pushRes U g₁ _).symm
    _ = colimit.ι (S.stageFunctor U) (op C) (S.pushRes g₁.left (S.stageOpen_le U g₁)
          (S.pushRes g.left (S.stageOpen_le U g) t)) :=
        congrArg (fun x ↦ colimit.ι (S.stageFunctor U) (op C) x)
          (S.pushRes_congr g₁.left (S.stageOpen_le U g₁) hc')
    _ = colimit.ι (S.stageFunctor U) (op B) (S.pushRes g.left (S.stageOpen_le U g) t) :=
        S.stageColimit_ι_pushRes U g₁ _
    _ = colimit.ι (S.stageFunctor U) (op A) t := S.stageColimit_ι_pushRes U g t

/-- **Stacks 0A33, injectivity.**  Any two elements of `colim_{a : j → i} F_j(f_a⁻¹U)` are
represented at a common stage of the slice, where `colimit_ι_eq_of_stageToColimit_eq` applies. -/
theorem injective_stageColimitMap [UnivLE.{max v v', max v u}]
    (hU : IsCompact (U : Set (S.diagram.F.obj i))) :
    Function.Injective (S.stageColimitMap U) := by
  intro p q hpq
  obtain ⟨A₁, s₁, h₁⟩ :=
    Types.jointly_surjective_of_isColimit (colimit.isColimit (S.stageFunctor U)) p
  obtain ⟨A₂, s₂, h₂⟩ :=
    Types.jointly_surjective_of_isColimit (colimit.isColimit (S.stageFunctor U)) q
  have hp : colimit.ι (S.stageFunctor U) (IsFiltered.max A₁ A₂)
      ((S.stageFunctor U).map (IsFiltered.leftToMax A₁ A₂) s₁) = p :=
    (S.stageColimit_ι_map U _ _ _ s₁).trans h₁
  have hq : colimit.ι (S.stageFunctor U) (IsFiltered.max A₁ A₂)
      ((S.stageFunctor U).map (IsFiltered.rightToMax A₁ A₂) s₂) = q :=
    (S.stageColimit_ι_map U _ _ _ s₂).trans h₂
  have hcolim : S.stageToColimit U (IsFiltered.max A₁ A₂).unop
        ((S.stageFunctor U).map (IsFiltered.leftToMax A₁ A₂) s₁) =
      S.stageToColimit U (IsFiltered.max A₁ A₂).unop
        ((S.stageFunctor U).map (IsFiltered.rightToMax A₁ A₂) s₂) := by
    rw [← S.stageColimitMap_ι U, ← S.stageColimitMap_ι U, hp, hq]
    exact hpq
  rw [← hp, ← hq]
  exact S.colimit_ι_eq_of_stageToColimit_eq U hU _ _ _ hcolim

/-! ### Surjectivity of the canonical map of Stacks 0A33 -/

/-- **The descent step of Stacks 0A33.**  Let `ρ` be a section of `p_j⁻¹F_j` over `p_i⁻¹U`, let
`σ` be the section of `f_b⁻¹F_j` over `f_{b ∘ a}⁻¹U` that Stacks 0A32 produces from it, and let
`t` be the section of `F_k` that `exists_adj` descends `σ` to.  Then the germ-section of
`p_k⁻¹F_k` determined by `t` is the image of `ρ` under the transition map of the pullback
system. -/
lemma stageToPullback_stageRecast {A : Over i} (B : Over A.left)
    (t : (S.E.obj B.left).presheaf.obj (op (S.diagram.slicePre (S.diagram.slicePre U A) B)))
    (σ : (GermPullback.sheaf (S.diagram.mapFun B.hom) (S.E.obj A.left).presheaf).presheaf.obj
      (op (S.diagram.slicePre (S.diagram.slicePre U A) B)))
    (ρ : (S.pullback A.left).presheaf.obj (op (S.diagram.comapProj i U)))
    (ht : ∀ (y : S.diagram.F.obj B.left)
        (hy : y ∈ S.diagram.slicePre (S.diagram.slicePre U A) B),
      (⟨y, (S.E.obj B.left).presheaf.germ _ y hy t⟩ :
          GermPullback.Germs (S.E.obj B.left).presheaf) =
        S.pushGerm B.hom y (σ.1 ⟨y, hy⟩) (germs_fst σ ⟨y, hy⟩))
    (hσ : S.diagram.toLim (S.diagram.slicePre U A) (S.sheafAt A.left) B σ = S.toLimPre U A ρ) :
    S.stageToPullback U (Over.mk (B.hom ≫ A.hom)) (S.stageRecast U B t) =
      S.pullbackMap B.hom ρ := by
  refine GermPullback.ext fun z ↦ ?_
  have hz : z.1 ∈ S.diagram.limPre (S.diagram.slicePre U A) := S.projFun_mem_stageOpen U A z
  have hy' : S.diagram.projFun B.left z.1 ∈ S.diagram.slicePre (S.diagram.slicePre U A) B :=
    S.diagram.proj_mem (S.diagram.slicePre U A) (A := B) ⟨z.1, hz⟩
  -- The two sections take the same value at `z`, because `σ` computes `ρ` over the limit.
  have hval : σ.1 ⟨S.diagram.projFun B.left z.1, hy'⟩ = ρ.1 z :=
    congrArg (fun τ ↦ τ.1 ⟨z.1, hz⟩) hσ
  have hgerm : (S.stageToPullback U (Over.mk (B.hom ≫ A.hom)) (S.stageRecast U B t)).1 z =
      (⟨S.diagram.projFun B.left z.1, (S.E.obj B.left).presheaf.germ _ _ hy' t⟩ :
        GermPullback.Germs (S.E.obj B.left).presheaf) :=
    germs_mk_congr (S.germ_stageRecast U B t (S.diagram.projFun B.left z.1)
      (S.projFun_mem_stageOpen U (Over.mk (B.hom ≫ A.hom)) z) hy')
  refine hgerm.trans ((ht (S.diagram.projFun B.left z.1) hy').trans ?_)
  exact S.pushGerm_congr B.hom (S.diagram.projFun B.left z.1) hval _ _

/-- `stageToColimit` unwound: the germ-section of the stage section, injected into the colimit of
the pullback system and then pushed into the sheafification. -/
lemma stageToColimit_eq (A : Over i) (t : (S.stageFunctor U).obj (op A)) :
    S.stageToColimit U A t =
      DirectedColimitOfSheaves.canonicalMap S.pullbackSystem (S.diagram.comapProj i U)
        ((colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
          (op A.left)).app (op (S.diagram.comapProj i U)) (S.stageToPullback U A t)) := rfl

/-- The image in `F(p_i⁻¹U)` of the descended stage section of `stageToPullback_stageRecast` is
the image of the class of `ρ` under the canonical map of Stacks 009F. -/
lemma stageToColimit_stageRecast {A : Over i} (B : Over A.left)
    (t : (S.E.obj B.left).presheaf.obj (op (S.diagram.slicePre (S.diagram.slicePre U A) B)))
    (σ : (GermPullback.sheaf (S.diagram.mapFun B.hom) (S.E.obj A.left).presheaf).presheaf.obj
      (op (S.diagram.slicePre (S.diagram.slicePre U A) B)))
    (ρ : (S.pullback A.left).presheaf.obj (op (S.diagram.comapProj i U)))
    (ht : ∀ (y : S.diagram.F.obj B.left)
        (hy : y ∈ S.diagram.slicePre (S.diagram.slicePre U A) B),
      (⟨y, (S.E.obj B.left).presheaf.germ _ y hy t⟩ :
          GermPullback.Germs (S.E.obj B.left).presheaf) =
        S.pushGerm B.hom y (σ.1 ⟨y, hy⟩) (germs_fst σ ⟨y, hy⟩))
    (hσ : S.diagram.toLim (S.diagram.slicePre U A) (S.sheafAt A.left) B σ = S.toLimPre U A ρ) :
    S.stageToColimit U (Over.mk (B.hom ≫ A.hom)) (S.stageRecast U B t) =
      DirectedColimitOfSheaves.canonicalMap S.pullbackSystem (S.diagram.comapProj i U)
        ((colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
          (op A.left)).app (op (S.diagram.comapProj i U)) ρ) := by
  refine (S.stageToColimit_eq U (Over.mk (B.hom ≫ A.hom)) (S.stageRecast U B t)).trans ?_
  refine congrArg (fun ζ ↦ DirectedColimitOfSheaves.canonicalMap S.pullbackSystem
    (S.diagram.comapProj i U) ζ) ?_
  refine Eq.trans ?_ (S.ι_pullbackMap B.hom (S.diagram.comapProj i U) ρ)
  exact congrArg (fun ζ ↦ (colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
    (op B.left)).app (op (S.diagram.comapProj i U)) ζ)
    (S.stageToPullback_stageRecast U B t σ ρ ht hσ)

/-- **Stacks 0A33, surjectivity.**  This is the source's own argument.  Stacks 009F (4), in the
form `bijective_colimitCanonicalMap`, writes a section of `F` over `p_i⁻¹U` as the class of a
section `ρ` of `p_j⁻¹F_j` for a single `j`; a stage `a : k ⟶ i` below both `j` and `i` turns
`p_i⁻¹U` into `p_k⁻¹(f_a⁻¹U)`, with `f_a⁻¹U` quasi-compact because the transition maps are
spectral.  Stacks 0A32, applied to the sheaf `F_k` and that open, writes the transported `ρ` as
the class of a section of `f_b⁻¹F_k`, and `exists_adj` descends the latter to a section of
`F_{k'}` over `f_{b ∘ a}⁻¹U` — an element of the left-hand side mapping to the given section. -/
theorem surjective_stageColimitMap [UnivLE.{max v v', max v u}]
    (hU : IsCompact (U : Set (S.diagram.F.obj i))) :
    Function.Surjective (S.stageColimitMap U) := by
  intro ξ
  -- Stacks 009F (4): `ξ` is the class of a section of some `p_j⁻¹F_j` over `p_i⁻¹U`.
  obtain ⟨η, hη⟩ := (S.bijective_colimitCanonicalMap U hU).surjective ξ
  obtain ⟨K, ρ₀, -, hρ₀, -⟩ := DirectedColimitOfSheaves.exists_common_index S.pullbackSystem
    (S.diagram.comapProj i U) η η
  -- A stage `A : Over i` below both `K.unop` and `i`.
  obtain ⟨A, b⟩ : Σ' A : Over i, A.left ⟶ K.unop :=
    ⟨Over.mk (IsCofiltered.minToRight K.unop i), IsCofiltered.minToLeft K.unop i⟩
  have hι : (colimit.ι (DirectedColimitOfSheaves.presheafSystem S.pullbackSystem)
      (op A.left)).app (op (S.diagram.comapProj i U)) (S.pullbackMap b ρ₀) = η :=
    (S.ι_pullbackMap b (S.diagram.comapProj i U) ρ₀).trans hρ₀
  -- Stacks 0A32 for the sheaf `F_{A.left}` and the quasi-compact open `f_{A.hom}⁻¹U`.
  obtain ⟨p, hp⟩ := S.diagram.surjective_canonicalMap (S.diagram.slicePre U A) (S.sheafAt A.left)
    (S.isCompact_stageOpen U hU A) (S.toLimPre U A (S.pullbackMap b ρ₀))
  obtain ⟨B, σ, hσ⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (S.diagram.sliceFunctor (S.diagram.slicePre U A) (S.sheafAt A.left))) p
  have hσ' : colimit.ι (S.diagram.sliceFunctor (S.diagram.slicePre U A) (S.sheafAt A.left)) B σ
      = p := hσ
  have htoLim : S.diagram.toLim (S.diagram.slicePre U A) (S.sheafAt A.left) B.unop σ =
      S.toLimPre U A (S.pullbackMap b ρ₀) :=
    (S.diagram.canonicalMap_ι (S.diagram.slicePre U A) (S.sheafAt A.left) B σ).symm.trans
      (by rw [hσ']; exact hp)
  -- The adjunction map: `σ` comes from a section of `F_{B.unop.left}`.
  obtain ⟨t, ht⟩ := S.exists_adj B.unop.hom σ
  refine ⟨colimit.ι (S.stageFunctor U) (op (Over.mk (B.unop.hom ≫ A.hom)))
    (S.stageRecast U B.unop t), ?_⟩
  refine (S.stageColimitMap_ι U (Over.mk (B.unop.hom ≫ A.hom)) (S.stageRecast U B.unop t)).trans ?_
  refine (S.stageToColimit_stageRecast U B.unop t σ (S.pullbackMap b ρ₀) ht htoLim).trans ?_
  exact (congrArg (fun ζ ↦ DirectedColimitOfSheaves.canonicalMap S.pullbackSystem
    (S.diagram.comapProj i U) ζ) hι).trans hη

/-- **Stacks 0A33.**  Let `J` be a cofiltered index category, `j ↦ X_j` a diagram of spectral
spaces with spectral transition maps, `F_j` a sheaf of sets on `X_j` for each `j` together with a
compatible system of `f_a`-maps, and `F = colim_j p_j⁻¹F_j` on the limit `X = lim_j X_j`.  Then for
every `i` and every quasi-compact open `U ⊆ X_i` the canonical map
`colim_{a : j → i} F_j(f_a⁻¹U) → F(p_i⁻¹U)`
is bijective. -/
@[stacks 0A33]
theorem bijective_stageColimitMap [UnivLE.{max v v', max v u}]
    (hU : IsCompact (U : Set (S.diagram.F.obj i))) :
    Function.Bijective (S.stageColimitMap U) :=
  ⟨S.injective_stageColimitMap U hU, S.surjective_stageColimitMap U hU⟩

end StageSections

end SpectralSheafSystem

end
