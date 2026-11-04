module

public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Relative gluing of schemes over a basis of the topology of the base

Let `S` be a scheme and `B` a basis for its topology. Suppose given, for every `U ∈ B`, a scheme
`X U` over `U`, and for every inclusion `V ⊆ U` of members of `B` a morphism `ρ : X V ⟶ X U`
over `S` which identifies `X V` with the part of `X U` lying over `V`, these morphisms being
compatible with composition of inclusions. Then the `X U` glue: there is a scheme `X` over `S`,
unique up to unique isomorphism over `S`, whose part over each `U ∈ B` is `X U` compatibly with
the `ρ`.

This is Stacks 01LH.

## Main definitions

* `AlgebraicGeometry.Scheme.basisCover`: the open cover of `S` by the members of a basis of its
  topology, directed by inclusion.
* `AlgebraicGeometry.Scheme.BasisGluingData`: the gluing datum of Stacks 01LH — the family
  `X U ⟶ U` together with the restriction morphisms and their two properties.
* `AlgebraicGeometry.Scheme.BasisGluingData.Gluing`: a solution of the gluing problem posed by
  such a datum: a scheme over `S` together with charts identifying its part over each `U ∈ B`
  with `X U`.
* `AlgebraicGeometry.Scheme.BasisGluingData.gluing`: the solution produced by gluing.

## Main results

* `AlgebraicGeometry.Scheme.BasisGluingData.exists_isPullback_res_comp`: **Stacks 01LH,
  existence.** The glued scheme exists.
* `AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_isoOver`: **Stacks 01LH, uniqueness.**
  Two solutions are uniquely isomorphic over `S`.

## Implementation notes

The construction is not redone here: it is Mathlib's
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, which glues a family of schemes indexed by
a *locally directed* open cover of `S` — a cover whose index type is a category, with transition
maps along the morphisms, such that the pairwise fibre products of the cover are covered by its
own members. What this file supplies is the translation between that presentation and the
presentation of the source, together with the uniqueness clause, which Mathlib does not state.

* The index category. A basis `B` of the topology of `S`, ordered by inclusion, is an open cover
  of `S`: this is `AlgebraicGeometry.Scheme.basisCover`. The basis that Stacks 02W3 feeds to this
  lemma is the affine opens, `AlgebraicGeometry.Scheme.isBasis_affineOpens`. It is locally
  directed by
  `AlgebraicGeometry.Scheme.Cover.LocallyDirected.ofIsBasisOpensRange`, whose hypothesis — that
  the images of the members of the cover form a basis — holds by construction. The transition
  map along `V ≤ U` is `AlgebraicGeometry.Scheme.homOfLE`.
* The datum. Mathlib asks for a functor `B ⥤ Scheme` together with an *equifibered* natural
  transformation to the cover, i.e. one all of whose naturality squares are Cartesian. The
  functor is the family `X` with the restriction morphisms as its action on morphisms, so
  functoriality is exactly the cocycle condition of the source together with `ρ^U_U = 𝟙`; and
  the squares being Cartesian is exactly the condition that `ρ^U_V` identify `X V` with the part
  of `X U` over `V`. The identity `ρ^U_U = 𝟙` is *not* assumed: the source does not assume it,
  and it follows, since the Cartesian square for `U ≤ U` makes `ρ^U_U` a split epimorphism while
  the cocycle condition makes it idempotent
  (`AlgebraicGeometry.Scheme.BasisGluingData.res_self`).
* The conclusion. Mathlib's `isPullback_natTrans_ι_toBase` says that `X U`, with its structure
  morphism to `U` and its chart into the glued scheme, is the fibre product `X ×_S U`, which is
  the assertion that the chart identifies `X U` with the part of the glued scheme over `U`; and
  the compatibility of the charts with the restriction morphisms is naturality of the colimit
  inclusions.
* Uniqueness. The charts of a solution are open immersions, being base changes of the inclusions
  of the members of `B`, and they cover the solution because `B` covers `S`; so they form an
  open cover of it. That cover is again locally directed, this time *not* because its images
  form a basis — the preimages of the members of `B` need not be a basis of the topology of the
  glued scheme — but directly: two charts meet over the part lying above `U ⊓ V`, which is
  covered by the members of `B` inside `U ⊓ V`. Morphisms out of a locally directed open cover
  glue, so a solution receives a unique morphism to any other solution compatible with the
  charts, and the two morphisms between two solutions are mutually inverse.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-! ### The open cover by the members of a basis of the topology -/

/-- The open cover of `S` by the members of a basis `B` of its topology, indexed by `B` itself. -/
def basisCover (B : Set S.Opens) (hB : Opens.IsBasis B) : S.OpenCover where
  I₀ := B
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp hB (U := ⊤) (Opens.mem_top x)
    exact ⟨⟨V, hV⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

/-- The index type of `basisCover B hB` is `B`. -/
@[simp]
lemma basisCover_I₀ (B : Set S.Opens) (hB : Opens.IsBasis B) :
    (basisCover B hB).I₀ = B := rfl

/-- The morphism of `basisCover B hB` indexed by `U ∈ B` is the open immersion `U ⟶ S`. -/
@[simp]
lemma basisCover_f (B : Set S.Opens) (hB : Opens.IsBasis B) (U : B) :
    (basisCover B hB).f U = U.1.ι := rfl

/-- The index type of `basisCover B hB` is ordered by inclusion of opens. -/
instance (B : Set S.Opens) (hB : Opens.IsBasis B) : Preorder (basisCover B hB).I₀ :=
  inferInstanceAs <| Preorder B

/-- The cover of `S` by the members of a basis, ordered by inclusion, is locally directed, with
transition morphisms the inclusions of opens. -/
instance (B : Set S.Opens) (hB : Opens.IsBasis B) : (basisCover B hB).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp [basisCover]; rfl) <| by
    convert! hB
    simp [basisCover]

/-- The transition morphism of `basisCover B hB` along `U ≤ V` is the inclusion
`S.homOfLE h : U ⟶ V`. -/
@[simp]
lemma basisCover_trans (B : Set S.Opens) (hB : Opens.IsBasis B) {U V : B} (h : U ≤ V) :
    (basisCover B hB).trans (homOfLE h) = S.homOfLE h := rfl

/-! ### The gluing datum -/

/-- A gluing datum over a basis `B` of the topology of `S`, as in Stacks 01LH: a scheme `obj U`
over each `U ∈ B`, and for each inclusion `V ⊆ U` of members of `B` a morphism
`res : obj V ⟶ obj U` which identifies `obj V` with the part of `obj U` over `V`, subject to the
cocycle condition for a chain `W ⊆ V ⊆ U`. -/
structure BasisGluingData (S : Scheme.{u}) (B : Set S.Opens) where
  /-- The scheme living over the member `U` of the basis. -/
  obj : B → Scheme.{u}
  /-- The structure morphism of `obj U`, as a morphism to `U`. -/
  proj (U : B) : obj U ⟶ (U.1 : Scheme.{u})
  /-- The restriction morphism `ρ^U_V` attached to an inclusion `V ⊆ U` of members of `B`. -/
  res {V U : B} (h : V.1 ≤ U.1) : obj V ⟶ obj U
  /-- The restriction morphism identifies `obj V` with the part of `obj U` lying over `V`. -/
  isPullback_res {V U : B} (h : V.1 ≤ U.1) :
    IsPullback (res h) (proj V) (proj U) (S.homOfLE h)
  /-- The cocycle condition: restricting from `U` to `V` and then to `W` is restricting from `U`
  to `W`. -/
  res_trans {W V U : B} (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ U.1) :
    res (hWV.trans hVU) = res hWV ≫ res hVU

namespace BasisGluingData

variable {B : Set S.Opens} (D : BasisGluingData S B)

/-- The restriction morphism along the inclusion of a member of the basis into itself is the
identity.

This is not part of the datum: the Cartesian square for `U ⊆ U` makes `res` a split epimorphism
and the cocycle condition makes it idempotent, which forces it to be the identity. -/
lemma res_self (U : B) (h : U.1 ≤ U.1) : D.res h = 𝟙 _ := by
  have hpb : IsPullback (D.res h) (D.proj U) (D.proj U) (𝟙 (U.1 : Scheme.{u})) :=
    S.homOfLE_rfl U.1 ▸ D.isPullback_res h
  have hl : hpb.lift (𝟙 _) (D.proj U) (by simp) ≫ D.res h = 𝟙 _ := hpb.lift_fst _ _ _
  calc D.res h = (hpb.lift (𝟙 _) (D.proj U) (by simp) ≫ D.res h) ≫ D.res h := by
        rw [hl, Category.id_comp]
    _ = hpb.lift (𝟙 _) (D.proj U) (by simp) ≫ D.res h ≫ D.res h := by rw [Category.assoc]
    _ = hpb.lift (𝟙 _) (D.proj U) (by simp) ≫ D.res h := by rw [← D.res_trans h h]
    _ = 𝟙 _ := hl

/-- Each restriction morphism of a gluing datum is an open immersion. -/
instance isOpenImmersion_res {V U : B} (h : V.1 ≤ U.1) : IsOpenImmersion (D.res h) :=
  MorphismProperty.of_isPullback (D.isPullback_res h).flip inferInstance

/-- The diagram of the pieces of a gluing datum, indexed by the basis ordered by inclusion. -/
def functor (hB : Opens.IsBasis B) : (basisCover B hB).I₀ ⥤ Scheme.{u} where
  obj U := D.obj U
  map {_ _} f := D.res (leOfHom f)
  map_id U := D.res_self U _
  map_comp _ _ := D.res_trans _ _

/-- A gluing datum over a basis of the topology of `S`, read as a relative gluing datum over the
open cover of `S` by the members of that basis. -/
def relativeGluingData (hB : Opens.IsBasis B) : (basisCover B hB).RelativeGluingData where
  functor := D.functor hB
  natTrans :=
    { app := D.proj
      naturality := fun {_ _} f ↦ (D.isPullback_res (leOfHom f)).w }
  equifibered := fun {_ _} f ↦ D.isPullback_res (leOfHom f)

/-- The scheme obtained by gluing the pieces of a gluing datum over a basis. -/
def glued (hB : Opens.IsBasis B) : Scheme.{u} := (D.relativeGluingData hB).glued

/-- The structure morphism of the glued scheme. -/
def toBase (hB : Opens.IsBasis B) : D.glued hB ⟶ S := (D.relativeGluingData hB).toBase

/-- The chart of the glued scheme attached to a member of the basis. -/
def chart (hB : Opens.IsBasis B) (U : B) : D.obj U ⟶ D.glued hB :=
  colimit.ι (D.relativeGluingData hB).functor U

/-- The chart `D.obj U ⟶ D.glued hB` identifies `D.obj U`, with its structure morphism to `U`, with
the fibre product of the glued scheme and `U` over `S`. -/
lemma isPullback_proj_chart (hB : Opens.IsBasis B) (U : B) :
    IsPullback (D.proj U) (D.chart hB U) U.1.ι (D.toBase hB) :=
  (D.relativeGluingData hB).isPullback_natTrans_ι_toBase U

/-- The charts of the glued scheme are compatible with the restriction morphisms. -/
lemma res_comp_chart (hB : Opens.IsBasis B) {V U : B} (h : V.1 ≤ U.1) :
    D.res h ≫ D.chart hB U = D.chart hB V :=
  colimit.w (D.relativeGluingData hB).functor (homOfLE h)

/-! ### Solutions of the gluing problem -/

/-- A solution of the gluing problem posed by a gluing datum `D` over a basis `B` of the topology
of `S`: a scheme over `S` together with, for each `U ∈ B`, a chart identifying `D.obj U` with the
part of it lying over `U`, compatibly with the restriction morphisms of `D`. -/
structure Gluing where
  /-- The underlying scheme. -/
  base : Scheme.{u}
  /-- The structure morphism to `S`. -/
  toBase : base ⟶ S
  /-- The chart attached to a member of the basis. -/
  chart (U : B) : D.obj U ⟶ base
  /-- The chart identifies `D.obj U` with the part of the solution lying over `U`. -/
  isPullback_chart (U : B) : IsPullback (D.proj U) (chart U) U.1.ι toBase
  /-- The charts are compatible with the restriction morphisms. -/
  res_comp_chart {V U : B} (h : V.1 ≤ U.1) : D.res h ≫ chart U = chart V

/-- The solution of the gluing problem produced by gluing. -/
def gluing (hB : Opens.IsBasis B) : D.Gluing where
  base := D.glued hB
  toBase := D.toBase hB
  chart := D.chart hB
  isPullback_chart := D.isPullback_proj_chart hB
  res_comp_chart h := D.res_comp_chart hB h

namespace Gluing

variable {D : BasisGluingData S B} (G : D.Gluing)

/-- Each chart of a solution of the gluing problem is an open immersion. -/
instance isOpenImmersion_chart (U : B) : IsOpenImmersion (G.chart U) :=
  MorphismProperty.of_isPullback (G.isPullback_chart U) inferInstance

/-- A point in the image of the chart attached to `U` lies over `U`. -/
lemma toBase_chart_apply (U : B) (y : D.obj U) : G.toBase ((G.chart U) y) ∈ U.1 := by
  have h : (G.chart U ≫ G.toBase) y = (D.proj U ≫ U.1.ι) y := by
    rw [← (G.isPullback_chart U).w]
  rw [Scheme.Hom.comp_apply] at h
  rw [h]
  exact (D.proj U y).2

/-- The open cover of a solution by its charts. -/
def cover (hB : Opens.IsBasis B) : G.base.OpenCover where
  I₀ := B
  X U := D.obj U
  f U := G.chart U
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstance⟩
    obtain ⟨V, hV, hxV, -⟩ :=
      Opens.isBasis_iff_nbhd.mp hB (U := ⊤) (Opens.mem_top (G.toBase x))
    obtain ⟨y, -, hy⟩ :=
      exists_preimage_of_isPullback (G.isPullback_chart ⟨V, hV⟩) ⟨G.toBase x, hxV⟩ x rfl
    exact ⟨⟨V, hV⟩, ⟨y, hy⟩⟩

/-- The index type of the cover of a solution by its charts is ordered by inclusion of opens. -/
instance (hB : Opens.IsBasis B) : Preorder (G.cover hB).I₀ := inferInstanceAs <| Preorder B

/-- Two charts of a solution meet over the part of the base lying in the intersection of the two
corresponding members of the basis, which is covered by the members of the basis contained in
that intersection. -/
lemma exists_lift_res_eq (hB : Opens.IsBasis B) (i j : B)
    (x : (pullback (G.chart i) (G.chart j)).carrier) :
    ∃ (W : B) (h₁ : W.1 ≤ i.1) (h₂ : W.1 ≤ j.1) (y : D.obj W),
      pullback.lift (D.res h₁) (D.res h₂)
        (by rw [G.res_comp_chart, G.res_comp_chart]) y = x := by
  have hcond : G.chart i (pullback.fst (G.chart i) (G.chart j) x)
      = G.chart j (pullback.snd (G.chart i) (G.chart j) x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hmeet : G.toBase (G.chart i (pullback.fst (G.chart i) (G.chart j) x)) ∈ i.1 ⊓ j.1 := by
    refine ⟨G.toBase_chart_apply i _, ?_⟩
    rw [hcond]
    exact G.toBase_chart_apply j _
  obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp hB hmeet
  obtain ⟨y, -, hy⟩ :=
    exists_preimage_of_isPullback (G.isPullback_chart ⟨W, hW⟩) ⟨_, hxW⟩
      (G.chart i (pullback.fst (G.chart i) (G.chart j) x)) rfl
  refine ⟨⟨W, hW⟩, le_trans hWle inf_le_left, le_trans hWle inf_le_right, y, ?_⟩
  apply (pullback.snd (G.chart i) (G.chart j)).injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  apply (G.chart j).injective
  rw [← Scheme.Hom.comp_apply, G.res_comp_chart, hy, hcond]

/-- The cover of a solution by its charts, ordered by inclusion, is locally directed, with
transition morphisms the restriction morphisms of `D`. -/
instance (hB : Opens.IsBasis B) : (G.cover hB).LocallyDirected where
  trans {_ _} hij := D.res (leOfHom hij)
  trans_id U := D.res_self U _
  trans_comp _ _ := D.res_trans _ _
  w {_ _} hij := G.res_comp_chart (leOfHom hij)
  property_trans {_ _} hij := D.isOpenImmersion_res (leOfHom hij)
  directed {i j} x := by
    obtain ⟨W, h₁, h₂, y, hy⟩ := G.exists_lift_res_eq hB i j x
    exact ⟨W, homOfLE h₁, homOfLE h₂, y, hy⟩

/-- Two morphisms out of a solution agree if they agree after composition with every chart. -/
lemma hom_ext (hB : Opens.IsBasis B) {T : Scheme.{u}} {a b : G.base ⟶ T}
    (h : ∀ U : B, G.chart U ≫ a = G.chart U ≫ b) : a = b :=
  (G.cover hB).hom_ext a b h

/-- The comparison morphism from one solution of a gluing problem to another, obtained by gluing
the charts of the target along the cover of the source by its charts. -/
def desc (hB : Opens.IsBasis B) (G' : D.Gluing) : G.base ⟶ G'.base :=
  (G.cover hB).glueMorphismsOfLocallyDirected G'.chart
    fun {_ _} hij ↦ G'.res_comp_chart (leOfHom hij)

/-- The comparison morphism `G.desc hB G'` carries each chart of `G` to the corresponding chart
of `G'`. -/
@[reassoc (attr := simp)]
lemma chart_comp_desc (hB : Opens.IsBasis B) (G' : D.Gluing) (U : B) :
    G.chart U ≫ G.desc hB G' = G'.chart U :=
  (G.cover hB).map_glueMorphismsOfLocallyDirected G'.chart
    (fun {_ _} hij ↦ G'.res_comp_chart (leOfHom hij)) U

/-- The comparison morphism between two solutions is a morphism over `S`. -/
lemma desc_comp_toBase (hB : Opens.IsBasis B) (G' : D.Gluing) :
    G.desc hB G' ≫ G'.toBase = G.toBase :=
  G.hom_ext hB fun U ↦ by
    rw [← Category.assoc, chart_comp_desc, ← (G'.isPullback_chart U).w,
      ← (G.isPullback_chart U).w]

/-- Two solutions of the same gluing problem are isomorphic over the base. -/
def isoOfGluing (hB : Opens.IsBasis B) (G' : D.Gluing) : G.base ≅ G'.base where
  hom := G.desc hB G'
  inv := G'.desc hB G
  hom_inv_id := G.hom_ext hB fun U ↦ by
    rw [← Category.assoc, chart_comp_desc, chart_comp_desc, Category.comp_id]
  inv_hom_id := G'.hom_ext hB fun U ↦ by
    rw [← Category.assoc, chart_comp_desc, chart_comp_desc, Category.comp_id]

/-- Between two solutions of the same gluing problem there is exactly one isomorphism compatible
with the charts, and it is an isomorphism over the base. -/
theorem existsUnique_isoOfGluing (hB : Opens.IsBasis B) (G' : D.Gluing) :
    ∃! e : G.base ≅ G'.base,
      (∀ U : B, G.chart U ≫ e.hom = G'.chart U) ∧ e.hom ≫ G'.toBase = G.toBase :=
  ⟨G.isoOfGluing hB G', ⟨G.chart_comp_desc hB G', G.desc_comp_toBase hB G'⟩,
    fun _ he ↦ Iso.ext <| G.hom_ext hB fun U ↦ (he.1 U).trans (G.chart_comp_desc hB G' U).symm⟩

end Gluing

/-! ### Existence and uniqueness of the glued scheme -/

/-- Let `S` be a scheme and `B` a basis for its topology. Given a scheme `D.obj U` over `U` for
every `U ∈ B`, together with morphisms `D.res : D.obj V ⟶ D.obj U` for `V ⊆ U` in `B`
identifying `D.obj V` with the part of `D.obj U` over `V` and satisfying the cocycle condition,
there is a morphism of schemes `f : X ⟶ S` and charts `i U : D.obj U ⟶ X` identifying `D.obj U`
with the part of `X` over `U`, compatibly with the restriction morphisms. -/
@[stacks 01LH "existence of the glued scheme, with the charts identifying each piece with the
part of it lying over the corresponding member of the basis"]
theorem exists_isPullback_res_comp (hB : Opens.IsBasis B) (D : BasisGluingData S B) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (i : ∀ U : B, D.obj U ⟶ X),
      (∀ U : B, IsPullback (D.proj U) (i U) U.1.ι f) ∧
        ∀ {V U : B} (h : V.1 ≤ U.1), D.res h ≫ i U = i V :=
  ⟨D.glued hB, D.toBase hB, D.chart hB, D.isPullback_proj_chart hB,
    fun h ↦ D.res_comp_chart hB h⟩

/-- The glued scheme of a gluing datum over a basis of the topology of `S` is unique up to unique
isomorphism over `S`: between any two solutions of the gluing problem there is exactly one
isomorphism compatible with the charts, and it is a morphism over `S`. -/
@[stacks 01LH "the glued scheme is unique up to unique isomorphism over the base"]
theorem existsUnique_isoOver (hB : Opens.IsBasis B) (D : BasisGluingData S B)
    {X X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    {i : ∀ U : B, D.obj U ⟶ X} {i' : ∀ U : B, D.obj U ⟶ X'}
    (hi : ∀ U : B, IsPullback (D.proj U) (i U) U.1.ι f)
    (hi' : ∀ U : B, IsPullback (D.proj U) (i' U) U.1.ι f')
    (hres : ∀ {V U : B} (h : V.1 ≤ U.1), D.res h ≫ i U = i V)
    (hres' : ∀ {V U : B} (h : V.1 ≤ U.1), D.res h ≫ i' U = i' V) :
    ∃! e : X ≅ X', (∀ U : B, i U ≫ e.hom = i' U) ∧ e.hom ≫ f' = f :=
  Gluing.existsUnique_isoOfGluing (D := D) ⟨X, f, i, hi, hres⟩ hB ⟨X', f', i', hi', hres'⟩

end BasisGluingData

end AlgebraicGeometry.Scheme

end
