module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.BaseChangeToTheLimit

/-!
# The germ-model pullback system on the vertex of an abstract cone

`StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian` builds the pullback system
`j ↦ pⱼ⁻¹𝒜ⱼ` on the *concrete* limit `S.invLim` of a spectral diagram, and abelian Stacks 0A33
is stated about it.  The two colimit-comparison clauses of Tag 0A37 are stated about an
*abstract* cone `c` in `SheafedSpace AddCommGrpCat`, whose vertex is characterized only by
`IsLimit c`.  This file builds the same system over such a cone:

* the sheaves `pₖ⁻¹Fₖ` on the space underlying `c.pt`, as germ models along the cone legs;
* the transition maps between them and their functoriality, giving a functor
  `Kᵒᵖ ⥤ c.pt.Sheaf AddCommGrpCat`; and
* the cocone from that functor to the sheaf on the vertex.

Nothing here needs `IsLimit c`: the system and the cocone exist over any cone.  What a limiting
cone adds is that the cocone is a *colimit* cocone, which is
`SheafedSpaceLimit.existsUnique_mapOut_pull_eq` in corepresented form.

## Main definitions

* `SheafedSpaceLimit.pullSheaf`: the germ model `pₖ⁻¹Fₖ` on the space underlying `c.pt`.
* `SheafedSpaceLimit.transUnit` and `SheafedSpaceLimit.trans`: the transition map
  `pᵢ⁻¹Fᵢ ⟶ pⱼ⁻¹Fⱼ` attached to `a : j ⟶ i`, and the map `Fᵢ ⟶ (pᵢ)_* pⱼ⁻¹Fⱼ` adjoint to it.
* `SheafedSpaceLimit.pullSystem`: the system `Kᵒᵖ ⥤ c.pt.Sheaf AddCommGrpCat`.
* `SheafedSpaceLimit.coleg`: the `k`-th leg `pₖ⁻¹Fₖ ⟶ c.pt.presheaf` of the comparison cocone,
  adjoint to the sheaf component of the `k`-th cone projection.
* `SheafedSpaceLimit.pullCocone`: the comparison cocone itself.
* `SheafedSpaceLimit.isColimitPullCocone`: that cocone is a colimit cocone when `c` is limiting.

## Main results

* `SheafedSpaceLimit.trans_ofSection`: the transition map sends the germwise pullback of
  `s ∈ Fᵢ(V)` to the germwise pullback of the `f_a`-image of `s`.  This is the defining property
  of `trans`, and everything else is proved from it.
* `SheafedSpaceLimit.pull_hom_ext`: a morphism out of `pᵢ⁻¹Fᵢ` into a sheaf is determined by its
  values on germwise pullbacks.
* `SheafedSpaceLimit.trans_id` and `SheafedSpaceLimit.trans_comp`: functoriality.
* `SheafedSpaceLimit.trans_comp_coleg`: the cocone identity `transₐ ≫ colegⱼ = colegᵢ`.
* `SheafedSpaceLimit.isColimitPullCocone`: **the sheaf on the vertex of a limiting cone of
  abelian sheafed spaces is the colimit of the germ-model inverse images of the sheaves at the
  stages**, as an actual colimit cocone in the category of abelian sheaves on the vertex, not
  merely in corepresented form.

## Implementation notes

### Why this is a fresh construction and not a generalization

The transition maps of `DescendOpensAbelian` are built *germwise*, as the stalk maps of the
`f_a`-maps acting on the values of germ-model sections, on top of the `Type`-valued development
of `StacksFrontier.Topology.Sheaves.Limits.DescendOpens`.  Generalizing that from the concrete
projections `S.proj j` to abstract cone legs would mean generalizing the `Type`-valued layer
underneath it.

Instead the transition maps are obtained here from the *universal property* of the germ model,
`GermPullback.existsUnique_mapOut`: `trans a` is the unique map `pᵢ⁻¹Fᵢ ⟶ pⱼ⁻¹Fⱼ` whose
composite with the unit is `transUnit a`.  The gain is that every identity to be proved —
functoriality, and the cocone identity — is an equation between morphisms with *the same source
and the same target*, namely presheaves on the one space underlying `c.pt`.  No transport along
the base equality `pⱼ ≫ f_a = pᵢ` appears in any of those statements, and
`pull_hom_ext` reduces each of them to an identity between germwise pullbacks.

The base equality is still needed, in two confined places: in `transUnit`, as a single
`eqToHom` between `(pⱼ ≫ f_a)_*` and `(pᵢ)_*` — the two double pushforwards agree on the nose,
`Opens.map` of a composite being `rfl` — and in the proofs, where
`AlgebraicGeometry.PresheafedSpace.congr_app` turns an equality of morphisms of presheafed
spaces into a componentwise identity with an explicit restriction map.  Both are absorbed by
`GermPullback.ofSection_map_section`, because the opens involved are *equal* and the morphisms
of `Opens` between two fixed opens form a subsingleton.

### From the corepresented statement to an actual colimit

`SheafedSpaceLimit.existsUnique_mapOut_pull_eq` already says that the vertex sheaf is
`colimₖ pₖ⁻¹Fₖ` in corepresented form, but its statement is phrased in germ-model language and
its compatibility hypothesis `hψ` is an equation between morphisms of *sheafed spaces*.  Two
steps bridge the gap to `IsColimit`:

* `coleg_comp`, from `GermPullback.mapOut_comp`: the `k`-th component attached to a map of
  sheaves `g` on the vertex is `coleg k ≫ g`, so the conclusion of
  `existsUnique_mapOut_pull_eq` becomes a statement about the legs of `pullCocone`; and
* `leg_pushAdj_comp`, which derives `hψ` from the naturality of an arbitrary cocone on
  `pullSystem`.  This is where the base equality is used for the third and last time, through
  `AlgebraicGeometry.PresheafedSpace.ext`: the restriction map it leaves behind is between equal
  opens of the vertex, so `Subsingleton.elim` identifies it with the inclusion that
  `GermPullback.abelianPresheaf_map_ofSection` absorbs.

`existsUnique_desc_pullCocone` packages the result, and `isColimitPullCocone` reads it as an
`IsColimit`.  `Exists.choose` and `Exists.choose_spec` are used rather than `obtain`, since the
latter would build its motive from the goal.

## References

* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace GermPullback

variable {Y Z : TopCat.{u}} (𝒢 : (Y : TopCat.{u}).Presheaf AddCommGrpCat.{u})

/-- **An `eqToHom` between two values of a presheaf at equal opens is a restriction map.**  The
morphisms of `Opens` between two fixed opens form a subsingleton, so the unique one between two
*equal* opens induces the canonical identification. -/
lemma eqToHom_eq_map {V V' : Opens ((Y : TopCat.{u}) : Type u)} (e : V = V') (k : V' ⟶ V) :
    eqToHom (congrArg (fun U ↦ 𝒢.obj (op U)) e) = 𝒢.map k.op := by
  subst e
  rw [Subsingleton.elim k (𝟙 _)]
  simp

/-- **The germwise pullback of a section does not see a restriction of that section.**  Over an
open `W` whose image lies in both `V'` and `V`, the germwise pullback of the restriction of
`s ∈ 𝒢(V)` to `V'` is the germwise pullback of `s`, because the germ of a section at a point is
unchanged by restricting the section to a smaller open containing that point. -/
lemma ofSection_map_section
    {g : ((Z : TopCat.{u}) : Type u) → ((Y : TopCat.{u}) : Type u)}
    {W : Opens ((Z : TopCat.{u}) : Type u)} {V V' : Opens ((Y : TopCat.{u}) : Type u)}
    (k : V' ⟶ V) (hV : ∀ z : W, g z.1 ∈ V) (hV' : ∀ z : W, g z.1 ∈ V')
    (s : 𝒢.obj (op V)) :
    ofSection (g := g) (𝒢 := typePresheaf 𝒢) hV'
        (ConcreteCategory.hom (𝒢.map k.op) s) =
      ofSection (g := g) (𝒢 := typePresheaf 𝒢) hV s := by
  refine ext fun z ↦ ?_
  rw [ofSection_val, ofSection_val]
  exact congrArg (Sigma.mk _) ((typePresheaf 𝒢).germ_res_apply k _ (hV' z) s)

/-- Two germwise pullbacks agree as soon as the generating sections agree after restriction.
This is the form in which `ofSection_map_section` absorbs the restriction maps produced by
`AlgebraicGeometry.PresheafedSpace.congr_app`. -/
lemma ofSection_eq_of_map_eq
    {g : ((Z : TopCat.{u}) : Type u) → ((Y : TopCat.{u}) : Type u)}
    {W : Opens ((Z : TopCat.{u}) : Type u)} {V₁ V₂ : Opens ((Y : TopCat.{u}) : Type u)}
    (m : V₁ ⟶ V₂) (h₁ : ∀ z : W, g z.1 ∈ V₁) (h₂ : ∀ z : W, g z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂))
    (he : s₁ = ConcreteCategory.hom (𝒢.map m.op) s₂) :
    ofSection (g := g) (𝒢 := typePresheaf 𝒢) h₁ s₁ =
      ofSection (g := g) (𝒢 := typePresheaf 𝒢) h₂ s₂ := by
  rw [he]
  exact ofSection_map_section 𝒢 m h₂ h₁ s₂

/-- **Postcomposing the mapping-out morphism.**  Composing `mapOut φ` with a map of sheaves
`g : H ⟶ H'` gives the mapping-out morphism of `φ` followed by `f_* g`. -/
lemma mapOut_comp {f : Z ⟶ Y} {H H' : (Z : TopCat.{u}).Presheaf AddCommGrpCat.{u}}
    (hH : TopCat.Presheaf.IsSheaf H) (hH' : TopCat.Presheaf.IsSheaf H')
    (φ : 𝒢 ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj H) (g : H ⟶ H') :
    mapOut f (φ ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map g) hH' =
      mapOut f φ hH ≫ g :=
  (mapOut_unique f _ hH' (by
    rw [Functor.map_comp, ← Category.assoc, toPushforwardPresheaf_comp_mapOut])).symm

/-- Restriction of a germwise pullback, in the abelian spelling. -/
lemma abelianPresheaf_map_ofSection
    {g : ((Z : TopCat.{u}) : Type u) → ((Y : TopCat.{u}) : Type u)}
    {A B : Opens ((Z : TopCat.{u}) : Type u)} (m : B ⟶ A)
    {V : Opens ((Y : TopCat.{u}) : Type u)} (hV : ∀ z : A, g z.1 ∈ V)
    (hV' : ∀ z : B, g z.1 ∈ V) (s : 𝒢.obj (op V)) :
    ConcreteCategory.hom ((abelianPresheaf g 𝒢).map m.op)
        (ofSection (g := g) (𝒢 := typePresheaf 𝒢) hV s) =
      ofSection (g := g) (𝒢 := typePresheaf 𝒢) hV' s := rfl

end GermPullback

namespace Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

variable {K : Type*} [Category K] {E : K ⥤ SheafedSpace.{u + 1, u, u} AddCommGrpCat.{u}}
  (c : Cone E)

/-! ### The germ models along the cone legs -/

/-- The base map of the `k`-th cone projection, as a function. -/
abbrev projFun (k : K) : ((c.pt : TopCat.{u}) : Type u) → ((E.obj k : TopCat.{u}) : Type u) :=
  ConcreteCategory.hom (c.π.app k).hom.base

/-- The base maps of a cone of sheafed spaces form a cone of spaces: `pⱼ ≫ f_a = pᵢ`. -/
lemma baseEq {j i : K} (a : j ⟶ i) :
    (c.π.app j).hom.base ≫ (E.map a).hom.base = (c.π.app i).hom.base :=
  congrArg (fun m ↦ m.hom.base) (c.w a)

/-- `baseEq` read on points. -/
lemma projFun_comp {j i : K} (a : j ⟶ i) (x : ((c.pt : TopCat.{u}) : Type u)) :
    ConcreteCategory.hom (E.map a).hom.base (projFun c j x) = projFun c i x :=
  ConcreteCategory.congr_hom (baseEq c a) x

/-- **The germ model `pₖ⁻¹Fₖ`** on the space underlying the vertex of `c`. -/
abbrev pullSheaf (k : K) : (c.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} :=
  GermPullback.abelianSheaf (projFun c k) (E.obj k).presheaf

/-- The open `pᵢ⁻¹V` of the vertex is carried into `f_a⁻¹V` by `pⱼ`. -/
lemma mem_stageOpen {j i : K} (a : j ⟶ i) (V : Opens ((E.obj i : TopCat.{u}) : Type u))
    (z : (Opens.map (c.π.app i).hom.base).obj V) :
    projFun c j z.1 ∈ (Opens.map (E.map a).hom.base).obj V := by
  show ConcreteCategory.hom (E.map a).hom.base (projFun c j z.1) ∈ V
  rw [projFun_comp]
  exact z.2

/-! ### The transition maps -/

/-- **The map `Fᵢ ⟶ (pᵢ)_* pⱼ⁻¹Fⱼ` adjoint to the transition map of the pullback system.**  It is
the `f_a`-map of the diagram, followed by the unit of the germ model at the stage `j`, followed by
the identification of `(pⱼ ≫ f_a)_*` with `(pᵢ)_*`.  The two double pushforwards agree on the
nose — `Opens.map` of a composite is `rfl` — so the last factor is a single `eqToHom` coming from
`baseEq`, and it is the only place where the base equality enters a *definition*. -/
def transUnit {j i : K} (a : j ⟶ i) :
    (E.obj i).presheaf ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app i).hom.base).obj
        (pullSheaf c j).presheaf :=
  (E.map a).hom.c ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (E.map a).hom.base).map
      (GermPullback.toPushforwardPresheaf (c.π.app j).hom.base (E.obj j).presheaf) ≫
    eqToHom (congrArg
      (fun m ↦ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} m).obj (pullSheaf c j).presheaf)
      (baseEq c a))

/-- `transUnit a` sends `s ∈ Fᵢ(V)` to the germwise pullback along `pⱼ`, over `pᵢ⁻¹V`, of the
`f_a`-image of `s`. -/
lemma transUnit_app_apply {j i : K} (a : j ⟶ i)
    (V : Opens ((E.obj i : TopCat.{u}) : Type u)) (s : (E.obj i).presheaf.obj (op V)) :
    ConcreteCategory.hom ((transUnit c a).app (op V)) s =
      GermPullback.ofSection (g := projFun c j)
        (𝒢 := GermPullback.typePresheaf (E.obj j).presheaf)
        (mem_stageOpen c a V) (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s) := by
  have hW : (Opens.map (c.π.app j).hom.base).obj ((Opens.map (E.map a).hom.base).obj V)
      = (Opens.map (c.π.app i).hom.base).obj V :=
    congrArg (fun m ↦ (Opens.map m).obj V) (baseEq c a)
  have hle : (Opens.map (c.π.app i).hom.base).obj V ≤
      (Opens.map (c.π.app j).hom.base).obj ((Opens.map (E.map a).hom.base).obj V) :=
    le_of_eq hW.symm
  have happ : (eqToHom (congrArg
      (fun m ↦ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} m).obj (pullSheaf c j).presheaf)
      (baseEq c a))).app (op V)
      = (pullSheaf c j).presheaf.map (homOfLE hle).op := by
    rw [eqToHom_app]
    exact GermPullback.eqToHom_eq_map (pullSheaf c j).presheaf hW (homOfLE hle)
  have h1 : ConcreteCategory.hom ((transUnit c a).app (op V)) s
      = ConcreteCategory.hom ((pullSheaf c j).presheaf.map (homOfLE hle).op)
          (ConcreteCategory.hom
            ((GermPullback.toPushforwardPresheaf (c.π.app j).hom.base (E.obj j).presheaf).app
              (op ((Opens.map (E.map a).hom.base).obj V)))
            (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s)) := by
    rw [← happ]
    rfl
  rw [h1]
  rfl

/-- **The transition map `pᵢ⁻¹Fᵢ ⟶ pⱼ⁻¹Fⱼ` of the pullback system on the vertex of `c`**: the
unique morphism out of the germ model whose composite with the unit is `transUnit a`. -/
def trans {j i : K} (a : j ⟶ i) : (pullSheaf c i).presheaf ⟶ (pullSheaf c j).presheaf :=
  GermPullback.mapOut (c.π.app i).hom.base (transUnit c a) (pullSheaf c j).2

/-- **A morphism out of `pᵢ⁻¹Fᵢ` into a sheaf is determined by its values on the germwise
pullbacks of the sections of `Fᵢ`.**  Both morphisms solve the same mapping-out problem for the
germ model, so `GermPullback.mapOut_unique` identifies them.  This is the extensionality
principle that every identity below is proved with. -/
lemma pull_hom_ext {i : K} {H : (c.pt : TopCat.{u}).Presheaf AddCommGrpCat.{u}}
    (hH : TopCat.Presheaf.IsSheaf H) {ψ₁ ψ₂ : (pullSheaf c i).presheaf ⟶ H}
    (h : ∀ (V : Opens ((E.obj i : TopCat.{u}) : Type u))
        (s : (E.obj i).presheaf.obj (op V)),
      ψ₁.app (op ((Opens.map (c.π.app i).hom.base).obj V))
          (GermPullback.ofSection (g := projFun c i)
            (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2) s) =
        ψ₂.app (op ((Opens.map (c.π.app i).hom.base).obj V))
          (GermPullback.ofSection (g := projFun c i)
            (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2) s)) :
    ψ₁ = ψ₂ := by
  set φ := GermPullback.toPushforwardPresheaf (c.π.app i).hom.base (E.obj i).presheaf ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app i).hom.base).map ψ₁ with hφ
  have k1 : ψ₁ = GermPullback.mapOut (c.π.app i).hom.base φ hH :=
    GermPullback.mapOut_unique (c.π.app i).hom.base φ hH hφ.symm
  have hv := (GermPullback.toPushforwardPresheaf_comp_eq_iff (c.π.app i).hom.base φ ψ₁).1 hφ.symm
  have k2 : ψ₂ = GermPullback.mapOut (c.π.app i).hom.base φ hH :=
    GermPullback.mapOut_unique (c.π.app i).hom.base φ hH
      ((GermPullback.toPushforwardPresheaf_comp_eq_iff (c.π.app i).hom.base φ ψ₂).2
        fun V s ↦ (h V s).symm.trans (hv V s))
  exact k1.trans k2.symm

/-- **The defining property of the transition map**: it sends the germwise pullback along `pᵢ` of
`s ∈ Fᵢ(V)` to the germwise pullback along `pⱼ` of the `f_a`-image of `s`, over any open of the
vertex carried into `V` by `pᵢ`. -/
lemma trans_ofSection {j i : K} (a : j ⟶ i)
    {W : Opens ((c.pt : TopCat.{u}) : Type u)} {V : Opens ((E.obj i : TopCat.{u}) : Type u)}
    (hV : ∀ z : W, projFun c i z.1 ∈ V)
    (hV' : ∀ z : W, projFun c j z.1 ∈ (Opens.map (E.map a).hom.base).obj V)
    (s : (E.obj i).presheaf.obj (op V)) :
    (trans c a).app (op W)
        (GermPullback.ofSection (g := projFun c i)
          (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) hV s) =
      GermPullback.ofSection (g := projFun c j)
        (𝒢 := GermPullback.typePresheaf (E.obj j).presheaf) hV'
        (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s) := by
  have h1 : (trans c a).app (op W)
      (GermPullback.ofSection (g := projFun c i)
        (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) hV s)
      = GermPullback.localValue (c.π.app i).hom.base (transUnit c a) hV s :=
    GermPullback.appValue_ofSection (c.π.app i).hom.base (transUnit c a)
      (pullSheaf c j).2 hV s
  rw [h1, GermPullback.localValue, transUnit_app_apply]
  rfl

/-! ### Functoriality -/

/-- Equal morphisms of sheafed spaces have sheaf components agreeing up to any restriction map
between the two (equal) preimage opens. -/
private lemma hom_c_app_apply_eq_map {X Y : SheafedSpace.{u + 1, u, u} AddCommGrpCat.{u}}
    {α β : X ⟶ Y} (h : α = β) (V : Opens ((Y : TopCat.{u}) : Type u))
    (m : op ((Opens.map β.hom.base).obj V) ⟶ op ((Opens.map α.hom.base).obj V))
    (s : Y.presheaf.obj (op V)) :
    ConcreteCategory.hom (α.hom.c.app (op V)) s =
      ConcreteCategory.hom (X.presheaf.map m) (ConcreteCategory.hom (β.hom.c.app (op V)) s) := by
  subst h
  rw [Subsingleton.elim m (𝟙 _)]
  simp

/-- **The transition maps compose.**  Both sides send the germwise pullback of `s ∈ Fᵢ(V)` to a
germwise pullback of an `f`-image of `s`, and the two images agree because the cocycle law
`E.map (b ≫ a) = E.map b ≫ E.map a` identifies them up to a restriction between *equal* opens. -/
lemma trans_comp {k j i : K} (b : k ⟶ j) (a : j ⟶ i) :
    trans c (b ≫ a) = trans c a ≫ trans c b := by
  refine pull_hom_ext c (pullSheaf c k).2 fun V s ↦ ?_
  have hmle : (Opens.map (E.map (b ≫ a)).hom.base).obj V ≤
      (Opens.map (E.map b).hom.base).obj ((Opens.map (E.map a).hom.base).obj V) := by
    rw [E.map_comp]
    exact le_rfl
  have hmem2 : ∀ z : (Opens.map (c.π.app i).hom.base).obj V, projFun c k z.1 ∈
      (Opens.map (E.map b).hom.base).obj ((Opens.map (E.map a).hom.base).obj V) :=
    fun z ↦ hmle (mem_stageOpen c (b ≫ a) V z)
  have hR : (trans c a ≫ trans c b).app (op ((Opens.map (c.π.app i).hom.base).obj V))
        (GermPullback.ofSection (g := projFun c i)
          (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2) s) =
      GermPullback.ofSection (g := projFun c k)
        (𝒢 := GermPullback.typePresheaf (E.obj k).presheaf) hmem2
        (ConcreteCategory.hom ((E.map b).hom.c.app
          (op ((Opens.map (E.map a).hom.base).obj V)))
          (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s)) :=
    (congrArg (fun t ↦ ConcreteCategory.hom
        ((trans c b).app (op ((Opens.map (c.π.app i).hom.base).obj V))) t)
        (trans_ofSection c a (fun z ↦ z.2) (mem_stageOpen c a V) s)).trans
      (trans_ofSection c b (mem_stageOpen c a V) hmem2 _)
  rw [trans_ofSection c (b ≫ a) (fun z ↦ z.2) (mem_stageOpen c (b ≫ a) V) s, hR]
  refine GermPullback.ofSection_eq_of_map_eq (E.obj k).presheaf (homOfLE hmle)
    (mem_stageOpen c (b ≫ a) V) hmem2 _ _ ?_
  exact hom_c_app_apply_eq_map (E.map_comp b a) V _ s

/-- **The transition map at an identity is the identity**, by the same argument as `trans_comp`
with the identity law `E.map (𝟙 i) = 𝟙 (E.obj i)` in place of the cocycle law. -/
lemma trans_id (i : K) : trans c (𝟙 i) = 𝟙 (pullSheaf c i).presheaf := by
  refine pull_hom_ext c (pullSheaf c i).2 fun V s ↦ ?_
  have hmle : (Opens.map (E.map (𝟙 i)).hom.base).obj V ≤ V := by
    rw [E.map_id]
    exact le_rfl
  rw [trans_ofSection c (𝟙 i) (fun z ↦ z.2) (mem_stageOpen c (𝟙 i) V) s]
  refine GermPullback.ofSection_eq_of_map_eq (E.obj i).presheaf (homOfLE hmle)
    (mem_stageOpen c (𝟙 i) V) (fun z ↦ z.2) _ _ ?_
  exact hom_c_app_apply_eq_map (E.map_id i) V _ s

/-- **The pullback system on the vertex of an abstract cone**: the functor
`Kᵒᵖ ⥤ c.pt.Sheaf AddCommGrpCat` sending `k` to the germ model `pₖ⁻¹Fₖ` and `a : j ⟶ i` to
`trans a`.  This is the abstract-cone counterpart of
`SpectralAbelianSheafSystem.abelianPullbackSystem`, which lives over the concrete limit
`S.invLim`. -/
def pullSystem : Kᵒᵖ ⥤ (c.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} where
  obj A := pullSheaf c A.unop
  map α := ⟨trans c α.unop⟩
  map_id A := InducedCategory.hom_ext (trans_id c A.unop)
  map_comp α β := InducedCategory.hom_ext (trans_comp c β.unop α.unop)

/-! ### The comparison cocone -/

/-- **The `k`-th leg of the comparison cocone**, `pₖ⁻¹Fₖ ⟶ c.pt.presheaf`: the morphism out of
the germ model adjoint to the sheaf component of the `k`-th cone projection. -/
def coleg (k : K) : (pullSheaf c k).presheaf ⟶ c.pt.presheaf :=
  GermPullback.mapOut (c.π.app k).hom.base (c.π.app k).hom.c c.pt.IsSheaf

/-- `coleg k` sends a germwise pullback to the local value prescribed by the sheaf component of
the `k`-th cone projection. -/
lemma coleg_ofSection (k : K) {W : Opens ((c.pt : TopCat.{u}) : Type u)}
    {V : Opens ((E.obj k : TopCat.{u}) : Type u)} (hV : ∀ z : W, projFun c k z.1 ∈ V)
    (s : (E.obj k).presheaf.obj (op V)) :
    (coleg c k).app (op W)
        (GermPullback.ofSection (g := projFun c k)
          (𝒢 := GermPullback.typePresheaf (E.obj k).presheaf) hV s) =
      GermPullback.localValue (c.π.app k).hom.base (c.π.app k).hom.c hV s :=
  GermPullback.appValue_ofSection (c.π.app k).hom.base (c.π.app k).hom.c c.pt.IsSheaf hV s

/-- **The legs of the comparison cocone are compatible with the transition maps.**  Evaluated on
the germwise pullback of `s ∈ Fᵢ(V)` both sides are the image of `s` under the sheaf component of
the `i`-th cone projection: on the left the sheaf half of the cone identity
`c.π.app j ≫ E.map a = c.π.app i` is applied, and the restriction maps it leaves behind are
between *equal* opens of the vertex, hence identities. -/
lemma trans_comp_coleg {j i : K} (a : j ⟶ i) : trans c a ≫ coleg c j = coleg c i := by
  refine pull_hom_ext c c.pt.IsSheaf fun V s ↦ ?_
  have hid : ∀ (P : (c.pt : TopCat.{u}).Presheaf AddCommGrpCat.{u})
      (m : op ((Opens.map (c.π.app i).hom.base).obj V) ⟶
        op ((Opens.map (c.π.app i).hom.base).obj V))
      (t : P.obj (op ((Opens.map (c.π.app i).hom.base).obj V))),
      ConcreteCategory.hom (P.map m) t = t := by
    intro P m t
    rw [Subsingleton.elim m (𝟙 _), P.map_id]
    rfl
  have hcomp : ∀ (m : op ((Opens.map (c.π.app i).hom.base).obj V) ⟶
        op ((Opens.map (c.π.app j).hom.base).obj ((Opens.map (E.map a).hom.base).obj V)))
      (n : op ((Opens.map (c.π.app j).hom.base).obj ((Opens.map (E.map a).hom.base).obj V)) ⟶
        op ((Opens.map (c.π.app i).hom.base).obj V))
      (t : c.pt.presheaf.obj (op ((Opens.map (c.π.app i).hom.base).obj V))),
      ConcreteCategory.hom (c.pt.presheaf.map n)
        (ConcreteCategory.hom (c.pt.presheaf.map m) t) = t := by
    intro m n t
    rw [← ConcreteCategory.comp_apply, ← c.pt.presheaf.map_comp, hid]
  have hL : (trans c a ≫ coleg c j).app (op ((Opens.map (c.π.app i).hom.base).obj V))
        (GermPullback.ofSection (g := projFun c i)
          (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2) s) =
      GermPullback.localValue (c.π.app j).hom.base (c.π.app j).hom.c
        (mem_stageOpen c a V) (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s) :=
    (congrArg (fun t ↦ ConcreteCategory.hom
        ((coleg c j).app (op ((Opens.map (c.π.app i).hom.base).obj V))) t)
      (trans_ofSection c a (fun z ↦ z.2) (mem_stageOpen c a V) s)).trans
      (coleg_ofSection c j (mem_stageOpen c a V) _)
  have hcw : ConcreteCategory.hom ((c.π.app j).hom.c.app
        (op ((Opens.map (E.map a).hom.base).obj V)))
        (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) s) =
      ConcreteCategory.hom (c.pt.presheaf.map (eqToHom (congrArg
        (fun m ↦ op ((Opens.map m).obj V)) (baseEq c a).symm)))
        (ConcreteCategory.hom ((c.π.app i).hom.c.app (op V)) s) := by
    exact hom_c_app_apply_eq_map (c.w a) V _ s
  rw [hL, coleg_ofSection c i (fun z ↦ z.2) s]
  simp only [GermPullback.localValue, Functor.const_obj_obj]
  rw [hid, hcw]
  exact hcomp _ _ _

/-- **The comparison cocone on the pullback system**, with vertex the sheaf on the vertex of `c`.
Over a limiting cone this is the cocone that `existsUnique_mapOut_pull_eq` characterizes as a
colimit cocone in corepresented form. -/
def pullCocone : Cocone (pullSystem c) where
  pt := c.pt.sheaf
  ι :=
    { app := fun A ↦ ⟨coleg c A.unop⟩
      naturality := fun _ _ α ↦ InducedCategory.hom_ext (trans_comp_coleg c α.unop) }

/-- **The `k`-th component attached to a map of sheaves on the vertex is `coleg k` followed by
it.**  This is `GermPullback.mapOut_comp`, and it is what turns the conclusion of
`existsUnique_mapOut_pull_eq` into a statement about the legs of `pullCocone`. -/
lemma coleg_comp {H : (c.pt : TopCat.{u}).Presheaf AddCommGrpCat.{u}}
    (hH : TopCat.Presheaf.IsSheaf H) (g : c.pt.presheaf ⟶ H) (k : K) :
    coleg c k ≫ g = GermPullback.mapOut (c.π.app k).hom.base (pull c H g k) hH :=
  (GermPullback.mapOut_comp (E.obj k).presheaf c.pt.IsSheaf hH (c.π.app k).hom.c g).symm

/-- **The compatibility hypothesis of `existsUnique_mapOut_pull_eq`, from the naturality of a
cocone on the pullback system.**  The two sides are morphisms of sheafed spaces with base maps
`pᵢ ≫ f_a` and `pⱼ`, equal by `baseEq`; componentwise, `AlgebraicGeometry.PresheafedSpace.ext`
leaves a restriction between two *equal* opens of the vertex, which `Subsingleton.elim` and
`GermPullback.abelianPresheaf_map_ofSection` absorb, and what remains is exactly the naturality
of `s` evaluated on a germwise pullback through `trans_ofSection`. -/
lemma leg_pushAdj_comp (s : Cocone (pullSystem c)) {i j : K} (a : i ⟶ j) :
    leg c s.pt.presheaf s.pt.2 i (pushAdj c s.pt.presheaf i (s.ι.app (op i)).hom) ≫ E.map a =
      leg c s.pt.presheaf s.pt.2 j (pushAdj c s.pt.presheaf j (s.ι.app (op j)).hom) := by
  refine InducedCategory.hom_ext
    (AlgebraicGeometry.PresheafedSpace.ext _ _ (baseEq c a) ?_)
  refine NatTrans.ext (funext fun V ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
  induction V with
  | op V =>
    have hWeq : (Opens.map (c.π.app i).hom.base).obj ((Opens.map (E.map a).hom.base).obj V)
        = (Opens.map (c.π.app j).hom.base).obj V :=
      congrArg (fun m ↦ (Opens.map m).obj V) (baseEq c a)
    have hnat : trans c a ≫ (s.ι.app (op i)).hom = (s.ι.app (op j)).hom :=
      congrArg (fun m ↦ m.hom) (s.w a.op)
    have hgoal := ConcreteCategory.congr_hom (NatTrans.congr_app hnat
      (op ((Opens.map (c.π.app j).hom.base).obj V)))
      (GermPullback.ofSection (g := projFun c j)
        (𝒢 := GermPullback.typePresheaf (E.obj j).presheaf) (fun z ↦ z.2) t)
    have hR : ConcreteCategory.hom ((trans c a ≫ (s.ι.app (op i)).hom).app
          (op ((Opens.map (c.π.app j).hom.base).obj V)))
          (GermPullback.ofSection (g := projFun c j)
            (𝒢 := GermPullback.typePresheaf (E.obj j).presheaf) (fun z ↦ z.2) t) =
        ConcreteCategory.hom ((s.ι.app (op i)).hom.app
          (op ((Opens.map (c.π.app j).hom.base).obj V)))
          (GermPullback.ofSection (g := projFun c i)
            (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (mem_stageOpen c a V)
            (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) t)) :=
      congrArg (fun x ↦ ConcreteCategory.hom ((s.ι.app (op i)).hom.app
          (op ((Opens.map (c.π.app j).hom.base).obj V))) x)
        (trans_ofSection c a (fun z ↦ z.2) (mem_stageOpen c a V) t)
    refine Eq.trans ?_ (hR.symm.trans hgoal)
    refine Eq.trans ?_ (congrArg (fun x ↦ ConcreteCategory.hom
        ((s.ι.app (op i)).hom.app (op ((Opens.map (c.π.app j).hom.base).obj V))) x)
      (GermPullback.abelianPresheaf_map_ofSection (E.obj i).presheaf
        (homOfLE (le_of_eq hWeq.symm)) (fun z ↦ z.2) (mem_stageOpen c a V)
        (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) t)))
    refine Eq.trans ?_ (NatTrans.naturality_apply (s.ι.app (op i)).hom
      (homOfLE (le_of_eq hWeq.symm)).op
      (GermPullback.ofSection (g := projFun c i)
        (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2)
        (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) t))).symm
    refine congrArg (fun mm ↦ ConcreteCategory.hom (s.pt.presheaf.map mm)
      (ConcreteCategory.hom ((s.ι.app (op i)).hom.app
        (op ((Opens.map (c.π.app i).hom.base).obj ((Opens.map (E.map a).hom.base).obj V))))
        (GermPullback.ofSection (g := projFun c i)
          (𝒢 := GermPullback.typePresheaf (E.obj i).presheaf) (fun z ↦ z.2)
          (ConcreteCategory.hom ((E.map a).hom.c.app (op V)) t)))) ?_
    exact Subsingleton.elim
      (α := op ((Opens.map (c.π.app i).hom.base).obj
          ((Opens.map (E.map a).hom.base).obj V)) ⟶
        op ((Opens.map (c.π.app j).hom.base).obj V)) _ _

/-- **The universal property of the comparison cocone.**  For a limiting cone `c` and any cocone
`s` on the pullback system there is a unique map of sheaves on the vertex compatible with the
legs.  This is `existsUnique_mapOut_pull_eq` read through `coleg_comp` and `leg_pushAdj_comp`. -/
theorem existsUnique_desc_pullCocone (hc : IsLimit c) (s : Cocone (pullSystem c)) :
    ∃! g : c.pt.presheaf ⟶ s.pt.presheaf, ∀ k, coleg c k ≫ g = (s.ι.app (op k)).hom := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_mapOut_pull_eq c s.pt.presheaf s.pt.2 hc
    (fun k ↦ (s.ι.app (op k)).hom) (fun a ↦ leg_pushAdj_comp c s a)
  exact ⟨g, fun k ↦ (coleg_comp c s.pt.2 g k).trans (hg k),
    fun g' hg' ↦ hgu g' fun k ↦ (coleg_comp c s.pt.2 g' k).symm.trans (hg' k)⟩

/-- **The sheaf on the vertex of a limiting cone of abelian sheafed spaces is the colimit of the
germ-model inverse images of the sheaves at the stages.**  Unlike
`existsUnique_mapOut_pull_eq`, which is corepresented and phrased in germ-model language, this
is an actual colimit cocone in the category of abelian sheaves on the space underlying the
vertex, so `CategoryTheory.Limits.colimit.post` and everything downstream of it — in particular
abelian Stacks 01FF — applies to the system on the vertex of an abstract cone. -/
def isColimitPullCocone (hc : IsLimit c) : IsColimit (pullCocone c) where
  desc s := ⟨(existsUnique_desc_pullCocone c hc s).choose⟩
  fac s A := InducedCategory.hom_ext ((existsUnique_desc_pullCocone c hc s).choose_spec.1 A.unop)
  uniq s m hm := InducedCategory.hom_ext
    ((existsUnique_desc_pullCocone c hc s).choose_spec.2 m.hom
      fun k ↦ congrArg (fun x ↦ x.hom) (hm (op k)))

end Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

end
