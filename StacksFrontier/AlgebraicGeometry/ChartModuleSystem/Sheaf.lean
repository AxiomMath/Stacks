module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Local
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The sheaf of modules glued from a chart module system

Let `S` be a chart module system on an index of affine charts `I` of a scheme `Y`. This file
constructs the sheaf of `𝒪_Y`-modules `S.sheaf` glued from it, identifies its sections over each
chart with the module on the chart, and describes its global sections and the morphisms out of it.

## Construction

The sections of `S.sheaf` over an open `W` are, by definition, the *compatible families* over `W`:
an element of `M c` for every chart `c` contained in `W`, the element for a refinement being the
restriction of the element for the chart (`AlgebraicGeometry.ChartModuleSystem.sectionsSubgroup`).
This is the limit over the charts in `W` and their refinements, so restriction maps and the module
structure over `Γ(Y, W)` are componentwise and need no choice. All the content is in the sheaf
condition and in the comparison with the charts, and both reduce to descent within a single chart
(`AlgebraicGeometry.ChartModuleSystem.existsUnique_of_sieve`): a compatible family is determined
by, and can be built from, its values on any cofinal sieve of charts
(`AlgebraicGeometry.ChartModuleSystem.existsUnique_sectionsSubgroup`).

This route was preferred over gluing the tilde sheaves of the chart modules along their overlaps
(`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue`): the overlaps of two charts are not charts, and
the comparison isomorphisms there would themselves have to be glued from the charts inside the
overlaps, with a cocycle condition to check.

Morphisms out of `S.sheaf` are built with Stacks 009U
(`Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`) from their components on a basis of
charts.

## Main definitions

* `AlgebraicGeometry.ChartModuleSystem.sheaf`: the glued sheaf of `𝒪_Y`-modules.
* `AlgebraicGeometry.ChartModuleSystem.sectionsEquiv`: its sections over the chart `c` are `M c`,
  `Γ(Y, V c)`-linearly.
* `AlgebraicGeometry.ChartModuleSystem.globalSectionOfCompatible`: the global section attached to a
  compatible family `s c ∈ M c`.
* `AlgebraicGeometry.ChartModuleSystem.homOfCompatible`: the morphism `S.sheaf ⟶ H` determined by
  compatible maps `M c → Γ(H, V c)`, and `AlgebraicGeometry.ChartModuleSystem.homOfFamily` the same
  for maps given on a basis of charts only.

## Main results

* `AlgebraicGeometry.ChartModuleSystem.isSheaf_presheafAb`: the compatible families form a sheaf.
* `AlgebraicGeometry.ChartModuleSystem.sectionsEquiv_restrict`: the identification of sections over
  the charts commutes with restriction.
* `AlgebraicGeometry.ChartModuleSystem.sectionsEquiv_globalSectionOfCompatible` and
  `AlgebraicGeometry.ChartModuleSystem.eq_globalSectionOfCompatible`: global sections are
  compatible families.
* `AlgebraicGeometry.ChartModuleSystem.homOfCompatible_app` and
  `AlgebraicGeometry.ChartModuleSystem.hom_ext`: morphisms out of the glued sheaf are compatible
  families of maps on the charts.

## References

* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ChartModuleSystem

open Scheme

variable {Y : Scheme.{u}} {I : Y.AffineChartIndex} (S : ChartModuleSystem I)

/-! ### Compatible families -/

/-- Restricting a function along `f` and then along `g` is restricting it along `f ≫ g`. -/
private theorem presheaf_map_map_apply {A B C : Y.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (r : Y.presheaf.obj A) :
    (Y.presheaf.map g).hom ((Y.presheaf.map f).hom r) = (Y.presheaf.map (f ≫ g)).hom r := by
  rw [Functor.map_comp]
  rfl

/-- Restricting a function from `W` to a chart contained in `W` and then to a refinement of that
chart is restricting it to the refinement. -/
theorem res_map {W : Y.Opens} {c' c : I.ι} (h : I.Refines c' c) (hc : (I.V c).1 ≤ W)
    (hc' : (I.V c').1 ≤ W) (r : Γ(Y, W)) :
    I.res h ((Y.presheaf.map (homOfLE hc).op).hom r) = (Y.presheaf.map (homOfLE hc').op).hom r := by
  rw [Scheme.AffineChartIndex.res, presheaf_map_map_apply]
  rfl

/-- The compatible families over an open `W`: an element of `M c` for every chart `c` contained
in `W`, the element for a refinement being the restriction of the element for the chart. -/
def sectionsSubgroup (W : Y.Opens) :
    AddSubgroup (∀ c : {c : I.ι // (I.V c).1 ≤ W}, S.M c.1) where
  carrier := {s | ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (hc : (I.V c).1 ≤ W)
    (hc' : (I.V c').1 ≤ W), S.ρ h (s ⟨c, hc⟩) = s ⟨c', hc'⟩}
  add_mem' {s t} hs ht c' c h hc hc' := by
    simp only [Pi.add_apply, map_add, hs h hc hc', ht h hc hc']
  zero_mem' c' c h hc hc' := by simp
  neg_mem' {s} hs c' c h hc hc' := by simp only [Pi.neg_apply, map_neg, hs h hc hc']

variable {S} in
/-- Compatibility of a family over `W` along a refinement. -/
theorem sectionsSubgroup_compat {W : Y.Opens} (s : S.sectionsSubgroup W) {c' c : I.ι}
    (h : I.Refines c' c) (hc : (I.V c).1 ≤ W) (hc' : (I.V c').1 ≤ W) :
    S.ρ h (s.1 ⟨c, hc⟩) = s.1 ⟨c', hc'⟩ :=
  s.2 h hc hc'

/-- Compatible families are stable under the componentwise action of functions on `W`. -/
theorem smul_mem_sectionsSubgroup (W : Y.Opens) (r : Γ(Y, W)) (s : S.sectionsSubgroup W) :
    (fun c : {c : I.ι // (I.V c).1 ≤ W} => (Y.presheaf.map (homOfLE c.2).op).hom r • s.1 c) ∈
      S.sectionsSubgroup W := by
  intro c' c h hc hc'
  show S.ρ h ((Y.presheaf.map (homOfLE hc).op).hom r • s.1 ⟨c, hc⟩) = _
  rw [map_smulₛₗ, res_map, sectionsSubgroup_compat]

/-- **The compatible families over `W` form a `Γ(Y, W)`-module**, a function acting on the
element for a chart `c` after restriction to `V c`. -/
instance moduleSectionsSubgroup (W : Y.Opens) : Module Γ(Y, W) (S.sectionsSubgroup W) where
  smul r s := ⟨_, S.smul_mem_sectionsSubgroup W r s⟩
  one_smul s := Subtype.ext (funext fun c => by
    change (Y.presheaf.map (homOfLE c.2).op).hom 1 • s.1 c = s.1 c
    rw [map_one, one_smul])
  mul_smul r₁ r₂ s := Subtype.ext (funext fun c => by
    change (Y.presheaf.map (homOfLE c.2).op).hom (r₁ * r₂) • s.1 c =
      (Y.presheaf.map (homOfLE c.2).op).hom r₁ • (Y.presheaf.map (homOfLE c.2).op).hom r₂ • s.1 c
    rw [map_mul, mul_smul])
  smul_zero r := Subtype.ext (funext fun c => smul_zero _)
  smul_add r s t := Subtype.ext (funext fun c => smul_add _ (s.1 c) (t.1 c))
  add_smul r₁ r₂ s := Subtype.ext (funext fun c => by
    change (Y.presheaf.map (homOfLE c.2).op).hom (r₁ + r₂) • s.1 c =
      (Y.presheaf.map (homOfLE c.2).op).hom r₁ • s.1 c +
        (Y.presheaf.map (homOfLE c.2).op).hom r₂ • s.1 c
    rw [map_add, add_smul])
  zero_smul s := Subtype.ext (funext fun c => by
    change (Y.presheaf.map (homOfLE c.2).op).hom 0 • s.1 c = 0
    rw [map_zero, zero_smul])

variable {S} in
/-- A function acts on a compatible family componentwise, after restriction. -/
theorem smul_coe {W : Y.Opens} (r : Γ(Y, W)) (s : S.sectionsSubgroup W)
    (c : {c : I.ι // (I.V c).1 ≤ W}) :
    (r • s).1 c = (Y.presheaf.map (homOfLE c.2).op).hom r • s.1 c :=
  rfl

/-- Restriction of compatible families to a smaller open. -/
def sectionsRestrict {W W' : Y.Opens} (h : W' ≤ W) :
    S.sectionsSubgroup W →+ S.sectionsSubgroup W' where
  toFun s := ⟨fun c => s.1 ⟨c.1, c.2.trans h⟩, fun _ _ hr _ _ => s.2 hr _ _⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of abelian groups of compatible families. -/
def presheafAb : TopCat.Presheaf AddCommGrpCat.{u} Y where
  obj W := AddCommGrpCat.of (S.sectionsSubgroup W.unop)
  map f := AddCommGrpCat.ofHom (S.sectionsRestrict f.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The module structure of `presheafAb` over the structure sheaf. -/
instance modulePresheafAb (W : Y.Opensᵒᵖ) :
    Module (Y.ringCatSheaf.obj.obj W) (S.presheafAb.obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (S.sectionsSubgroup W.unop))

/-- The restriction maps of `presheafAb` are semilinear. -/
theorem presheafAb_map_smul ⦃W W' : Y.Opensᵒᵖ⦄ (f : W ⟶ W') (r : Y.ringCatSheaf.obj.obj W)
    (s : S.presheafAb.obj W) :
    S.presheafAb.map f (r • s) = Y.ringCatSheaf.obj.map f r • S.presheafAb.map f s := by
  refine Subtype.ext (funext fun c => ?_)
  show (Y.presheaf.map (homOfLE (c.2.trans f.unop.le)).op).hom r • s.1 ⟨c.1, _⟩ =
    (Y.presheaf.map (homOfLE c.2).op).hom ((Y.presheaf.map f).hom r) • s.1 ⟨c.1, _⟩
  exact (congrArg (· • s.1 ⟨c.1, c.2.trans f.unop.le⟩)
    (presheaf_map_map_apply f (homOfLE c.2).op r)).symm

/-- The presheaf of `𝒪_Y`-modules of compatible families. -/
noncomputable def presheafOfModules : PresheafOfModules.{u} Y.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf S.presheafAb S.presheafAb_map_smul

/-! ### Gluing compatible families -/

section Glue

variable (W : Y.Opens) (P : I.ι → Prop) (hPW : ∀ e, P e → (I.V e).1 ≤ W)
  (hPref : ∀ ⦃e' e : I.ι⦄, P e → I.Refines e' e → P e')
  (hcof : ∀ c, (I.V c).1 ≤ W → ∀ y ∈ (I.V c).1, ∃ e, P e ∧ I.Refines e c ∧ y ∈ (I.V e).1)
  (m : ∀ e, P e → S.M e)
  (hm : ∀ ⦃e' e : I.ι⦄ (he : P e) (h : I.Refines e' e), m e' (hPref he h) = S.ρ h (m e he))

include hPW hcof hm in
/-- **A compatible family over `W` is determined by, and can be built from, its values on a
cofinal sieve of charts.** Let `P` be a property of charts contained in `W`, stable under
refinement, such that every chart in `W` is covered by its refinements with `P`; a family of
elements on the charts with `P` compatible with restriction extends uniquely to a compatible family
over `W`. -/
theorem existsUnique_sectionsSubgroup :
    ∃! s : S.sectionsSubgroup W, ∀ e (he : P e), s.1 ⟨e, hPW e he⟩ = m e he := by
  choose x hx hxu using fun c : {c : I.ι // (I.V c).1 ≤ W} =>
    S.existsUnique_of_sieve c.1 P hPref (hcof c.1 c.2) m hm
  have hcompat : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (hc : (I.V c).1 ≤ W)
      (hc' : (I.V c').1 ≤ W), S.ρ h (x ⟨c, hc⟩) = x ⟨c', hc'⟩ := by
    intro c' c h hc hc'
    refine hxu ⟨c', hc'⟩ _ fun e he he' => ?_
    rw [S.ρ_ρ]
    exact hx ⟨c, hc⟩ e he _
  refine ⟨⟨x, hcompat⟩, fun e he =>
    (hxu ⟨e, hPW e he⟩ (m e he) fun e' he' h => (hm he h).symm).symm, fun s hs => ?_⟩
  refine Subtype.ext (funext fun c => hxu c _ fun e he h => ?_)
  rw [sectionsSubgroup_compat s h c.2 (hPW e he)]
  exact hs e he

end Glue

/-! ### The sheaf condition -/

/-- **The compatible families form a sheaf.** A family of compatible families on the members of an
open covering, agreeing on the overlaps, glues uniquely: on a chart contained in one member of the
covering the glued family is the given one, and on any other chart it is obtained by gluing within
that chart (`AlgebraicGeometry.ChartModuleSystem.existsUnique_of_sieve`). -/
theorem isSheaf_presheafAb : S.presheafAb.IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf => ?_
  let P : I.ι → Prop := fun e => ∃ i, (I.V e).1 ≤ U i
  have key : ∀ e i j (hi : (I.V e).1 ≤ U i) (hj : (I.V e).1 ≤ U j),
      (sf i : S.sectionsSubgroup (U i)).1 ⟨e, hi⟩ = (sf j : S.sectionsSubgroup (U j)).1 ⟨e, hj⟩ :=
    fun e i j hi hj => congrArg (fun s : S.sectionsSubgroup (U i ⊓ U j) => s.1 ⟨e, le_inf hi hj⟩)
      (hsf i j)
  let m : ∀ e, P e → S.M e := fun e he =>
    (sf he.choose : S.sectionsSubgroup _).1 ⟨e, he.choose_spec⟩
  have hPref : ∀ ⦃e' e : I.ι⦄, P e → I.Refines e' e → P e' := fun e' e ⟨i, hi⟩ h =>
    ⟨i, (I.le_of_refines h).trans hi⟩
  have hm : ∀ ⦃e' e : I.ι⦄ (he : P e) (h : I.Refines e' e), m e' (hPref he h) = S.ρ h (m e he) :=
    fun e' e he h => (key e' (hPref he h).choose he.choose (hPref he h).choose_spec
      ((I.le_of_refines h).trans he.choose_spec)).trans
      (sectionsSubgroup_compat (sf he.choose : S.sectionsSubgroup _) h he.choose_spec _).symm
  have hPW : ∀ e, P e → (I.V e).1 ≤ iSup U := fun e ⟨i, hi⟩ => hi.trans (le_iSup U i)
  have hcof : ∀ c, (I.V c).1 ≤ iSup U → ∀ y ∈ (I.V c).1,
      ∃ e, P e ∧ I.Refines e c ∧ y ∈ (I.V e).1 := by
    intro c hc y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hc hy)
    obtain ⟨e, he, hye, heU⟩ := I.exists_refines_le hy hi
    exact ⟨e, ⟨i, heU⟩, he, hye⟩
  obtain ⟨s, hs, hsu⟩ := S.existsUnique_sectionsSubgroup (iSup U) P hPW hPref hcof m hm
  refine ⟨s, fun i => Subtype.ext (funext fun c => ?_), fun t ht => hsu t fun e he => ?_⟩
  · exact (hs c.1 ⟨i, c.2⟩).trans (key _ _ _ _ _)
  · exact congrArg (fun s : S.sectionsSubgroup (U he.choose) => s.1 ⟨e, he.choose_spec⟩)
      (ht he.choose)

/-- **The sheaf of `𝒪_Y`-modules glued from a chart module system.** Its sections over an open
`W` are the compatible families over `W`: an element of `M c` for every chart `c` contained in
`W`, compatible with the restriction maps. -/
noncomputable def sheaf : Y.Modules :=
  ⟨S.presheafOfModules, S.isSheaf_presheafAb⟩

/-- The sections of the glued sheaf over `W` are the compatible families over `W`. -/
theorem sheaf_sections (W : Y.Opens) :
    (Γ(S.sheaf, W) : Type u) = S.sectionsSubgroup W :=
  rfl

/-! ### Sections over a chart -/

section Chart

variable (c : I.ι)

/-- An element of `M c` extends uniquely to a compatible family over `V c`. -/
theorem existsUnique_ofChart (x : S.M c) :
    ∃! s : S.sectionsSubgroup (I.V c).1, ∀ e (he : I.Refines e c),
      s.1 ⟨e, I.le_of_refines he⟩ = S.ρ he x :=
  S.existsUnique_sectionsSubgroup (I.V c).1 (I.Refines · c) (fun _ he => I.le_of_refines he)
    (fun _ _ he h => I.refines_trans h he)
    (fun c₀ hc₀ y hy => by
      obtain ⟨e, he₀, he, hye⟩ := I.exists_refines_refines hy (hc₀ hy)
      exact ⟨e, he, he₀, hye⟩)
    (fun e he => S.ρ he x) fun _ _ he h => (S.ρ_ρ h he x).symm

/-- The compatible family over `V c` determined by an element of `M c`: its value on a refinement
of `c` is the restriction. -/
noncomputable def ofChart (x : S.M c) : S.sectionsSubgroup (I.V c).1 :=
  (S.existsUnique_ofChart c x).exists.choose

/-- The family attached to `x : M c` takes the value `ρ x` on a refinement of `c`. -/
theorem ofChart_apply (x : S.M c) {e : I.ι} (he : I.Refines e c) (hle : (I.V e).1 ≤ (I.V c).1) :
    (S.ofChart c x).1 ⟨e, hle⟩ = S.ρ he x :=
  (S.existsUnique_ofChart c x).exists.choose_spec e he

/-- A compatible family over `V c` is determined by its value on `c`. -/
theorem sectionsSubgroup_ext_chart {s₁ s₂ : S.sectionsSubgroup (I.V c).1}
    (h : s₁.1 ⟨c, le_rfl⟩ = s₂.1 ⟨c, le_rfl⟩) : s₁ = s₂ :=
  (S.existsUnique_ofChart c (s₁.1 ⟨c, le_rfl⟩)).unique
    (fun _ he => (sectionsSubgroup_compat s₁ he le_rfl _).symm)
    (fun _ he => h ▸ (sectionsSubgroup_compat s₂ he le_rfl _).symm)

/-- **The sections of the glued sheaf over a chart are the module on that chart**, linearly over
the functions on the chart. A section is sent to its value on the chart itself. -/
noncomputable def sectionsEquiv : Γ(S.sheaf, (I.V c).1) ≃ₗ[Γ(Y, (I.V c).1)] S.M c where
  toFun s := (s : S.sectionsSubgroup (I.V c).1).1 ⟨c, le_rfl⟩
  invFun x := S.ofChart c x
  left_inv s := S.sectionsSubgroup_ext_chart c (by
    rw [ofChart_apply _ _ _ (I.refines_refl c), S.ρ_refl])
  right_inv x := by
    change (S.ofChart c x).1 ⟨c, le_rfl⟩ = x
    rw [ofChart_apply _ _ _ (I.refines_refl c), S.ρ_refl]
  map_add' _ _ := rfl
  map_smul' r s := by
    change (Y.presheaf.map (homOfLE le_rfl).op).hom r • (s : S.sectionsSubgroup _).1 ⟨c, le_rfl⟩ =
      r • (s : S.sectionsSubgroup _).1 ⟨c, le_rfl⟩
    rw [show (homOfLE (le_refl (I.V c).1)).op = 𝟙 (op (I.V c).1) from Subsingleton.elim _ _,
      Y.presheaf.map_id]
    rfl

/-- The section over `V c` attached to an element of `M c` restricts, on a refinement of `c`, to
the restriction of that element. -/
theorem sectionsEquiv_symm_apply (x : S.M c) {e : I.ι} (he : I.Refines e c)
    (hle : (I.V e).1 ≤ (I.V c).1) :
    ((S.sectionsEquiv c).symm x : S.sectionsSubgroup (I.V c).1).1 ⟨e, hle⟩ = S.ρ he x :=
  S.ofChart_apply c x he hle

/-- The value of a section over `W` on a chart `c` contained in `W` is the image under
`sectionsEquiv c` of its restriction to `V c`. -/
theorem sectionsEquiv_map {W : Y.Opens} (s : Γ(S.sheaf, W)) (hc : (I.V c).1 ≤ W) :
    S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE hc).op s) =
      (s : S.sectionsSubgroup W).1 ⟨c, hc⟩ :=
  rfl

/-- **The identification of sections over charts commutes with restriction:** for `c'` refining
`c`, restricting a section from `V c` to `V c'` corresponds to the restriction map `ρ`. -/
theorem sectionsEquiv_restrict {c' : I.ι} (h : I.Refines c' c) (s : Γ(S.sheaf, (I.V c).1)) :
    S.sectionsEquiv c' (S.sheaf.presheaf.map (homOfLE (I.le_of_refines h)).op s) =
      S.ρ h (S.sectionsEquiv c s) :=
  (sectionsSubgroup_compat (s : S.sectionsSubgroup (I.V c).1) h le_rfl _).symm

end Chart

/-! ### Global sections -/

/-- **A global section from a compatible family.** A family of elements `s c ∈ M c`, one for every
chart, with `ρ (s c) = s c'` whenever `c'` refines `c`, is a global section of the glued sheaf. -/
def globalSectionOfCompatible (s : ∀ c, S.M c)
    (hs : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c), S.ρ h (s c) = s c') : Γ(S.sheaf, ⊤) :=
  (⟨fun c => s c.1, fun _ _ h _ _ => hs h⟩ : S.sectionsSubgroup ⊤)

/-- The global section attached to a compatible family restricts on each chart `c` to `s c`. -/
@[simp] theorem sectionsEquiv_globalSectionOfCompatible (s : ∀ c, S.M c)
    (hs : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c), S.ρ h (s c) = s c') (c : I.ι) :
    S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE le_top).op
      (S.globalSectionOfCompatible s hs)) = s c :=
  rfl

/-- Two sections over `W` with the same restrictions to the charts contained in `W` are equal. -/
theorem section_ext {W : Y.Opens} {s₁ s₂ : Γ(S.sheaf, W)}
    (h : ∀ c (hc : (I.V c).1 ≤ W), S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE hc).op s₁) =
      S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE hc).op s₂)) : s₁ = s₂ :=
  Subtype.ext (funext fun c => h c.1 c.2)

/-- Every global section is the one attached to the compatible family of its restrictions to the
charts. -/
theorem eq_globalSectionOfCompatible (s : Γ(S.sheaf, ⊤)) :
    s = S.globalSectionOfCompatible
      (fun c => S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE le_top).op s))
      (fun _ _ h => sectionsSubgroup_compat (s : S.sectionsSubgroup ⊤) h le_top le_top) :=
  rfl

/-! ### Morphisms out of the glued sheaf -/

section Hom

variable {H : Y.Modules} {K : Type u} (κ : K → I.ι)
  (hκ : Opens.IsBasis (Set.range fun k => (I.V (κ k)).1))
  (φ : ∀ k, S.M (κ k) →ₗ[Γ(Y, (I.V (κ k)).1)] Γ(H, (I.V (κ k)).1))
  (hφ : ∀ (k₁ k₂ : K) (y : Y), y ∈ (I.V (κ k₁)).1 → y ∈ (I.V (κ k₂)).1 →
    ∃ k₃, y ∈ (I.V (κ k₃)).1 ∧ ∃ (h₁ : I.Refines (κ k₃) (κ k₁)) (h₂ : I.Refines (κ k₃) (κ k₂)),
      (∀ x, H.presheaf.map (homOfLE (I.le_of_refines h₁)).op (φ k₁ x) = φ k₃ (S.ρ h₁ x)) ∧
      (∀ x, H.presheaf.map (homOfLE (I.le_of_refines h₂)).op (φ k₂ x) = φ k₃ (S.ρ h₂ x)))

/-- The maps on sections over the charts `κ k` induced by a family `φ`. -/
noncomputable def homOfFamilyApp (k : K) :
    S.sheaf.val.obj (op (I.V (κ k)).1) ⟶ H.val.obj (op (I.V (κ k)).1) :=
  ModuleCat.ofHom (X := S.sheaf.val.obj (op (I.V (κ k)).1)) (Y := H.val.obj (op (I.V (κ k)).1))
    ((φ k).comp (S.sectionsEquiv (κ k)).toLinearMap :
      Γ(S.sheaf, (I.V (κ k)).1) →ₗ[Γ(Y, (I.V (κ k)).1)] Γ(H, (I.V (κ k)).1))

include hφ in
/-- The maps `homOfFamilyApp` are compatible with the restriction maps between the members of
the basis. -/
theorem isCompatibleOnBasis_homOfFamilyApp :
    Stacks.BasisRestriction.IsCompatibleOnBasis S.sheaf H (fun k => (I.V (κ k)).1)
      (S.homOfFamilyApp κ φ) := by
  intro a b hba (s : Γ(S.sheaf, (I.V (κ a)).1))
  have hloc := fun (y : {y : Y // y ∈ (I.V (κ b)).1}) => hφ a b y (hba y.2) y.2
  choose k₃ hy₃ h₁ h₂ hφ₁ hφ₂ using hloc
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover H (fun y => (I.V (κ (k₃ y))).1)
    (fun y => I.le_of_refines (h₂ y)) (fun y hy => ⟨⟨y, hy⟩, hy₃ ⟨y, hy⟩⟩) _ _ fun y => ?_
  show H.presheaf.map (homOfLE (I.le_of_refines (h₂ y))).op
      (φ b (S.sectionsEquiv (κ b) (S.sheaf.presheaf.map (homOfLE hba).op s))) =
    H.presheaf.map (homOfLE (I.le_of_refines (h₂ y))).op
      (H.presheaf.map (homOfLE hba).op (φ a (S.sectionsEquiv (κ a) s)))
  rw [Scheme.Modules.presheaf_map_comp_apply, ← op_comp, homOfLE_comp, hφ₂ y, hφ₁ y,
    ← sectionsEquiv_restrict, ← sectionsEquiv_restrict]
  rfl

/-- **The morphism out of the glued sheaf determined by compatible maps on a basis of charts.**
Let `κ : K → ι` be a family of charts forming a basis of the topology, and `φ k : M (κ k) → Γ(H, V
(κ k))` a family of `Γ(Y, V (κ k))`-linear maps which near every point of an intersection
`V (κ k₁) ∩ V (κ k₂)` are compatible with a common member `φ k₃` of the family on a common
refinement. Then the `φ k` are the components of a morphism of sheaves of modules
`S.sheaf ⟶ H` (`AlgebraicGeometry.ChartModuleSystem.homOfFamily_app`). It is built by Stacks 009U
from its components on the basis. -/
noncomputable def homOfFamily : S.sheaf ⟶ H :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis S.sheaf H (fun k => (I.V (κ k)).1)
    (S.homOfFamilyApp κ φ) hκ (S.isCompatibleOnBasis_homOfFamilyApp κ φ hφ)

/-- The component of `homOfFamily κ φ` on a chart `κ k` is `φ k`. -/
theorem homOfFamily_app (k : K) (s : Γ(S.sheaf, (I.V (κ k)).1)) :
    (S.homOfFamily κ hκ φ hφ).app (I.V (κ k)).1 s = φ k (S.sectionsEquiv (κ k) s) := by
  exact congrArg (fun f : S.sheaf.val.obj (op (I.V (κ k)).1) ⟶ H.val.obj (op (I.V (κ k)).1) =>
    f s) (Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app S.sheaf H
      (fun k => (I.V (κ k)).1) (S.homOfFamilyApp κ φ) hκ
      (S.isCompatibleOnBasis_homOfFamilyApp κ φ hφ) k)

include hκ in
/-- **Two morphisms out of the glued sheaf agreeing on a basis of charts are equal.** -/
theorem hom_ext_of_isBasis {f g : S.sheaf ⟶ H}
    (h : ∀ k (x : S.M (κ k)), f.app (I.V (κ k)).1 ((S.sectionsEquiv (κ k)).symm x) =
      g.app (I.V (κ k)).1 ((S.sectionsEquiv (κ k)).symm x)) : f = g := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis S.sheaf H (fun k => (I.V (κ k)).1)
    hκ f g fun k => ?_
  ext s
  obtain ⟨x, rfl⟩ := (S.sectionsEquiv (κ k)).symm.surjective s
  exact h k x

end Hom

section HomOfCompatible

variable {H : Y.Modules} (φ : ∀ c, S.M c →ₗ[Γ(Y, (I.V c).1)] Γ(H, (I.V c).1))
  (hφ : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : S.M c),
    H.presheaf.map (homOfLE (I.le_of_refines h)).op (φ c x) = φ c' (S.ρ h x))

/-- **The morphism out of the glued sheaf determined by compatible maps on the charts.** A family
of `Γ(Y, V c)`-linear maps `φ c : M c → Γ(H, V c)` commuting with the restriction maps defines a
morphism of sheaves of modules `S.sheaf ⟶ H`, whose component on `V c` is `φ c` read through
`sectionsEquiv c`. -/
noncomputable def homOfCompatible : S.sheaf ⟶ H :=
  S.homOfFamily id I.isBasis φ fun c₁ c₂ _ hy₁ hy₂ => by
    obtain ⟨c₃, h₁, h₂, hy₃⟩ := I.exists_refines_refines hy₁ hy₂
    exact ⟨c₃, hy₃, h₁, h₂, hφ h₁, hφ h₂⟩

/-- The component of `homOfCompatible φ` on a chart is `φ`. -/
theorem homOfCompatible_app (c : I.ι) (s : Γ(S.sheaf, (I.V c).1)) :
    (S.homOfCompatible φ hφ).app (I.V c).1 s = φ c (S.sectionsEquiv c s) :=
  S.homOfFamily_app id I.isBasis φ _ c s

end HomOfCompatible

/-- **Two morphisms out of the glued sheaf agreeing on the charts are equal.** -/
theorem hom_ext {H : Y.Modules} {f g : S.sheaf ⟶ H}
    (h : ∀ c (x : S.M c), f.app (I.V c).1 ((S.sectionsEquiv c).symm x) =
      g.app (I.V c).1 ((S.sectionsEquiv c).symm x)) : f = g :=
  S.hom_ext_of_isBasis (κ := id) I.isBasis h

end AlgebraicGeometry.ChartModuleSystem
