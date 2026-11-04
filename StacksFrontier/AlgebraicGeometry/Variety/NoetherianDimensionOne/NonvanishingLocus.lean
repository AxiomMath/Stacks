module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.IsolatingFunction
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.StalkModule
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.TrivializedInvertible
public import StacksFrontier.Topology.Sheaves.Glueing.AlgebraicStructure

/-!
# A retrocompact open as the nonvanishing locus of a section of an invertible module

Let `U` be a retrocompact open of a scheme `X` whose complement is discrete and along which the
local rings are Noetherian of Krull dimension at most one. This file proves that `U` is the
nonvanishing open of a global section of an invertible `O_X`-module, which is
[Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA).

The module is built by gluing. The charts are `U` itself together with, for each point `x` of the
complement, an affine open `V x` on which `x` is both the only point of the complement and the
zero locus of a single regular function `f x`
(`AlgebraicGeometry.exists_isAffineOpen_isolating_point`). On `U` the chosen equation is `1`; on
`V x` it is `f x`. Over an open contained in two distinct charts the equation of each chart is a
unit, because such an open is contained in `U`, so the ratio of the two equations is an invertible
section, and these ratios form a multiplicative cocycle. Gluing one copy of the structure sheaf
per chart along that cocycle produces a module `L`, and the chart equations are compatible for it,
hence define a global section `s`.

Invertibility of `L` is read off from the tautological chart trivializations
(`Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization`), and the
nonvanishing locus of `s` is computed chart by chart: on a chart the germ of `s` generates the
stalk modulo the maximal ideal exactly when the germ of the chart equation is a unit, and that
happens exactly at the points of `U`.

## Main results

* `AlgebraicGeometry.exists_isInvertible_nonvanishingOpen_eq`: the invertible module and its
  section, with `U` as the nonvanishing open.

## Implementation notes

The gluing is performed for an arbitrary family of opens equipped with a multiplicative cocycle
of invertible sections (`AlgebraicGeometry.NoetherianDimensionOne.UnitCocycle`); the charts of
Tag 09NA only enter in the last section.

The nonvanishing locus is the canonical open of Tag 01CY
(`Stacks.SheafOfModules.nonvanishingOpen`), which takes the invertibility of the module as an
instance; the witness is therefore bound explicitly in the statement so that the open can be
formed without choosing an arbitrary instance.

Tag 01CY states the nonvanishing locus with the stalk module structure of Tag 01CB, while the
local computation is most naturally performed with Mathlib's stalk module structure on a presheaf
of modules. The two agree (`Stacks.SheafOfModules.stalkModule_eq`), and
`Stacks.SheafOfModules.mem_smul_top_congr` transports membership in `𝔪 • ⊤` across the equality;
that transport is the only place where the two spellings meet.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TopCat

universe u

namespace AlgebraicGeometry.NoetherianDimensionOne

section Glueing

variable {X : Scheme.{u}}

/-! ### Restriction of sections of the structure sheaf -/

/-- Restriction of sections of the structure sheaf of `X`, as a ring homomorphism between the
`RingCat`-valued rings of sections that `PresheafOfModules` is indexed by. -/
private def chartRes {W Z : X.Opens} (h : Z ≤ W) :
    (X.ringCatSheaf.obj.obj (op W) : Type u) →+* (X.ringCatSheaf.obj.obj (op Z) : Type u) :=
  (X.ringCatSheaf.obj.map (homOfLE h).op).hom

private lemma chartRes_comp {V W Z : X.Opens} (hWV : W ≤ V) (hZW : Z ≤ W) :
    chartRes (hZW.trans hWV) = (chartRes hZW).comp (chartRes hWV) := by
  ext x
  show (X.ringCatSheaf.obj.map (homOfLE (hZW.trans hWV)).op).hom x = _
  have hc : (homOfLE hWV).op ≫ (homOfLE hZW).op = (homOfLE (hZW.trans hWV)).op :=
    Subsingleton.elim _ _
  rw [← hc, Functor.map_comp]
  rfl

/-- Restricting twice is restricting once. -/
private lemma chartRes_chartRes {V W Z : X.Opens} (hWV : W ≤ V) (hZW : Z ≤ W)
    (x : (X.ringCatSheaf.obj.obj (op V) : Type u)) :
    chartRes hZW (chartRes hWV x) = chartRes (hZW.trans hWV) x := by
  rw [chartRes_comp hWV hZW]
  rfl

private lemma chartRes_mul_comm (W : X.Opens)
    (r s : X.ringCatSheaf.obj.obj (op W)) : r * s = s * r :=
  @mul_comm Γ(X, W) inferInstance r s

/-- Restriction of sections, as a homomorphism of the groups of invertible sections. -/
private def chartResUnits {W Z : X.Opens} (h : Z ≤ W) :
    (X.ringCatSheaf.obj.obj (op W) : Type u)ˣ →* (X.ringCatSheaf.obj.obj (op Z) : Type u)ˣ :=
  Units.map (chartRes h).toMonoidHom

/-! ### Glueing one copy of the structure sheaf per chart -/

/-- A multiplicative cocycle on a family of opens `V` of a scheme `X`: an invertible section over
every open contained in two members of the family, compatible with restriction and satisfying the
cocycle condition. Glueing one copy of the structure sheaf per member of the family along such a
cocycle produces an invertible module. -/
private structure UnitCocycle (X : Scheme.{u}) {ι : Type u} (V : ι → X.Opens) where
  /-- The comparison unit over an open contained in both `V i` and `V j`. -/
  unit : ∀ (i j : ι) {W : X.Opens}, W ≤ V i → W ≤ V j →
    (X.ringCatSheaf.obj.obj (op W) : Type u)ˣ
  /-- The comparison units are compatible with restriction. -/
  unit_res : ∀ (i j : ι) {W Z : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hZW : Z ≤ W),
    chartRes hZW (unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) =
      (unit i j (hZW.trans hi) (hZW.trans hj) : X.ringCatSheaf.obj.obj (op Z))
  /-- The cocycle condition. -/
  unit_trans : ∀ (i j k : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k),
    ((unit j k hj hk : X.ringCatSheaf.obj.obj (op W)) * (unit i j hi hj :
        X.ringCatSheaf.obj.obj (op W))) =
      (unit i k hi hk : X.ringCatSheaf.obj.obj (op W))

/-- The structure sheaf of `X`, read as a presheaf of sets on the opens contained in `W`. -/
private def chartLocalPresheaf (W : X.Opens) :
    TopCat.Sheaf.LocalPresheaf X.toPresheafedSpace W :=
  TopCat.Presheaf.toLocalPresheaf (X.ringCatSheaf.obj ⋙ CategoryTheory.forget RingCat) W

private lemma chartLocalPresheaf_isSheaf (W : X.Opens) :
    (chartLocalPresheaf (X := X) W).IsSheaf :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (CategoryTheory.forget RingCat) X.ringCatSheaf.obj).mp X.ringCatSheaf.property) W

/-- The structure sheaf of `X`, read as a presheaf of abelian groups on the opens contained
in `W`. -/
private def chartAddLocalPresheaf (W : X.Opens) :
    TopCat.Sheaf.AddLocalPresheaf X.toPresheafedSpace W where
  obj Z _ := AddCommGrpCat.of (X.ringCatSheaf.obj.obj (op Z) : Type u)
  map h := AddCommGrpCat.ofHom (chartRes h).toAddMonoidHom
  map_id := by
    intro W' hW'
    apply AddCommGrpCat.hom_ext
    ext x
    simp [chartRes]
  map_map h₁ h₂ := by
    apply AddCommGrpCat.hom_ext
    ext x
    change chartRes h₂ (chartRes h₁ x) = _
    rw [chartRes_comp h₁ h₂]
    rfl

private lemma chartAddLocalPresheaf_isSheaf (W : X.Opens) :
    (chartAddLocalPresheaf (X := X) W).toLocalPresheaf.IsSheaf :=
  chartLocalPresheaf_isSheaf W

variable {ι : Type u} {V : ι → X.Opens}

/-- The glueing datum of sheaves of abelian groups attached to a multiplicative cocycle: one copy
of the structure sheaf per chart, compared on an overlap by multiplication by the comparison
unit. -/
private def cocycleAddGlueData (c : UnitCocycle X V) :
    TopCat.Sheaf.AddGlueData X.toPresheafedSpace V where
  sheaf i := chartAddLocalPresheaf (V i)
  isSheaf i := chartAddLocalPresheaf_isSheaf (V i)
  trans i j {W} hi hj :=
    AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (X.ringCatSheaf.obj.obj (op W) : Type u))
      (Y := AddCommGrpCat.of (X.ringCatSheaf.obj.obj (op W) : Type u))
      (AddAut.mulLeft (c.unit i j hi hj))
  trans_map := by
    intro i j W Z hi hj hZW
    apply AddCommGrpCat.hom_ext
    ext x
    change (X.ringCatSheaf.obj.obj (op W) : Type u) at x
    change (c.unit i j (hZW.trans hi) (hZW.trans hj) : X.ringCatSheaf.obj.obj (op Z)) *
        chartRes hZW x =
      chartRes hZW ((c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * x)
    rw [map_mul, c.unit_res]
  trans_trans := by
    intro i j k W hi hj hk
    apply AddCommGrpCat.hom_ext
    ext x
    change (X.ringCatSheaf.obj.obj (op W) : Type u) at x
    change (c.unit j k hj hk : X.ringCatSheaf.obj.obj (op W)) *
        ((c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * x) =
      (c.unit i k hi hk : X.ringCatSheaf.obj.obj (op W)) * x
    rw [← mul_assoc, c.unit_trans]

/-- Restriction from `W` to `W ⊓ V i`, used as the scalar action on the `i`-th component of a
compatible family over `W`. -/
private def cocycleScalarRes (V : ι → X.Opens) (i : ι) (W : X.Opens) :
    (X.ringCatSheaf.obj.obj (op W) : Type u) →+*
      (X.ringCatSheaf.obj.obj (op (W ⊓ V i)) : Type u) :=
  chartRes (inf_le_left : W ⊓ V i ≤ W)

private instance cocycleAmbientModule (V : ι → X.Opens) (W : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (op W) : Type u)
      (∀ i : ι, (X.ringCatSheaf.obj.obj (op (W ⊓ V i)) : Type u)) := by
  letI : ∀ i : ι, Module (X.ringCatSheaf.obj.obj (op W) : Type u)
      (X.ringCatSheaf.obj.obj (op (W ⊓ V i)) : Type u) :=
    fun i => Module.compHom _ (cocycleScalarRes V i W)
  exact inferInstance

/-- The compatible families of sections over `W`, as a submodule of the product of the sections
over the `W ⊓ V i`. -/
private def cocycleSectionsSubmodule (c : UnitCocycle X V) (W : X.Opens) :
    Submodule (X.ringCatSheaf.obj.obj (op W) : Type u)
      (∀ i : ι, (X.ringCatSheaf.obj.obj (op (W ⊓ V i)) : Type u)) := by
  refine {
    carrier := ((cocycleAddGlueData c).sectionsAddSubgroup W).carrier
    zero_mem' := ((cocycleAddGlueData c).sectionsAddSubgroup W).zero_mem
    add_mem' := fun hs ht => ((cocycleAddGlueData c).sectionsAddSubgroup W).add_mem hs ht
    smul_mem' := ?_ }
  intro r s hs
  change ∀ i j : ι, _ = _ at hs
  intro i j
  have hri : chartRes (inf_le_left.trans inf_le_left :
        W ⊓ V i ⊓ (W ⊓ V j) ≤ W) r =
      chartRes (inf_le_left : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V i) (cocycleScalarRes V i W r) :=
    (chartRes_chartRes _ _ r).symm
  have hrj : chartRes (inf_le_right.trans inf_le_left :
        W ⊓ V i ⊓ (W ⊓ V j) ≤ W) r =
      chartRes (inf_le_right : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V j) (cocycleScalarRes V j W r) :=
    (chartRes_chartRes _ _ r).symm
  have hcompat := hs i j
  change (c.unit i j (W := W ⊓ V i ⊓ (W ⊓ V j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      X.ringCatSheaf.obj.obj (op (W ⊓ V i ⊓ (W ⊓ V j)))) *
      chartRes (inf_le_left : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V i) (s i) =
    chartRes (inf_le_right : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V j) (s j) at hcompat
  change (c.unit i j (W := W ⊓ V i ⊓ (W ⊓ V j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      X.ringCatSheaf.obj.obj (op (W ⊓ V i ⊓ (W ⊓ V j)))) *
      chartRes (inf_le_left : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V i)
        (cocycleScalarRes V i W r * s i) =
    chartRes (inf_le_right : W ⊓ V i ⊓ (W ⊓ V j) ≤ W ⊓ V j)
      (cocycleScalarRes V j W r * s j)
  rw [map_mul, map_mul, ← hri, ← hrj, ← mul_assoc,
    chartRes_mul_comm (W ⊓ V i ⊓ (W ⊓ V j)) _
      (chartRes (inf_le_left.trans inf_le_left : W ⊓ V i ⊓ (W ⊓ V j) ≤ W) r),
    mul_assoc, hcompat]

/-- The presheaf of modules glued from a multiplicative cocycle. -/
private noncomputable def cocycleModulePresheaf (c : UnitCocycle X V) :
    PresheafOfModules.{u} X.ringCatSheaf.obj := by
  letI : ∀ W : (X.Opens)ᵒᵖ,
      Module (X.ringCatSheaf.obj.obj W) ((cocycleAddGlueData c).gluedAddPresheaf.obj W) :=
    fun W => by
      change Module (X.ringCatSheaf.obj.obj W : Type u) (cocycleSectionsSubmodule c W.unop)
      infer_instance
  refine PresheafOfModules.ofPresheaf (cocycleAddGlueData c).gluedAddPresheaf ?_
  intro W Z f r s
  change cocycleSectionsSubmodule c W.unop at s
  let : Module (X.ringCatSheaf.obj.obj Z : Type u)
      ((cocycleAddGlueData c).sectionsAddSubgroup Z.unop) := by
    change Module (X.ringCatSheaf.obj.obj Z : Type u) (cocycleSectionsSubmodule c Z.unop)
    infer_instance
  apply Subtype.ext
  funext i
  change chartRes (inf_le_inf_right (V i) f.unop.le)
      (cocycleScalarRes V i W.unop r * s.1 i) =
    cocycleScalarRes V i Z.unop ((X.ringCatSheaf.obj.map f).hom r) *
      chartRes (inf_le_inf_right (V i) f.unop.le) (s.1 i)
  rw [map_mul]
  congr 1
  change chartRes (inf_le_inf_right (V i) f.unop.le) (chartRes inf_le_left r) =
    chartRes inf_le_left (chartRes f.unop.le r)
  rw [chartRes_chartRes, chartRes_chartRes]

/-- The sheaf of modules glued from a multiplicative cocycle. -/
private noncomputable def cocycleModule (c : UnitCocycle X V) :
    SheafOfModules.{u} X.ringCatSheaf where
  val := cocycleModulePresheaf c
  isSheaf := (cocycleAddGlueData c).gluedAddPresheaf_isSheaf

/-- The tautological trivialization of the glued module on a chart, as a linear equivalence on
sections over an open contained in that chart. -/
private noncomputable def cocycleSectionsLinearEquiv (c : UnitCocycle X V) (i : ι)
    {W : X.Opens} (hW : W ≤ V i) :
    (cocycleModule c).val.obj (op W) ≃ₗ[X.ringCatSheaf.obj.obj (op W)]
      (X.ringCatSheaf.obj.obj (op W)) := by
  refine { __ := (cocycleAddGlueData c).toGlueData.sectionsEquiv i hW
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    change chartRes (le_inf le_rfl hW) (s.1 i + t.1 i) = _
    exact map_add _ _ _
  · intro r s
    change cocycleSectionsSubmodule c W at s
    change chartRes (le_inf le_rfl hW) (cocycleScalarRes V i W r * s.1 i) =
      r * chartRes (le_inf le_rfl hW) (s.1 i)
    rw [map_mul]
    congr 1
    change chartRes (le_inf le_rfl hW) (chartRes inf_le_left r) = r
    rw [chartRes_chartRes]
    change (X.ringCatSheaf.obj.map (𝟙 (op W))).hom r = r
    simp

/-- The tautological trivialization of the glued module on a chart, in the form consumed by
`Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization`. -/
private noncomputable def cocycleTrivialization (c : UnitCocycle X V) (i : ι) :
    Stacks.SheafOfModules.Trivialized.Trivialization X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        (cocycleModule c) (V i) :=
  PresheafOfModules.isoMk (fun W =>
    (cocycleSectionsLinearEquiv c i W.unop.hom.le).toModuleIso) (by
      intro W W' f
      ext s
      exact (cocycleAddGlueData c).toGlueData.sectionsEquiv_map i
        W.unop.hom.le f.unop.left.le s)

/-- **The glued module is invertible**, by Tag 0B8M, since it is trivial on each chart. -/
private lemma cocycleModule_isInvertible (c : UnitCocycle X V)
    (hcover : TopologicalSpace.IsOpenCover V) :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        (cocycleModule c) :=
  Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization
    ((Opens.coversTop_iff X.carrier V).mpr hcover) (cocycleTrivialization c)

/-- The global section of the glued module determined by a compatible family of chart
equations. -/
private noncomputable def cocycleSection (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j)) :
    (cocycleModule c).sections := by
  refine PresheafOfModules.sectionsMk (M := (cocycleModule c).val)
    (fun W => ⟨fun i => chartRes inf_le_right (t i), ?_⟩) ?_
  · intro i j
    change (c.unit i j (W := W.unop ⊓ V i ⊓ (W.unop ⊓ V j))
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        X.ringCatSheaf.obj.obj (op (W.unop ⊓ V i ⊓ (W.unop ⊓ V j)))) *
        chartRes inf_le_left (chartRes inf_le_right (t i)) =
      chartRes inf_le_right (chartRes inf_le_right (t j))
    rw [chartRes_chartRes, chartRes_chartRes]
    exact ht i j _ _
  · intro W Z f
    apply Subtype.ext
    funext i
    change chartRes (inf_le_inf_right (V i) f.unop.le) (chartRes inf_le_right (t i)) =
      chartRes inf_le_right (t i)
    rw [chartRes_chartRes]

private lemma cocycleSection_trivialization (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j))
    (i : ι) {W : X.Opens} (hW : W ≤ V i) :
    cocycleSectionsLinearEquiv c i hW ((cocycleSection c t ht).eval (op W)) =
      chartRes hW (t i) := by
  show chartRes (le_inf le_rfl hW) (chartRes inf_le_right (t i)) = _
  rw [chartRes_chartRes]

/-! ### The stalks of the glued module -/

/-- The cocone, over the neighbourhoods of a point `x` of the chart `V i`, given by taking the
`i`-th component of a compatible family and its germ at `x`. -/
private noncomputable def cocycleStalkCocone (c : UnitCocycle X V) (i : ι) (x : X)
    (hx : x ∈ V i) :
    CategoryTheory.Limits.Cocone ((OpenNhds.inclusion x).op ⋙
      (cocycleModule c).val.presheaf) := by
  refine {
    pt := AddCommGrpCat.of (X.presheaf.stalk x)
    ι := {
      app W := AddCommGrpCat.ofHom {
        toFun s := X.presheaf.germ (W.unop.1 ⊓ V i) x ⟨W.unop.2, hx⟩ (s.1 i)
        map_zero' := by
          change X.presheaf.germ (W.unop.1 ⊓ V i) x _ 0 = 0
          exact map_zero _
        map_add' _ _ := map_add _ _ _ }
      naturality W Z f := by
        apply AddCommGrpCat.hom_ext
        ext s
        change X.presheaf.germ (Z.unop.1 ⊓ V i) x _
            (X.presheaf.map (homOfLE (inf_le_inf_right (V i) f.unop.le)).op (s.1 i)) = _
        exact X.presheaf.germ_res_apply _ _ _ _ } }

/-- The projection of the stalk of the glued module to the stalk of the structure sheaf, read in
the chart `V i`. -/
private noncomputable def cocycleStalkProjection (c : UnitCocycle X V) (i : ι) (x : X)
    (hx : x ∈ V i) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (cocycleModule c).val.presheaf x →+
      X.presheaf.stalk x :=
  (CategoryTheory.Limits.colimit.desc _ (cocycleStalkCocone c i x hx)).hom

private lemma cocycleStalkProjection_germ (c : UnitCocycle X V) (i : ι) (x : X)
    (hx : x ∈ V i) (W : X.Opens) (hxW : x ∈ W)
    (s : (cocycleModule c).val.obj (op W)) :
    cocycleStalkProjection c i x hx
        (TopCat.Presheaf.germ (cocycleModule c).val.presheaf W x hxW s) =
      X.presheaf.germ (W ⊓ V i) x ⟨hxW, hx⟩ (s.1 i) :=
  congrArg (fun q : (cocycleModule c).val.presheaf.obj (op W) ⟶
      AddCommGrpCat.of (X.presheaf.stalk x) => q.hom s)
    (CategoryTheory.Limits.colimit.ι_desc (cocycleStalkCocone c i x hx)
      (op (⟨W, hxW⟩ : OpenNhds x)))

/-- The projection to the stalk of the structure sheaf is linear. -/
private noncomputable def cocycleStalkProjectionLinearMap (c : UnitCocycle X V) (i : ι) (x : X)
    (hx : x ∈ V i) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (cocycleModule c).val.presheaf x →ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x := by
  refine { __ := cocycleStalkProjection c i x hx
           map_smul' := ?_ }
  intro r m
  change cocycleStalkProjection c i x hx (r • m) =
    r * cocycleStalkProjection c i x hx m
  obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Z, hZW, hxZ, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
    (cocycleModule c).val.presheaf m hxW
  rw [← X.presheaf.germ_res_apply (homOfLE hZW) x hxZ r]
  refine (congrArg (cocycleStalkProjection c i x hx) (PresheafOfModules.germ_smul (R := X.presheaf)
    (cocycleModule c).val x Z hxZ ((X.presheaf.map (homOfLE hZW).op) r) s)).symm.trans
    ((cocycleStalkProjection_germ c i x hx Z hxZ _).trans ?_)
  change X.presheaf.germ (Z ⊓ V i) x _
      (X.presheaf.map (homOfLE (show Z ⊓ V i ≤ Z from inf_le_left)).op
        (X.presheaf.map (homOfLE hZW).op r) *
          (show Γ(X, Z ⊓ V i) from s.1 i)) = _
  rw [cocycleStalkProjection_germ c i x hx Z hxZ s, map_mul,
    ← X.presheaf.germ_res_apply (homOfLE (show Z ⊓ V i ≤ Z from inf_le_left)) x
      (show x ∈ Z ⊓ V i from ⟨hxZ, hx⟩) _]

private lemma cocycleStalkProjection_section (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j))
    (i : ι) (x : X) (hx : x ∈ V i) :
    cocycleStalkProjectionLinearMap c i x hx
      (TopCat.Presheaf.Γgerm (cocycleModule c).val.presheaf x
        ((cocycleSection c t ht).eval (op ⊤))) =
      X.presheaf.germ (V i) x hx (t i) := by
  show cocycleStalkProjection c i x hx
      (TopCat.Presheaf.germ (C := Ab.{u}) (cocycleModule c).val.presheaf ⊤ x (Opens.mem_top x)
        ((cocycleSection c t ht).eval (op ⊤))) = X.presheaf.germ (V i) x hx (t i)
  refine (cocycleStalkProjection_germ c i x hx ⊤ (Opens.mem_top x) _).trans ?_
  exact X.presheaf.germ_res_apply (homOfLE inf_le_right) x _ _

/-- The germ of a global section at a point of `W` is the germ there of its restriction
to `W`. -/
private lemma glueSectionGerm_eq (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)
    (s : M.sections) (W : X.Opens) (x : X) (hx : x ∈ W) :
    TopCat.Presheaf.Γgerm M.val.presheaf x (s.eval (op ⊤)) =
      TopCat.Presheaf.germ M.val.presheaf W x hx (s.eval (op W)) := by
  rw [← TopCat.Presheaf.Γgerm_res_apply M.val.presheaf (i := homOfLE le_top) x hx]
  exact congrArg (TopCat.Presheaf.germ M.val.presheaf W x hx) (s.property (homOfLE le_top).op)

/-- If the chart equation of `V i` has a unit germ at `x`, then the glued section is nonvanishing
at `x`: the projection to the stalk of the structure sheaf carries `𝔪_x L_x` into `𝔪_x` and sends
the germ of the section to the germ of the chart equation. -/
private lemma cocycleSection_mem_nonvanishingLocus (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j))
    (i : ι) (x : X) (hx : x ∈ V i)
    (hu : IsUnit (X.presheaf.germ (V i) x hx (t i))) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (cocycleModule c)
      (cocycleSection c t ht) := by
  have hinst := Stacks.SheafOfModules.stalkModule_eq (X := X.toRingedSpace)
    (cocycleModule c).val x
  intro h
  have h' : TopCat.Presheaf.Γgerm (C := Ab.{u}) (cocycleModule c).val.presheaf x
      ((cocycleSection c t ht).eval (op ⊤)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (cocycleModule c).val.presheaf x)) :=
    (Stacks.SheafOfModules.mem_smul_top_congr hinst _ _).mp h
  apply IsLocalRing.notMem_maximalIdeal.mpr hu
  rw [← cocycleStalkProjection_section c t ht i x hx]
  refine Submodule.smul_induction_on h' ?_ ?_
  · intro r hr m _
    rw [map_smul]
    exact Ideal.mul_mem_right _ _ hr
  · intro r s hr hs
    rw [map_add]
    exact add_mem hr hs

/-- If the chart equation of `V i` has a germ in the maximal ideal at `x`, then the glued section
vanishes at `x`: in the chart trivialization the section is the chart equation times a basis
section. -/
private lemma cocycleSection_notMem_nonvanishingLocus (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j))
    (i : ι) (x : X) (hx : x ∈ V i)
    (hm : X.presheaf.germ (V i) x hx (t i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    x ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (cocycleModule c)
      (cocycleSection c t ht) := by
  have hinst := Stacks.SheafOfModules.stalkModule_eq (X := X.toRingedSpace)
    (cocycleModule c).val x
  have hs : (cocycleSection c t ht).eval (op (V i)) =
      t i • (cocycleSectionsLinearEquiv c i (le_refl (V i))).symm 1 := by
    apply (cocycleSectionsLinearEquiv c i (le_refl (V i))).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    have he := cocycleSection_trivialization c t ht i (le_refl (V i))
    change cocycleSectionsLinearEquiv c i (le_refl (V i))
      ((cocycleSection c t ht).eval (op (V i))) =
        (X.ringCatSheaf.obj.map (𝟙 (op (V i)))).hom (t i) at he
    rw [CategoryTheory.Functor.map_id] at he
    simpa only [RingCat.id_apply, smul_eq_mul, mul_one] using he
  intro hn
  apply hn
  refine (Stacks.SheafOfModules.mem_smul_top_congr hinst _ _).mpr ?_
  rw [show (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace (cocycleModule
    c).val x ⊤ (Opens.mem_top x)
        ((cocycleSection c t ht).eval (op ⊤)) :
        TopCat.Presheaf.stalk (C := Ab.{u}) (cocycleModule c).val.presheaf x) =
      TopCat.Presheaf.Γgerm (cocycleModule c).val.presheaf x
        ((cocycleSection c t ht).eval (op ⊤)) from rfl,
    glueSectionGerm_eq X (cocycleModule c) _ (V i) x hx, hs]
  exact (congrArg (· ∈ _)
    (PresheafOfModules.germ_smul (R := X.presheaf) (cocycleModule c).val x (V i) hx _ _)).mpr
    (Submodule.smul_mem_smul hm Submodule.mem_top)

/-- **The nonvanishing locus of the glued section, computed in a chart.** The glued section is
nonvanishing at a point of `V i` exactly when the germ there of the chart equation `t i` is a
unit. -/
private lemma cocycleSection_mem_nonvanishingLocus_iff (c : UnitCocycle X V)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (V i)) : Type u))
    (ht : ∀ (i j : ι) {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j),
      (c.unit i j hi hj : X.ringCatSheaf.obj.obj (op W)) * chartRes hi (t i) =
        chartRes hj (t j))
    (i : ι) (x : X) (hx : x ∈ V i) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (cocycleModule c)
      (cocycleSection c t ht) ↔ IsUnit (X.presheaf.germ (V i) x hx (t i)) := by
  refine ⟨fun h => ?_, cocycleSection_mem_nonvanishingLocus c t ht i x hx⟩
  by_contra hu
  exact cocycleSection_notMem_nonvanishingLocus c t ht i x hx
    (IsLocalRing.notMem_maximalIdeal.not_right.mp hu) h

end Glueing

/-! ### Glueing along a family of chart equations -/

section ChartFamily

variable {X : Scheme.{u}} {U : X.Opens}

/-- A *chart family* for an open `U` of a scheme `X`: an open cover of `X`, one chart equation per
member of the cover whose restriction to any open contained both in `U` and in that member is
invertible, and such that two distinct members of the cover meet only inside `U`.

The ratios of the chart equations then form a multiplicative cocycle, so one copy of the structure
sheaf per chart glues to an invertible module, and the chart equations glue to a global section
whose nonvanishing locus is `U`. -/
private structure ChartFamily (X : Scheme.{u}) (U : X.Opens) where
  /-- The index type of the cover. -/
  ι : Type u
  /-- The cover. -/
  opens : ι → X.Opens
  /-- It is a cover. -/
  cover : TopologicalSpace.IsOpenCover opens
  /-- The chart equations. -/
  equation : ∀ i, (X.ringCatSheaf.obj.obj (op (opens i)) : Type u)
  /-- A chart equation is invertible on an open contained both in `U` and in its chart. -/
  isUnit_res : ∀ (i : ι) {W : X.Opens}, W ≤ U → ∀ h : W ≤ opens i,
    IsUnit (chartRes h (equation i))
  /-- Two distinct charts meet only inside `U`. -/
  inter_le : ∀ i j : ι, i ≠ j → opens i ⊓ opens j ≤ U

/-- The chart equation of `V i`, read as an invertible section over an open contained both in `U`
and in `V i`. -/
private noncomputable def ChartFamily.frame (F : ChartFamily X U) (i : F.ι) {W : X.Opens}
    (hWU : W ≤ U) (hWi : W ≤ F.opens i) : (X.ringCatSheaf.obj.obj (op W) : Type u)ˣ :=
  (F.isUnit_res i hWU hWi).unit

private lemma ChartFamily.frame_val (F : ChartFamily X U) (i : F.ι) {W : X.Opens}
    (hWU : W ≤ U) (hWi : W ≤ F.opens i) :
    (F.frame i hWU hWi : X.ringCatSheaf.obj.obj (op W)) = chartRes hWi (F.equation i) :=
  IsUnit.unit_spec _

private lemma ChartFamily.frame_res (F : ChartFamily X U) (i : F.ι) {W Z : X.Opens}
    (hWU : W ≤ U) (hWi : W ≤ F.opens i) (hZW : Z ≤ W) :
    chartResUnits hZW (F.frame i hWU hWi) =
      F.frame i (hZW.trans hWU) (hZW.trans hWi) := by
  apply Units.ext
  show chartRes hZW (F.frame i hWU hWi : X.ringCatSheaf.obj.obj (op W)) = _
  rw [F.frame_val, F.frame_val, chartRes_chartRes]

open scoped Classical in
/-- The comparison unit of a chart family: the ratio of the two chart equations, which makes sense
because an open contained in two distinct charts is contained in `U`. -/
private noncomputable def ChartFamily.cocycleUnit (F : ChartFamily X U) (i j : F.ι)
    {W : X.Opens} (hi : W ≤ F.opens i) (hj : W ≤ F.opens j) :
    (X.ringCatSheaf.obj.obj (op W) : Type u)ˣ :=
  if h : i = j then 1
  else
    F.frame j ((le_inf hi hj).trans (F.inter_le i j h)) hj *
      (F.frame i ((le_inf hi hj).trans (F.inter_le i j h)) hi)⁻¹

private lemma ChartFamily.cocycleUnit_self (F : ChartFamily X U) (i : F.ι) {W : X.Opens}
    (hi hi' : W ≤ F.opens i) : F.cocycleUnit i i hi hi' = 1 := by
  unfold ChartFamily.cocycleUnit
  split
  · rfl
  · exact absurd rfl ‹¬i = i›

/-- Over an open contained in `U` the comparison unit is the ratio of the two chart equations,
whether or not the two charts are distinct. -/
private lemma ChartFamily.cocycleUnit_of_le (F : ChartFamily X U) (i j : F.ι) {W : X.Opens}
    (hi : W ≤ F.opens i) (hj : W ≤ F.opens j) (hWU : W ≤ U) :
    F.cocycleUnit i j hi hj = F.frame j hWU hj * (F.frame i hWU hi)⁻¹ := by
  unfold ChartFamily.cocycleUnit
  split
  · subst ‹i = j›
    exact (mul_inv_cancel _).symm
  · rfl

private lemma ChartFamily.cocycleUnit_res (F : ChartFamily X U) (i j : F.ι) {W Z : X.Opens}
    (hi : W ≤ F.opens i) (hj : W ≤ F.opens j) (hZW : Z ≤ W) :
    chartResUnits hZW (F.cocycleUnit i j hi hj) =
      F.cocycleUnit i j (hZW.trans hi) (hZW.trans hj) := by
  by_cases hij : i = j
  · subst hij
    rw [F.cocycleUnit_self, F.cocycleUnit_self, map_one]
  · have hWU : W ≤ U := (le_inf hi hj).trans (F.inter_le i j hij)
    rw [F.cocycleUnit_of_le i j hi hj hWU,
      F.cocycleUnit_of_le i j (hZW.trans hi) (hZW.trans hj) (hZW.trans hWU),
      map_mul, map_inv, F.frame_res, F.frame_res]

private lemma ChartFamily.cocycleUnit_trans (F : ChartFamily X U) (i j k : F.ι) {W : X.Opens}
    (hi : W ≤ F.opens i) (hj : W ≤ F.opens j) (hk : W ≤ F.opens k) :
    F.cocycleUnit j k hj hk * F.cocycleUnit i j hi hj = F.cocycleUnit i k hi hk := by
  by_cases hij : i = j
  · subst hij
    rw [F.cocycleUnit_self, mul_one]
  · by_cases hjk : j = k
    · subst hjk
      rw [F.cocycleUnit_self, one_mul]
    · have hWU : W ≤ U := (le_inf hi hj).trans (F.inter_le i j hij)
      rw [F.cocycleUnit_of_le i j hi hj hWU, F.cocycleUnit_of_le j k hj hk hWU,
        F.cocycleUnit_of_le i k hi hk hWU]
      group

/-- The multiplicative cocycle of a chart family. -/
private noncomputable def ChartFamily.cocycle (F : ChartFamily X U) :
    UnitCocycle X F.opens where
  unit i j {_W} hi hj := F.cocycleUnit i j hi hj
  unit_res i j {_W _Z} hi hj hZW := congrArg Units.val (F.cocycleUnit_res i j hi hj hZW)
  unit_trans i j k {_W} hi hj hk := congrArg Units.val (F.cocycleUnit_trans i j k hi hj hk)

/-- The chart equations of a chart family are compatible for its cocycle. -/
private lemma ChartFamily.equation_compatible (F : ChartFamily X U) (i j : F.ι) {W : X.Opens}
    (hi : W ≤ F.opens i) (hj : W ≤ F.opens j) :
    (F.cocycleUnit i j hi hj : X.ringCatSheaf.obj.obj (op W)) *
        chartRes hi (F.equation i) =
      chartRes hj (F.equation j) := by
  by_cases hij : i = j
  · subst hij
    rw [F.cocycleUnit_self, Units.val_one, one_mul]
  · have hWU : W ≤ U := (le_inf hi hj).trans (F.inter_le i j hij)
    rw [F.cocycleUnit_of_le i j hi hj hWU, ← F.frame_val i hWU hi, ← F.frame_val j hWU hj]
    show ((F.frame j hWU hj * (F.frame i hWU hi)⁻¹ * F.frame i hWU hi :
      (X.ringCatSheaf.obj.obj (op W) : Type u)ˣ) : X.ringCatSheaf.obj.obj (op W)) = _
    rw [inv_mul_cancel_right]

/-- The invertible module glued from a chart family. -/
private noncomputable def ChartFamily.module (F : ChartFamily X U) :
    SheafOfModules.{u} X.ringCatSheaf :=
  cocycleModule F.cocycle

private lemma ChartFamily.module_isInvertible (F : ChartFamily X U) :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        F.module :=
  cocycleModule_isInvertible F.cocycle F.cover

/-- The global section of the glued module given by the chart equations. -/
private noncomputable def ChartFamily.globalSection (F : ChartFamily X U) : F.module.sections :=
  cocycleSection F.cocycle F.equation (fun i j {_W} hi hj => F.equation_compatible i j hi hj)

/-- **The nonvanishing locus of the glued section, computed in a chart.** -/
private lemma ChartFamily.mem_nonvanishingLocus_iff (F : ChartFamily X U) (i : F.ι) (x : X)
    (hx : x ∈ F.opens i) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) F.module
        F.globalSection ↔
      IsUnit (X.presheaf.germ (F.opens i) x hx (F.equation i)) :=
  cocycleSection_mem_nonvanishingLocus_iff F.cocycle F.equation
    (fun i j {_W} hi hj => F.equation_compatible i j hi hj) i x hx

end ChartFamily

/-! ### The charts of Tag 09NA -/

section Charts

/-- The data isolating a point `x` of the complement of `U`: an affine open neighbourhood on which
`x` is the only point of the complement, and a regular function cutting out `x`. -/
private structure PointChart {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ (U : Set X)ᶜ) where
  /-- The affine open neighbourhood. -/
  V : X.Opens
  /-- It is affine. -/
  affine : IsAffineOpen V
  /-- It contains `x`. -/
  point_mem : x ∈ V
  /-- It meets the complement of `U` only in `x`. -/
  complement : (V : Set X) ∩ (U : Set X)ᶜ = {x}
  /-- The equation. -/
  f : Γ(X, V)
  /-- It cuts out `x`. -/
  zero : (V : Set X) \ (X.basicOpen f : Set X) = {x}

/-- A chart equation is invertible away from the point it cuts out, in particular on any open
contained both in `U` and in the chart. -/
private lemma pointChart_isUnit_res {X : Scheme.{u}} {U : X.Opens} {x : X}
    {hx : x ∈ (U : Set X)ᶜ} (c : PointChart U x hx) {W : X.Opens}
    (hWU : W ≤ U) (hWV : W ≤ c.V) :
    IsUnit (chartRes hWV (c.f : X.ringCatSheaf.obj.obj (op c.V))) := by
  have hWbasic : W ≤ X.basicOpen c.f := by
    intro y hy
    by_contra hyb
    have hy0 : y ∈ (c.V : Set X) \ (X.basicOpen c.f : Set X) := ⟨hWV hy, hyb⟩
    rw [c.zero, Set.mem_singleton_iff] at hy0
    exact hx (hy0 ▸ hWU hy)
  apply X.toRingedSpace.isUnit_of_isUnit_germ W
  intro y hy
  rw [show X.presheaf.germ W y hy (chartRes hWV (c.f : X.ringCatSheaf.obj.obj (op c.V))) =
      X.presheaf.germ c.V y (hWV hy) c.f from
    X.presheaf.germ_res_apply (homOfLE hWV) y hy c.f]
  exact (X.mem_basicOpen c.f y (hWV hy)).mp (hWbasic hy)

/-- The germ of a chart equation at a point of its chart is a unit exactly at the points of `U`:
the zero locus of the equation in the chart is the distinguished point, which is the only point of
the complement of `U` there. -/
private lemma pointChart_germ_isUnit_iff {X : Scheme.{u}} {U : X.Opens} {y : X}
    {hy : y ∈ (U : Set X)ᶜ} (c : PointChart U y hy) (x : X) (hx : x ∈ c.V) :
    IsUnit (X.presheaf.germ c.V x hx c.f) ↔ x ∈ U := by
  rw [← X.mem_basicOpen c.f x hx]
  refine ⟨fun hxb => ?_, fun hxU => ?_⟩
  · by_contra hxU
    have hxy : x = y := by
      apply Set.mem_singleton_iff.mp
      rw [← c.complement]
      exact ⟨hx, by simpa using hxU⟩
    have hzero : x ∈ (c.V : Set X) \ (X.basicOpen c.f : Set X) := by
      rw [c.zero]
      exact Set.mem_singleton_iff.mpr hxy
    exact hzero.2 hxb
  · by_contra hxb
    have hzero : x ∈ (c.V : Set X) \ (X.basicOpen c.f : Set X) := ⟨hx, hxb⟩
    rw [c.zero, Set.mem_singleton_iff] at hzero
    exact hy (hzero ▸ hxU)

variable (X : Scheme.{u}) (U : X.Opens)
  (hU : IsRetrocompact (U : Set X)) [DiscreteTopology (Uᶜ : Set X)]
  (h_noetherian : ∀ x : X, x ∈ (U : Set X)ᶜ → IsNoetherianRing (X.presheaf.stalk x))
  (h_dimension : ∀ x : X, x ∈ (U : Set X)ᶜ → Ring.KrullDimLE 1 (X.presheaf.stalk x))

/-- A choice of isolating data at each point of the complement of `U`, from Tag 0623. -/
private noncomputable def pointChartOf (x : X) (hx : x ∈ (U : Set X)ᶜ) : PointChart U x hx := by
  classical
  let h := exists_isAffineOpen_isolating_point X U hU h_noetherian h_dimension x hx
  let V := Classical.choose h
  have hV := Classical.choose_spec h
  exact ⟨V, hV.1, hV.2.1, hV.2.2.1, Classical.choose hV.2.2.2,
    Classical.choose_spec hV.2.2.2⟩

/-- A point of the complement of `U`. -/
private abbrev ComplementPoint : Type u := {x : X // x ∈ (U : Set X)ᶜ}

/-- The index set of the chart cover: `U` itself, plus one chart per point of the complement. -/
private abbrev ChartIndex : Type u := Option (ComplementPoint X U)

/-- The chart cover: `U` itself, plus the isolating neighbourhood of each point of the
complement. -/
private noncomputable def chartOpen : ChartIndex X U → X.Opens
  | none => U
  | some y => (pointChartOf X U hU h_noetherian h_dimension y.1 y.2).V

/-- The chart equations: `1` on `U`, and the isolating function on the chart of a point of the
complement. -/
private noncomputable def chartEquation (i : ChartIndex X U) :
    Γ(X, chartOpen X U hU h_noetherian h_dimension i) :=
  match i with
  | none => 1
  | some y => (pointChartOf X U hU h_noetherian h_dimension y.1 y.2).f

private lemma chartOpen_isOpenCover :
    TopologicalSpace.IsOpenCover (chartOpen X U hU h_noetherian h_dimension) := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun i => (chartOpen X U hU h_noetherian h_dimension i).2)
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hx : x ∈ U
  · exact ⟨none, hx⟩
  · refine ⟨some ⟨x, by simpa using hx⟩, ?_⟩
    simpa [chartOpen] using
      (pointChartOf X U hU h_noetherian h_dimension x (by simpa using hx)).point_mem

/-- Two distinct charts meet only inside `U`: a point of the complement lying in two isolating
neighbourhoods would be both of their distinguished points. -/
private lemma chartOpen_inter_le (i j : ChartIndex X U) (hij : i ≠ j) :
    chartOpen X U hU h_noetherian h_dimension i ⊓
      chartOpen X U hU h_noetherian h_dimension j ≤ U := by
  cases i with
  | none => exact inf_le_left
  | some y =>
    cases j with
    | none => exact inf_le_right
    | some z =>
      intro w hw
      by_contra hwU
      have hwC : w ∈ (U : Set X)ᶜ := by simpa using hwU
      have hwy : w = y.1 := by
        apply Set.mem_singleton_iff.mp
        rw [← (pointChartOf X U hU h_noetherian h_dimension y.1 y.2).complement]
        exact ⟨hw.1, hwC⟩
      have hwz : w = z.1 := by
        apply Set.mem_singleton_iff.mp
        rw [← (pointChartOf X U hU h_noetherian h_dimension z.1 z.2).complement]
        exact ⟨hw.2, hwC⟩
      exact hij (congrArg some (Subtype.ext (hwy.symm.trans hwz)))

/-- The chart family of Tag 09NA. -/
private noncomputable def chartFamily : ChartFamily X U where
  ι := ChartIndex X U
  opens := chartOpen X U hU h_noetherian h_dimension
  cover := chartOpen_isOpenCover X U hU h_noetherian h_dimension
  equation := chartEquation X U hU h_noetherian h_dimension
  isUnit_res i {_W} hWU h := by
    cases i with
    | none =>
      rw [show chartRes h (chartEquation X U hU h_noetherian h_dimension none) = 1 from
        map_one (chartRes h)]
      exact isUnit_one
    | some y => exact pointChart_isUnit_res _ hWU h
  inter_le := chartOpen_inter_le X U hU h_noetherian h_dimension

/-- **The chart equation of `V i` has a unit germ at a point of `V i` exactly at the points
of `U`.** On the chart of a point `y` of the complement this is the defining property of the
isolating function: its zero locus in that chart is `{y}`, and `y` is the only point of the
complement there. -/
private lemma chartEquation_germ_isUnit_iff (i : ChartIndex X U) (x : X)
    (hx : x ∈ chartOpen X U hU h_noetherian h_dimension i) :
    IsUnit (X.presheaf.germ (chartOpen X U hU h_noetherian h_dimension i) x hx
        (chartEquation X U hU h_noetherian h_dimension i)) ↔ x ∈ U := by
  cases i with
  | none => exact iff_of_true (by simp [chartEquation]) hx
  | some y => exact pointChart_germ_isUnit_iff _ x hx

end Charts

end AlgebraicGeometry.NoetherianDimensionOne

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 09NA.** A retrocompact open with discrete complement along which the
local rings are Noetherian of Krull dimension at most one is the nonvanishing open of a global
section of an invertible module. -/
@[stacks 09NA "nonvanishing_locus"]
theorem exists_isInvertible_nonvanishingOpen_eq
    (X : Scheme.{u}) (U : X.Opens)
    (hU : IsRetrocompact (U : Set X))
    [DiscreteTopology (Uᶜ : Set X)]
    (h_noetherian : ∀ x : X, x ∈ (U : Set X)ᶜ →
      IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, x ∈ (U : Set X)ᶜ →
      Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
          L)
      (s : L.sections),
      U = (letI := hL
           Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s) := by
  open NoetherianDimensionOne in
  let F := chartFamily X U hU h_noetherian h_dimension
  refine ⟨F.module, F.module_isInvertible, F.globalSection, ?_⟩
  ext x
  show x ∈ U ↔ x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
    F.module F.globalSection
  obtain ⟨i, hx⟩ := TopologicalSpace.IsOpenCover.exists_mem F.cover x
  exact ((F.mem_nonvanishingLocus_iff i x hx).trans
    (chartEquation_germ_isUnit_iff X U hU h_noetherian h_dimension i x hx)).symm

end AlgebraicGeometry

end
