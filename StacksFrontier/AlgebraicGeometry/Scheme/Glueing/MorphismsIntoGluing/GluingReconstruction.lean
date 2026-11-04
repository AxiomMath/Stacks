module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.LocallyRingedSpaces

/-!
# Morphisms into a gluing of locally ringed spaces

A locally ringed space covered by open subspaces that map compatibly to the pieces of a gluing
datum admits a unique morphism to the glued space inducing those maps.

This is the reconstruction half of the mapping property for morphisms into a gluing: the other
half, which describes a given morphism into the gluing through its pullbacks to the canonical
charts, is in
`StacksFrontier.AlgebraicGeometry.Scheme.Glueing.LocallyRingedSpaces`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCoverGlueData`: an open covering of a
  locally ringed space, read as a gluing datum.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCoverFromGlued`: the comparison morphism
  from that gluing to the covered space.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCoverFromGlued_isIso`: that comparison
  morphism is an isomorphism, so a locally ringed space is the gluing of any open covering of
  itself.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.existsUnique_hom_of_openCover`: morphisms of
  locally ringed spaces glue over an open covering of the source — compatible morphisms out of
  the members of the covering come from a unique morphism out of the covered space.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext_of_openCover`: two morphisms of locally
  ringed spaces agreeing on the members of an open covering of the source are equal.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.existsUnique_hom_to_glued_of_compatibleCharts`:
  compatible morphisms from an open covering of a locally ringed space to the pieces of a gluing
  datum determine a unique morphism to the glued space.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ChartDatum`: that descent datum, bundled.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.chartDatumOfHom`: the descent datum induced by a
  morphism into the glued space, carried by the pullbacks of the canonical charts.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_chartDatumOfHom`: a morphism into the glued
  space is recovered from the descent datum it induces, which closes one half of the round trip
  with `existsUnique_hom_to_glued`.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ChartDatum.range_v`: the covering carried by a
  descent datum is the inverse-image covering of the morphism the datum determines.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ChartDatum.chartIso_hom_fst_and_snd`: the other
  half of the round trip — chart by chart, a descent datum is carried isomorphically onto the
  descent datum induced by the morphism it determines, compatibly with the covering maps and the
  local morphisms.

## Implementation notes

The covering is itself turned into a gluing datum whose overlaps are the pullbacks of the
covering maps, and the resulting glued space is identified with the covered space: that
comparison morphism is an open immersion by a stalkwise argument and surjective because the
covering is jointly surjective, hence an isomorphism. The descent datum then produces a morphism
out of the auxiliary gluing, and composing with the inverse of the comparison gives the morphism
being sought.

The auxiliary gluing datum is declared reducible at `implicit` transparency for the rest of the
file. Without that, the structure projections of a `noncomputable def` do not reduce where the
elaborator checks implicit arguments, and the two descent conditions below cannot even be stated
in the pullback form in which they are proved.

## References

* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

section Reconstruction

/-- An open covering of a locally ringed space, read as a gluing datum: the pieces are the
members of the covering, the overlaps are their pairwise pullbacks over the covered space, and
the transition maps are the pullback symmetries.

The covered space is recovered from this datum up to isomorphism by `openCoverFromGlued` and
`openCoverFromGlued_isIso`. -/
noncomputable def openCoverGlueData
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] :
    LocallyRingedSpace.GlueData.{u} where
  J := I
  U := V
  V := fun ij ↦ pullback (v ij.1) (v ij.2)
  f i j := pullback.fst (v i) (v j)
  t i j := (pullbackSymmetry (v i) (v j)).hom
  t_id i := by simp
  t' i j k := pullback.lift
    (pullback.lift
      (pullback.fst _ _ ≫ pullback.snd (v i) (v j))
      (pullback.snd _ _ ≫ pullback.snd (v i) (v k)) (by
        simp only [Category.assoc, ← pullback.condition]
        exact pullback.condition_assoc _))
    (pullback.fst _ _ ≫ (pullbackSymmetry (v i) (v j)).hom)
    (by
      refine (pullback.lift_fst (f := v j) (g := v k) _ _ _).trans ?_
      simp)
  t_fac i j k := pullback.lift_snd _ _ _
  cocycle i j k := by
    apply (cancel_mono (pullback.fst (pullback.fst (v i) (v j))
      (pullback.fst (v i) (v k)) ≫ pullback.fst (v i) (v j) ≫ v i)).mp
    simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullbackSymmetry_hom_comp_snd_assoc]
  f_open i j := inferInstance

attribute [local implicit_reducible] openCoverGlueData

/-- The comparison morphism from the gluing of a family of open immersions to their common
target: on the piece indexed by `i` it is the covering map `v i`. -/
noncomputable def openCoverFromGlued
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] :
    (openCoverGlueData v).glued ⟶ Y :=
  Multicoequalizer.desc _ _ v (by
    rintro ⟨i, j⟩
    change pullback.fst (v i) (v j) ≫ v i =
      ((pullbackSymmetry (v i) (v j)).hom ≫ pullback.fst (v j) (v i)) ≫ v j
    rw [pullbackSymmetry_hom_comp_fst]
    exact pullback.condition)

/-- Specializing along an equality of points induces an isomorphism of stalks. -/
private lemma isIso_stalkSpecializes_of_eq
    {C : Type*} [Category C] [HasColimits C] {X : TopCat}
    (F : X.Presheaf C) {x y : X} (h : x = y) :
    IsIso (F.stalkSpecializes (specializes_of_eq h)) := by
  subst y
  simpa only [TopCat.Presheaf.stalkSpecializes_refl] using
    (inferInstance : IsIso (𝟙 (F.stalk x)))

/-- Equal morphisms of locally ringed spaces agree pointwise on underlying spaces. -/
private lemma base_apply_congr {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    f.base x = g.base x := by
  rw [h]

/-- On the piece indexed by `i`, the comparison morphism `openCoverFromGlued v` is `v i`. -/
private lemma ι_openCoverFromGlued
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] (i : I) :
    (openCoverGlueData v).ι i ≫ openCoverFromGlued v = v i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- Pointwise form of `ι_openCoverFromGlued`. -/
private lemma openCoverFromGlued_base_ι_apply
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] (i : I) (x : V i) :
    (openCoverFromGlued v).base (((openCoverGlueData v).ι i).base x) = (v i).base x :=
  base_apply_congr (ι_openCoverFromGlued v i) x

/-- The comparison morphism out of the gluing of a family of open immersions is injective. -/
private lemma openCoverFromGlued_injective
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] :
    Function.Injective (openCoverFromGlued v).base := by
  let E := openCoverGlueData v
  intro a b hab
  obtain ⟨i, x, rfl⟩ := E.ι_jointly_surjective a
  obtain ⟨j, y, rfl⟩ := E.ι_jointly_surjective b
  have hxy : (v i).base x = (v j).base y :=
    (openCoverFromGlued_base_ι_apply v i x).symm.trans
      (hab.trans (openCoverFromGlued_base_ι_apply v j y))
  obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst (v i) (v j)).base := by
    rw [range_pullback_fst_of_right]
    exact ⟨y, hxy.symm⟩
  have hz' : (pullback.snd (v i) (v j)).base z = y := by
    apply (inferInstance : LocallyRingedSpace.IsOpenImmersion (v j)).base_open.injective
    calc
      (v j).base ((pullback.snd (v i) (v j)).base z) =
          (v i).base ((pullback.fst (v i) (v j)).base z) :=
        (base_apply_congr (pullback.condition (f := v i) (g := v j)) z).symm
      _ = (v i).base x := congrArg (v i).base hz
      _ = _ := hxy
  have hglue : pullback.fst (v i) (v j) ≫ E.ι i =
      pullback.snd (v i) (v j) ≫ E.ι j := by
    simpa [E, openCoverGlueData, Category.assoc] using (E.glue_condition i j).symm
  simpa only [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply, hz, hz'] using!
    base_apply_congr hglue z

/-- The comparison morphism out of the gluing of a family of open immersions is an open
embedding on underlying spaces. -/
private lemma openCoverFromGlued_isOpenEmbedding
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] :
    Topology.IsOpenEmbedding (openCoverFromGlued v).base := by
  let E := openCoverGlueData v
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (openCoverFromGlued v).base.hom.continuous (openCoverFromGlued_injective v)
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨i, x, rfl⟩ := E.ι_jointly_surjective z
  refine ⟨(v i).base '' ((E.ι i).base ⁻¹' U), ?_, ?_, ?_⟩
  · rintro _ ⟨x', hx', rfl⟩
    exact ⟨(E.ι i).base x', hx', openCoverFromGlued_base_ι_apply v i x'⟩
  · exact (inferInstance : LocallyRingedSpace.IsOpenImmersion (v i)).base_open.isOpenMap _
      (hU.preimage (E.ι i).base.hom.continuous)
  · exact ⟨x, hz, (openCoverFromGlued_base_ι_apply v i x).symm⟩

/-- The comparison morphism out of the gluing of a family of open immersions induces
isomorphisms on all stalks. -/
private lemma isIso_stalkMap_openCoverFromGlued
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)] (z : (openCoverGlueData v).glued) :
    IsIso ((openCoverFromGlued v).stalkMap z) := by
  let E := openCoverGlueData v
  let q := openCoverFromGlued v
  obtain ⟨i, x, rfl⟩ := E.ι_jointly_surjective z
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (ι_openCoverFromGlued v i) x
  rw [LocallyRingedSpace.stalkMap_comp] at h
  have hx : (v i).base x = (E.ι i ≫ q).base x :=
    (openCoverFromGlued_base_ι_apply v i x).symm
  have h' : LocallyRingedSpace.Hom.stalkMap q ((E.ι i).base x) ≫
      LocallyRingedSpace.Hom.stalkMap (E.ι i) x =
        Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫
          LocallyRingedSpace.Hom.stalkMap (v i) x := h
  exact IsIso.of_isIso_fac_right (f := LocallyRingedSpace.Hom.stalkMap (E.ι i) x)
    (hh := IsIso.comp_isIso' (isIso_stalkSpecializes_of_eq Y.presheaf hx)
      (LocallyRingedSpace.IsOpenImmersion.stalk_iso (v i) x)) h'

/-- For a jointly surjective family of open immersions, the comparison morphism out of their
gluing is surjective. -/
private lemma openCoverFromGlued_surjective
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)]
    (hv : ∀ y : Y, ∃ i x, (v i).base x = y) :
    Function.Surjective (openCoverFromGlued v).base := fun y ↦
  let ⟨i, x, hx⟩ := hv y
  ⟨_, (openCoverFromGlued_base_ι_apply v i x).trans hx⟩

/-- For a jointly surjective family of open immersions, the comparison morphism out of their
gluing is an isomorphism: a locally ringed space is the gluing of any open covering of itself.
It is an open immersion by a stalkwise argument and surjective because the covering is jointly
surjective. -/
lemma openCoverFromGlued_isIso
    {I : Type u} {Y : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)]
    (hv : ∀ y : Y, ∃ i x, (v i).base x = y) :
    IsIso (openCoverFromGlued v) := by
  have := isIso_stalkMap_openCoverFromGlued v
  have :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (openCoverFromGlued_isOpenEmbedding v)
  have : Epi (openCoverFromGlued v).base :=
    (TopCat.epi_iff_surjective _).mpr (openCoverFromGlued_surjective v hv)
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

/-- Morphisms of locally ringed spaces glue over an open covering of the source: a family of
morphisms out of the members of the covering which agree on the pairwise overlaps comes from a
unique morphism out of the covered space.

This is the locally ringed space counterpart of `AlgebraicGeometry.Scheme.Cover.glueMorphisms`,
and the reason it is available here is that the covered space is the gluing of its own covering
(`openCoverFromGlued_isIso`), so the morphism is obtained from the universal property of the
multicoequalizer. -/
@[stacks 01JB "morphisms of locally ringed spaces glue over an open covering of the source"]
theorem existsUnique_hom_of_openCover
    {I : Type u} {Y Z : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (v i)]
    (hv : ∀ y : Y, ∃ i x, (v i).base x = y)
    (h : ∀ i, V i ⟶ Z)
    (hcompat : ∀ i j, pullback.fst (v i) (v j) ≫ h i = pullback.snd (v i) (v j) ≫ h j) :
    ∃! f : Y ⟶ Z, ∀ i, v i ≫ f = h i := by
  let E := openCoverGlueData v
  let q := openCoverFromGlued v
  have : IsIso q := openCoverFromGlued_isIso v hv
  have hq (i : I) : E.ι i ≫ q = v i := ι_openCoverFromGlued v i
  let k : E.glued ⟶ Z := Multicoequalizer.desc E.diagram _ h (by
    rintro ⟨i, j⟩
    change pullback.fst (v i) (v j) ≫ h i =
      ((pullbackSymmetry (v i) (v j)).hom ≫ pullback.fst (v j) (v i)) ≫ h j
    rw [pullbackSymmetry_hom_comp_fst]
    exact hcompat i j)
  have hk (i : I) : E.ι i ≫ k = h i := Multicoequalizer.π_desc _ _ _ _ _
  refine ⟨inv q ≫ k, fun i ↦ ?_, fun f hf ↦ ?_⟩
  · rw [← hq i, Category.assoc, IsIso.hom_inv_id_assoc, hk]
  · apply (cancel_epi q).mp
    apply Multicoequalizer.hom_ext
    intro i
    change E.ι i ≫ (q ≫ f) = E.ι i ≫ (q ≫ inv q ≫ k)
    rw [← Category.assoc, hq i, hf i, IsIso.hom_inv_id_assoc, hk i]

/-- Two morphisms of locally ringed spaces out of a space covered by open immersions agree as
soon as they agree on each member of the covering. -/
theorem hom_ext_of_openCover
    {I : Type u} {Y Z : LocallyRingedSpace.{u}}
    {V : I → LocallyRingedSpace.{u}} (v : ∀ i, V i ⟶ Y)
    (v_open : ∀ i, LocallyRingedSpace.IsOpenImmersion (v i))
    (hv : ∀ y : Y, ∃ i x, (v i).base x = y)
    (a b : Y ⟶ Z) (hab : ∀ i, v i ≫ a = v i ≫ b) : a = b := by
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion (v i) := v_open
  obtain ⟨_, _, huniq⟩ := existsUnique_hom_of_openCover v hv (fun i ↦ v i ≫ a)
    fun _ _ ↦ pullback.condition_assoc a
  exact (huniq a fun _ ↦ rfl).trans (huniq b fun i ↦ (hab i).symm).symm

/-- Compatible morphisms from an open covering of a locally ringed space to the pieces of a
gluing datum determine a unique morphism to the glued space. The two equations for
`transitionLift` say that on `V i ×_Y V j` the maps are related by the transition `D.t i j`. -/
@[stacks 01JB "reconstruction from compatible charts"]
theorem existsUnique_hom_to_glued_of_compatibleCharts
    (D : LocallyRingedSpace.GlueData.{u}) (Y : LocallyRingedSpace.{u})
    (V : D.J → LocallyRingedSpace.{u}) (v : ∀ i, V i ⟶ Y)
    (v_open : ∀ i, LocallyRingedSpace.IsOpenImmersion (v i))
    (v_jointly_surjective : ∀ y : Y, ∃ (i : D.J) (x : V i), (v i).base x = y)
    (g : ∀ i, V i ⟶ D.U i)
    (transitionLift : ∀ i j, pullback (v i) (v j) ⟶ D.V (i, j))
    (transitionLift_f : ∀ i j,
      transitionLift i j ≫ D.f i j = pullback.fst (v i) (v j) ≫ g i)
    (transitionLift_t_f : ∀ i j,
      transitionLift i j ≫ D.t i j ≫ D.f j i = pullback.snd (v i) (v j) ≫ g j) :
    ∃! f : Y ⟶ D.glued, ∀ i, v i ≫ f = g i ≫ D.ι i := by
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion (v i) := v_open
  have hcompat (i j : D.J) :
      pullback.fst (v i) (v j) ≫ g i ≫ D.ι i =
        pullback.snd (v i) (v j) ≫ g j ≫ D.ι j := by
    calc
      _ = (transitionLift i j ≫ D.f i j) ≫ D.ι i := by
        rw [transitionLift_f, Category.assoc]
      _ = (transitionLift i j ≫ D.t i j ≫ D.f j i) ≫ D.ι j := by
        simp only [Category.assoc]
        rw [D.glue_condition]
      _ = _ := by rw [transitionLift_t_f, Category.assoc]
  exact existsUnique_hom_of_openCover v v_jointly_surjective (fun i ↦ g i ≫ D.ι i) hcompat

end Reconstruction

section RoundTrip

/-- Descent datum for a morphism into a glueing: an open covering `v i : V i ⟶ Y` of a locally
ringed space together with morphisms `g i : V i ⟶ D.U i` to the pieces of the glueing datum,
such that the inverse image of the prescribed overlap `D.V (i, j)` under `g i` is exactly
`V i ∩ V j`, and such that on `V i ∩ V j` the maps `g i` and `g j` are related by the prescribed
transition. The last condition is carried by a lift `transitionLift i j` of `V i ∩ V j` into the
overlap, together with the two equations describing its two components. -/
structure ChartDatum (D : LocallyRingedSpace.GlueData.{u}) (Y : LocallyRingedSpace.{u}) where
  /-- The pieces of the covering of `Y`. -/
  V : D.J → LocallyRingedSpace.{u}
  /-- The covering maps. -/
  v : ∀ i, V i ⟶ Y
  /-- The covering maps are open immersions. -/
  v_open : ∀ i, LocallyRingedSpace.IsOpenImmersion (v i)
  /-- The covering maps are jointly surjective. -/
  v_jointlySurjective : ∀ y : Y, ∃ (i : D.J) (x : V i), (v i).base x = y
  /-- The local morphisms to the pieces of the glueing datum. -/
  g : ∀ i, V i ⟶ D.U i
  /-- `g i ⁻¹' (U i j) = V i ∩ V j`, both sides read as subsets of `V i` and the intersection
  as the part of `V i` lying over `V j`. -/
  preimage_overlap : ∀ i j,
    (g i).base ⁻¹' Set.range (D.f i j).base = (v i).base ⁻¹' Set.range (v j).base
  /-- The lift of `V i ∩ V j` into the prescribed overlap. -/
  transitionLift : ∀ i j, pullback (v i) (v j) ⟶ D.V (i, j)
  /-- The lift is compatible with `g i`. -/
  transitionLift_f : ∀ i j, transitionLift i j ≫ D.f i j = pullback.fst (v i) (v j) ≫ g i
  /-- The lift is compatible with `g j` through the transition map. -/
  transitionLift_t_f : ∀ i j,
    transitionLift i j ≫ D.t i j ≫ D.f j i = pullback.snd (v i) (v j) ≫ g j

/-- The descent datum attached to a morphism into the glued space: the covering is by the
pullbacks of the canonical charts, and the local morphisms are the second projections. -/
@[expose] noncomputable def chartDatumOfHom (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) : D.ChartDatum Y where
  V i := pullback g (D.ι i)
  v i := pullback.fst g (D.ι i)
  v_open _ := inferInstance
  v_jointlySurjective y := D.hom_pullbackCharts_jointlySurjective g y
  g i := pullback.snd g (D.ι i)
  preimage_overlap i j := by
    rw [D.hom_pullbackCharts_preimage_overlap g i j, range_pullback_fst_of_right]
  transitionLift i j := (D.hom_pullbackCharts_transition g i j).choose
  transitionLift_f i j := (D.hom_pullbackCharts_transition g i j).choose_spec.1.1
  transitionLift_t_f i j := (D.hom_pullbackCharts_transition g i j).choose_spec.1.2

/-- The `i`-th chart of `chartDatumOfHom g` is `pullback g (D.ι i)`. -/
@[simp]
lemma chartDatumOfHom_V (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOfHom g).V i = pullback g (D.ι i) := rfl

/-- The `i`-th covering map of `chartDatumOfHom g` is `pullback.fst g (D.ι i)`. -/
@[simp]
lemma chartDatumOfHom_v (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOfHom g).v i = pullback.fst g (D.ι i) := rfl

/-- The `i`-th local morphism of `chartDatumOfHom g` is `pullback.snd g (D.ι i)`. -/
@[simp]
lemma chartDatumOfHom_g (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOfHom g).g i = pullback.snd g (D.ι i) := rfl

/-- Compatible morphisms from an open covering of `Y` to the pieces of a glueing datum determine
a unique morphism `Y ⟶ D.glued`, for the descent datum carried by an arbitrary chart datum. -/
theorem existsUnique_hom_to_glued (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) :
    ∃! f : Y ⟶ D.glued, ∀ i, C.v i ≫ f = C.g i ≫ D.ι i :=
  D.existsUnique_hom_to_glued_of_compatibleCharts Y C.V C.v C.v_open C.v_jointlySurjective C.g
    C.transitionLift C.transitionLift_f C.transitionLift_t_f

/-- The mapping property for morphisms *into* a glueing: a morphism `g : Y ⟶ D.glued` is
recovered from the descent datum it induces, so that passing from a morphism to its chart datum
and back is the identity. Combined with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.existsUnique_hom_to_glued`, which says that every
chart datum determines a unique morphism, this identifies `Mor(Y, D.glued)` with the set of
descent data arising from morphisms. -/
@[stacks 01JB "the mapping property for morphisms into the glueing"]
theorem hom_chartDatumOfHom (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) :
    ∀ f : Y ⟶ D.glued,
      (∀ i, (D.chartDatumOfHom g).v i ≫ f = (D.chartDatumOfHom g).g i ≫ D.ι i) → f = g :=
  fun _ hf ↦ (D.existsUnique_hom_to_glued (D.chartDatumOfHom g)).unique hf fun _ ↦
    pullback.condition

/-- **Stacks Project, Tag 01JB.** The covering carried by a descent datum is necessarily the
inverse-image covering of the morphism the datum determines: `V i = f ⁻¹' U i`. -/
theorem ChartDatum.range_v {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) :
    Set.range (C.v i).base = f.base ⁻¹' Set.range (D.ι i).base := by
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(C.g i).base x, (base_apply_congr (hf i) x).symm⟩
  · obtain ⟨j, x, rfl⟩ := C.v_jointlySurjective y
    have hcomp : f.base ((C.v j).base x) = (D.ι j).base ((C.g j).base x) :=
      base_apply_congr (hf j) x
    have hx : (C.g j).base x ∈ (D.ι j).base ⁻¹' Set.range (D.ι i).base := by
      rwa [Set.mem_preimage, ← hcomp]
    rw [← D.range_overlap j i] at hx
    exact (Set.ext_iff.mp (C.preimage_overlap j i) x).mp hx

/-- The comparison morphism from the `i`-th chart of a descent datum to the `i`-th chart of the
inverse-image covering of the morphism the datum determines. -/
noncomputable def ChartDatum.toPullback {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) : C.V i ⟶ pullback f (D.ι i) :=
  pullback.lift (C.v i) (C.g i) (hf i)

/-- The comparison morphism `C.toPullback hf i` followed by the first projection is the covering
map `C.v i`. -/
@[simp, reassoc]
lemma ChartDatum.toPullback_fst {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) :
    C.toPullback hf i ≫ pullback.fst f (D.ι i) = C.v i :=
  pullback.lift_fst _ _ _

/-- **Stacks Project, Tag 01JB.** The comparison morphism of `ChartDatum.toPullback` is an
isomorphism: a descent datum agrees with the one induced by the morphism it determines. -/
theorem ChartDatum.isIso_toPullback {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) : IsIso (C.toPullback hf i) := by
  have := C.v_open i
  have hsub : Set.range (pullback.fst f (D.ι i)).base ⊆ Set.range (C.v i).base := by
    rw [C.range_v hf i, range_pullback_fst_of_right]
  refine ⟨LocallyRingedSpace.IsOpenImmersion.lift (C.v i) (pullback.fst f (D.ι i)) hsub,
    ?_, ?_⟩
  · rw [← cancel_mono (C.v i), Category.assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, C.toPullback_fst hf i, Category.id_comp]
  · rw [← cancel_mono (pullback.fst f (D.ι i)), Category.assoc, C.toPullback_fst hf i,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]

/-- The `i`-th chart of a descent datum, identified with the `i`-th chart of the inverse-image
covering of the morphism the datum determines. The target is the `i`-th chart of
`chartDatumOfHom`, by `chartDatumOfHom_V`. -/
@[expose] noncomputable def ChartDatum.chartIso {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) :
    C.V i ≅ pullback f (D.ι i) :=
  have := C.isIso_toPullback hf i
  asIso (C.toPullback hf i)

/-- The forward morphism of `C.chartIso hf i` is the comparison morphism `C.toPullback hf i`. -/
@[simp]
lemma ChartDatum.chartIso_hom {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) :
    (C.chartIso hf i).hom = C.toPullback hf i := rfl

/-- The other half of the round trip for morphisms *into* a glueing: a descent datum is carried
isomorphically, chart by chart and compatibly with both the covering maps and the local
morphisms, onto the descent datum induced by the morphism it determines — whose charts, covering
maps and local morphisms are `pullback f (D.ι i)`, `pullback.fst f (D.ι i)` and
`pullback.snd f (D.ι i)` by `chartDatumOfHom_V`, `chartDatumOfHom_v` and `chartDatumOfHom_g`.
Together with `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_chartDatumOfHom` this identifies
`Mor(Y, D.glued)` with the descent data of the statement. -/
@[stacks 01JB "a descent datum is its own inverse-image covering"]
theorem ChartDatum.chartIso_hom_fst_and_snd {D : LocallyRingedSpace.GlueData.{u}}
    {Y : LocallyRingedSpace.{u}} (C : D.ChartDatum Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.v i ≫ f = C.g i ≫ D.ι i) (i : D.J) :
    (C.chartIso hf i).hom ≫ pullback.fst f (D.ι i) = C.v i ∧
      (C.chartIso hf i).hom ≫ pullback.snd f (D.ι i) = C.g i :=
  ⟨C.toPullback_fst hf i, pullback.lift_snd _ _ _⟩

end RoundTrip

end AlgebraicGeometry.LocallyRingedSpace.GlueData

end
