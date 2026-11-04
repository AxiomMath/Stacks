module

public import Mathlib.Algebra.Category.Grp.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmallGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardGluing

/-!
# The rigidified Picard functor of a morphism with a section, as a Zariski sheaf of groups

Let `f : X ⟶ S` be a morphism of schemes with a section `σ`. For an `S`-scheme `T` write
`X_T = X ×_S T` and `σ_T : T ⟶ X_T` for the induced section. The *rigidified Picard functor*
`Pic_{X/S,σ}` sends `T` to the group of Picard classes of `X_T` killed by `σ_T^*`, which is the
functor the source works with in the proof of [Stacks, Tag 0B9Z] (see the text before
[Stacks, Tag 0B9V]). It is formed here on *all* `S`-schemes, valued in groups of the universe of
the schemes, which is the input shape of the group-scheme criterion
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor` ([Stacks, Tag 0B9Q]).

The values lie in `Type u` because the Picard group is taken in its small model
`Stacks.Picard.smallOfScheme` ([Stacks, Tag 040B]). Since that criterion asks for groups in
multiplicative notation, the value at `T` is `Multiplicative` of the additive subgroup.

When `𝒪_T ⟶ (X_T ⟶ T)_* 𝒪_{X_T}` is an isomorphism for every `T` — for a smooth projective curve
over a field with a rational point this is [Stacks, Tag 0B9U] — the functor is a sheaf for the
Zariski topology (`Stacks.RigidifiedPicard.isSheaf_functor`), by gluing rigidified classes along
fpqc coverings (`Stacks.RigidifiedPicard.exists_glue`).

## Main definitions

* `Stacks.RigidifiedPicard.group` — `Pic_{X/S,σ}(T)` as an additive subgroup of `Pic(X_T)`.
* `Stacks.RigidifiedPicard.functor` — the functor `(Over S)ᵒᵖ ⥤ GrpCat`.

## Main results

* `Stacks.RigidifiedPicard.isSheaf_functor` — the Zariski sheaf property.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The identification of the small Picard group of a scheme with its Picard group. -/
abbrev smallEquiv (Y : Scheme.{u}) : Stacks.Picard.smallOfScheme Y ≃+ Stacks.Picard.ofScheme Y :=
  Stacks.Picard.smallPicardGroupAddEquiv Y.presheaf (Stacks.RingedSpace.structureIsSheaf _)

/-- The identification `smallEquiv` commutes with pullback of Picard classes along `g`. -/
@[simp]
theorem smallEquiv_smallSchemePullbackClassHom {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : Stacks.Picard.smallOfScheme Z) :
    smallEquiv Y (Stacks.Picard.smallSchemePullbackClassHom g x) =
      Stacks.Picard.schemePullbackClass g (smallEquiv Z x) :=
  Stacks.Picard.smallPicardGroupAddEquiv_smallPullbackClassHom _ _

/-- **`Pic_{X/S,σ}(T)`**: the classes of the small Picard group of `X_T` killed by pullback
along the induced section `σ_T`. -/
def group (T : Over S) : AddSubgroup (Stacks.Picard.smallOfScheme (bc f T)) :=
  (Stacks.Picard.smallSchemePullbackClassHom (bcSection f σ hσ T)).ker

/-- A class lies in `Pic_{X/S,σ}(T)` if and only if its pullback along `σ_T` is trivial in the
Picard group. -/
theorem mem_group_iff (T : Over S) (x : Stacks.Picard.smallOfScheme (bc f T)) :
    x ∈ group f σ hσ T ↔
      Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) (smallEquiv _ x) = 0 := by
  rw [group, AddMonoidHom.mem_ker, ← smallEquiv_smallSchemePullbackClassHom,
    AddEquiv.map_eq_zero_iff]

/-- Pullback along `X_T ⟶ X_U` sends `Pic_{X/S,σ}(U)` into `Pic_{X/S,σ}(T)`. -/
theorem smallSchemePullbackClassHom_bcMap_mem {T U : Over S} (g : T ⟶ U)
    (x : Stacks.Picard.smallOfScheme (bc f U)) (hx : x ∈ group f σ hσ U) :
    Stacks.Picard.smallSchemePullbackClassHom (bcMap f g) x ∈ group f σ hσ T := by
  rw [group, AddMonoidHom.mem_ker, Stacks.Picard.smallSchemePullbackClassHom_comp,
    bcSection_comp_bcMap, ← Stacks.Picard.smallSchemePullbackClassHom_comp]
  rw [group, AddMonoidHom.mem_ker] at hx
  rw [hx, map_zero]

/-- Pullback along `X_T ⟶ X_U` as a homomorphism `Pic_{X/S,σ}(U) ⟶ Pic_{X/S,σ}(T)`. -/
def groupMap {T U : Over S} (g : T ⟶ U) : group f σ hσ U →+ group f σ hσ T :=
  ((Stacks.Picard.smallSchemePullbackClassHom (bcMap f g)).comp
    (group f σ hσ U).subtype).codRestrict _ fun x =>
      smallSchemePullbackClassHom_bcMap_mem f σ hσ g x.1 x.2

/-- The underlying class of `groupMap f σ hσ g x` is the pullback of `x` along `X_T ⟶ X_U`. -/
@[simp]
theorem coe_groupMap {T U : Over S} (g : T ⟶ U) (x : group f σ hσ U) :
    (groupMap f σ hσ g x : Stacks.Picard.smallOfScheme (bc f T)) =
      Stacks.Picard.smallSchemePullbackClassHom (bcMap f g) x :=
  rfl

/-- Pullback along the identity of `T` is the identity of `Pic_{X/S,σ}(T)`. -/
theorem groupMap_id (T : Over S) (x : group f σ hσ T) : groupMap f σ hσ (𝟙 T) x = x := by
  ext
  rw [coe_groupMap, bcMap_id, Stacks.Picard.smallSchemePullbackClassHom_id]

/-- Pullback along a composite `g ≫ h` is pullback along `h` followed by pullback along `g`. -/
theorem groupMap_comp {T U V : Over S} (g : T ⟶ U) (h : U ⟶ V) (x : group f σ hσ V) :
    groupMap f σ hσ (g ≫ h) x = groupMap f σ hσ g (groupMap f σ hσ h x) := by
  ext
  rw [coe_groupMap, coe_groupMap, coe_groupMap, bcMap_comp,
    Stacks.Picard.smallSchemePullbackClassHom_comp]

/-- **The rigidified Picard functor `Pic_{X/S,σ}`**, on all `S`-schemes, valued in groups. -/
def functor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Multiplicative (group f σ hσ T.unop))
  map g := GrpCat.ofHom (AddMonoidHom.toMultiplicative (groupMap f σ hσ g.unop))
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact congrArg Multiplicative.ofAdd (groupMap_id f σ hσ T.unop (Multiplicative.toAdd x))
  map_comp g h := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact congrArg Multiplicative.ofAdd
      (groupMap_comp f σ hσ h.unop g.unop (Multiplicative.toAdd x))

/-- The map of `functor f σ hσ` along `g` is `groupMap f σ hσ g` in multiplicative notation. -/
theorem functor_map_apply {T U : Over S} (g : T ⟶ U) (x : (functor f σ hσ).obj (op U)) :
    (functor f σ hσ).map g.op x =
      Multiplicative.ofAdd (groupMap f σ hσ g (Multiplicative.toAdd x)) :=
  rfl

/-! ### The Zariski sheaf property -/

/-- The base change of a Zariski covering family of `S`-schemes is an fpqc covering of `X_T`. -/
theorem bc_mem_fpqc_of_zariski {T : Over S} {ι : Type*} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hg : Presieve.ofArrows (fun i => (U i).left) (fun i => (g i).left) ∈
      Scheme.precoverage @IsOpenImmersion T.left) :
    Presieve.ofArrows (fun i => bc f (U i)) (fun i => bcMap f (g i)) ∈
      Scheme.fpqcPrecoverage.{u} (bc f T) :=
  Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ (bc_mem_of_mem f _ g hg)

/-- **Gluing in `Pic_{X/S,σ}`.** Rigidified classes on the members of a Zariski covering family
of an `S`-scheme `T` that agree after every further pullback are the restrictions of exactly one
rigidified class on `T`, as soon as the structure sheaf of every `S`-scheme is the direct image
of the structure sheaf of its base change. -/
theorem existsUnique_group_glue (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hR : Presieve.ofArrows (fun i => (U i).left) (fun i => (g i).left) ∈
      Scheme.precoverage @IsOpenImmersion T.left)
    (x : ∀ i, group f σ hσ (U i))
    (hx : ∀ (V : Over S) (i j : ι) (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      groupMap f σ hσ a (x i) = groupMap f σ hσ b (x j)) :
    ∃! t : group f σ hσ T, ∀ i, groupMap f σ hσ (g i) t = x i := by
  have hfpqc := bc_mem_fpqc_of_zariski f g hR
  let y : ∀ i, Stacks.Picard.ofScheme (bc f (U i)) := fun i =>
    smallEquiv _ ((x i : group f σ hσ (U i)) : Stacks.Picard.smallOfScheme (bc f (U i)))
  have hy0 : ∀ i, Stacks.Picard.schemePullbackClass (bcSection f σ hσ (U i)) (y i) = 0 :=
    fun i => (mem_group_iff f σ hσ (U i) _).1 (x i).2
  have hagree : ∀ (V : Over S) (i j : ι) (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      Stacks.Picard.schemePullbackClass (bcMap f a) (y i) =
        Stacks.Picard.schemePullbackClass (bcMap f b) (y j) := by
    intro V i j a b hab
    have h := congrArg (smallEquiv _ ∘ Subtype.val) (hx V i j a b hab)
    simp only [y, ← smallEquiv_smallSchemePullbackClassHom]
    exact h
  obtain ⟨c, hc⟩ := exists_glue f σ hσ hOiso g hfpqc y hy0 hagree
  let c₀ : Stacks.Picard.ofScheme (bc f T) := c - Stacks.Picard.schemePullbackClass (bcProj f T)
    (Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c)
  have hc₀ : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c₀ = 0 := by
    show Stacks.Picard.schemePullbackClassHom _ c₀ = 0
    rw [map_sub, sub_eq_zero]
    exact (schemePullbackClass_bcSection_bcProj f σ hσ T _).symm
  have hc₀i : ∀ i, Stacks.Picard.schemePullbackClass (bcMap f (g i)) c₀ = y i := by
    intro i
    show Stacks.Picard.schemePullbackClassHom _ c₀ = y i
    rw [map_sub]
    show Stacks.Picard.schemePullbackClass _ c -
      Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ _) = y i
    rw [hc i, schemePullbackClass_bcProj_natural, ← schemePullbackClass_bcSection_natural,
      hc i, hy0 i,
      show Stacks.Picard.schemePullbackClass (bcProj f (U i)) 0 = 0 from
        map_zero (Stacks.Picard.schemePullbackClassHom _), sub_zero]
  let t₀ : group f σ hσ T := ⟨(smallEquiv (bc f T)).symm c₀, by
    rwa [mem_group_iff, AddEquiv.apply_symm_apply]⟩
  refine ⟨t₀, fun i => ?_, fun t ht => ?_⟩
  · apply Subtype.ext
    apply (smallEquiv (bc f (U i))).injective
    show smallEquiv _ (Stacks.Picard.smallSchemePullbackClassHom (bcMap f (g i))
      ((smallEquiv (bc f T)).symm c₀)) = y i
    rw [smallEquiv_smallSchemePullbackClassHom, AddEquiv.apply_symm_apply, hc₀i]
  · apply Subtype.ext
    apply (smallEquiv (bc f T)).injective
    show smallEquiv _ _ = smallEquiv _ ((smallEquiv (bc f T)).symm c₀)
    rw [AddEquiv.apply_symm_apply]
    refine eq_of_section_eq f σ hσ hOiso g hfpqc _ _ ?_ fun i => ?_
    · rw [hc₀]
      exact (mem_group_iff f σ hσ T _).1 t.2
    · rw [hc₀i, ← smallEquiv_smallSchemePullbackClassHom]
      exact congrArg (smallEquiv _ ∘ Subtype.val) (ht i)

/-- The subfunctor of `Pic_{X/S,σ}` given by a family of subgroups `H T` of the rigidified Picard
groups which is stable under pullback. -/
def subfunctor (H : ∀ T : Over S, AddSubgroup (group f σ hσ T))
    (hH : ∀ {T U : Over S} (g : T ⟶ U) (x : group f σ hσ U), x ∈ H U →
      groupMap f σ hσ g x ∈ H T) : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Multiplicative (H T.unop))
  map g := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    (((groupMap f σ hσ g.unop).comp (H _).subtype).codRestrict _ fun x => hH g.unop x.1 x.2))
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact congrArg Multiplicative.ofAdd (Subtype.ext
      (groupMap_id f σ hσ T.unop (Multiplicative.toAdd x).1))
  map_comp g h := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact congrArg Multiplicative.ofAdd (Subtype.ext
      (groupMap_comp f σ hσ h.unop g.unop (Multiplicative.toAdd x).1))

/-- The map of `subfunctor f σ hσ H hH` along `g` is the restriction of `groupMap f σ hσ g`. -/
theorem subfunctor_map_apply (H : ∀ T : Over S, AddSubgroup (group f σ hσ T))
    (hH : ∀ {T U : Over S} (g : T ⟶ U) (x : group f σ hσ U), x ∈ H U →
      groupMap f σ hσ g x ∈ H T) {T U : Over S} (g : T ⟶ U)
    (x : (subfunctor f σ hσ H hH).obj (op U)) :
    ((Multiplicative.toAdd ((subfunctor f σ hσ H hH).map g.op x) : H T) : group f σ hσ T) =
      groupMap f σ hσ g (Multiplicative.toAdd x : H U) :=
  rfl

/-- A presheaf on `Over S` is a Zariski sheaf if compatible families on Zariski covering families
glue uniquely. -/
private theorem isSheaf_zariski_of_existsUnique_glue (F : (Over S)ᵒᵖ ⥤ Type u)
    (h : ∀ {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T),
      Presieve.ofArrows (fun i => (U i).left) (fun i => (g i).left) ∈
        Scheme.precoverage @IsOpenImmersion T.left → ∀ x : ∀ i, F.obj (op (U i)),
      (∀ (i j : ι) (V : Over S) (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
        F.map a.op (x i) = F.map b.op (x j)) → ∃! t : F.obj (op T), ∀ i, F.map (g i).op t = x i) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F := by
  rw [isSheaf_iff_isSheaf_of_type, over_toGrothendieck_eq_toGrothendieck_comap_forget,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨ι, U, g, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  rw [Presieve.isSheafFor_arrows_iff]
  exact h g hR

/-- **A local family of subgroups of `Pic_{X/S,σ}` is a Zariski sheaf**, as soon as the
structure sheaf of every `S`-scheme is the direct image of the structure sheaf of its base
change. -/
theorem isSheaf_subfunctor (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    (H : ∀ T : Over S, AddSubgroup (group f σ hσ T))
    (hH : ∀ {T U : Over S} (g : T ⟶ U) (x : group f σ hσ U), x ∈ H U →
      groupMap f σ hσ g x ∈ H T)
    (hloc : ∀ {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T),
      Presieve.ofArrows (fun i => (U i).left) (fun i => (g i).left) ∈
        Scheme.precoverage @IsOpenImmersion T.left →
      ∀ x : group f σ hσ T, (∀ i, groupMap f σ hσ (g i) x ∈ H (U i)) → x ∈ H T) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (subfunctor f σ hσ H hH ⋙ forget GrpCat) := by
  refine isSheaf_zariski_of_existsUnique_glue _ fun {T ι U} g hR x hx => ?_
  obtain ⟨t, ht, huniq⟩ := existsUnique_group_glue f σ hσ hOiso g hR
    (fun i => (Multiplicative.toAdd (x i) : H (U i)))
    (fun V i j a b hab => congrArg (Subtype.val ∘ Multiplicative.toAdd) (hx i j V a b hab))
  have htH : t ∈ H T := hloc g hR t fun i => by rw [ht i]; exact (Multiplicative.toAdd (x i)).2
  refine ⟨Multiplicative.ofAdd ⟨t, htH⟩, fun i => ?_, fun t' ht' => ?_⟩
  · exact congrArg Multiplicative.ofAdd (Subtype.ext (ht i))
  · exact congrArg Multiplicative.ofAdd (Subtype.ext (huniq _ fun i => congrArg
      (Subtype.val ∘ Multiplicative.toAdd) (ht' i)))

/-- **The rigidified Picard functor is a Zariski sheaf**, as soon as the structure sheaf of
every `S`-scheme `T` is the direct image of the structure sheaf of `X_T`. -/
theorem isSheaf_functor (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (functor f σ hσ ⋙ forget GrpCat) := by
  refine isSheaf_zariski_of_existsUnique_glue _ fun {T ι U} g hR x hx => ?_
  obtain ⟨t, ht, huniq⟩ := existsUnique_group_glue f σ hσ hOiso g hR
    (fun i => Multiplicative.toAdd (x i))
    (fun V i j a b hab => congrArg Multiplicative.toAdd (hx i j V a b hab))
  exact ⟨Multiplicative.ofAdd t, fun i => congrArg Multiplicative.ofAdd (ht i),
    fun t' ht' => congrArg Multiplicative.ofAdd
      (huniq _ fun i => congrArg Multiplicative.toAdd (ht' i))⟩

end Stacks.RigidifiedPicard

end
