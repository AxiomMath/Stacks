module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Scheme.AutomorphismFunctor

/-!
# The automorphism functor is a Zariski sheaf

Let `X` be a scheme over `S` and `T` an `S`-scheme with an open cover `T = ⋃ U_i`. The base
changes `X_{U_i}` form an open cover of `X_T`, and morphisms out of `X_T` glue along it. Hence
the automorphism functor `T ↦ Aut_T(X_T)` of `AlgebraicGeometry.Scheme.autFunctor` is a sheaf
for the Zariski topology:

* an endomorphism of `X_T` over `T` is determined by its base changes to the members `U_i`;
* endomorphisms of the `X_{U_i}` over `U_i` whose base changes to the overlaps
  `U_i ×_T U_j` agree glue to an endomorphism of `X_T` over `T`;

and the same holds for automorphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.coverOverObj`, `AlgebraicGeometry.Scheme.coverOverPairObj`: the
  members of an open cover of an `S`-scheme and their pairwise fibre products, as `S`-schemes,
  with their structure morphisms `AlgebraicGeometry.Scheme.coverOverι`,
  `AlgebraicGeometry.Scheme.coverOverPairFst` and `AlgebraicGeometry.Scheme.coverOverPairSnd`.
* `AlgebraicGeometry.Scheme.baseChangeOpenCover`: the open cover of `X_T` by the base changes
  of the members.
* `AlgebraicGeometry.Scheme.endGlue`: the glued endomorphism.

## Main results

* `AlgebraicGeometry.Scheme.endo_ext_of_openCover` and
  `AlgebraicGeometry.Scheme.aut_ext_of_openCover`: the separation property.
* `AlgebraicGeometry.Scheme.endBaseChange_endGlue` and
  `AlgebraicGeometry.Scheme.exists_autFunctor_map_eq_of_openCover`: the gluing property.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (X : Over S) {T : Over S} (𝒰 : T.left.OpenCover)

/-! ### The members of a cover as `S`-schemes -/

/-- A member of an open cover of an `S`-scheme, as an `S`-scheme. -/
abbrev coverOverObj (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)

/-- The inclusion of a member of an open cover, as a morphism of `S`-schemes. -/
abbrev coverOverι (i : 𝒰.I₀) : coverOverObj 𝒰 i ⟶ T := Over.homMk (𝒰.f i)

/-- The fibre product of two members of an open cover, as an `S`-scheme. -/
abbrev coverOverPairObj (i j : 𝒰.I₀) : Over S :=
  Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)

/-- The first projection of the fibre product of two members. -/
abbrev coverOverPairFst (i j : 𝒰.I₀) : coverOverPairObj 𝒰 i j ⟶ coverOverObj 𝒰 i :=
  Over.homMk (pullback.fst _ _)

/-- The second projection of the fibre product of two members. -/
abbrev coverOverPairSnd (i j : 𝒰.I₀) : coverOverPairObj 𝒰 i j ⟶ coverOverObj 𝒰 j :=
  Over.homMk (pullback.snd _ _) (by simp [← pullback.condition_assoc])

/-! ### The induced cover of the base change -/

/-- **The base changes of the members of an open cover of `T` cover `X_T`.** -/
abbrev baseChangeOpenCover : (pullback X.hom T.hom).OpenCover where
  I₀ := 𝒰.I₀
  X i := pullback (pullback.snd X.hom T.hom) (𝒰.f i)
  f i := pullback.fst _ _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨y, hy⟩ := 𝒰.covers (pullback.snd X.hom T.hom x)
    obtain ⟨z, hz, -⟩ := Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨𝒰.idx _, z, hz⟩

/-- The `i`-th member of `AlgebraicGeometry.Scheme.baseChangeOpenCover` maps to `X_T` by the first
projection. -/
@[simp]
theorem baseChangeOpenCover_f (i : 𝒰.I₀) :
    (baseChangeOpenCover X 𝒰).f i = pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) :=
  rfl

/-- The comparison of a member of `AlgebraicGeometry.Scheme.baseChangeOpenCover` with the base
change of `X` to the member of the cover. -/
abbrev baseChangeOpenCoverIso (i : 𝒰.I₀) :
    pullback (pullback.snd X.hom T.hom) (𝒰.f i) ≅ pullback X.hom (coverOverObj 𝒰 i).hom :=
  pullbackLeftPullbackSndIso X.hom T.hom (𝒰.f i)

/-- Composing `AlgebraicGeometry.Scheme.baseChangeOpenCoverIso` with the base change map of the
inclusion of the member gives the inclusion of the member of the induced cover. -/
@[reassoc (attr := simp)]
theorem baseChangeOpenCoverIso_hom_baseChangeMap (i : 𝒰.I₀) :
    (baseChangeOpenCoverIso X 𝒰 i).hom ≫ baseChangeMap X (coverOverι 𝒰 i) =
      pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) := by
  apply pullback.hom_ext
  · simp
  · simp [pullback.condition]

/-! ### Separation -/

/-- **An endomorphism of `X_T` over `T` is determined by its base changes to the members of an
open cover of `T`.** -/
theorem endo_ext_of_openCover
    {φ ψ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X}
    (h : ∀ i, endBaseChange X (coverOverι 𝒰 i) φ = endBaseChange X (coverOverι 𝒰 i) ψ) :
    φ = ψ := by
  apply endo_ext
  refine (baseChangeOpenCover X 𝒰).hom_ext _ _ fun i ↦ ?_
  rw [baseChangeOpenCover_f, ← baseChangeOpenCoverIso_hom_baseChangeMap X 𝒰 i, Category.assoc,
    Category.assoc, ← endBaseChange_left_fst, ← endBaseChange_left_fst, h i]

/-- **An automorphism of `X_T` over `T` is determined by its base changes to the members of an
open cover of `T`.** -/
theorem aut_ext_of_openCover {ψ ψ' : (autFunctor X).obj (op T)}
    (h : ∀ i, (autFunctor X).map (coverOverι 𝒰 i).op ψ =
      (autFunctor X).map (coverOverι 𝒰 i).op ψ') : ψ = ψ' :=
  Aut.ext (Iso.ext (endo_ext_of_openCover X 𝒰 fun i ↦ congrArg (·.asIso.hom) (h i)))

/-! ### Gluing -/

variable {X 𝒰} (φ : ∀ i, (Over.pullback (coverOverObj 𝒰 i).hom).obj X ⟶
  (Over.pullback (coverOverObj 𝒰 i).hom).obj X)

/-- The commutative square of the `i`-th member of the induced cover of `X_T` over the cover of
`T`. -/
theorem baseChangeOpenCover_condition (i : 𝒰.I₀) :
    pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) ≫ pullback.snd X.hom T.hom =
      pullback.snd (pullback.snd X.hom T.hom) (𝒰.f i) ≫ 𝒰.f i :=
  pullback.condition

/-- The comparison morphism from the fibre product of two members of the induced cover of `X_T`
to the base change of `X` to the fibre product of the two members of the cover of `T`. -/
def baseChangeOpenCoverPairMap (i j : 𝒰.I₀) :
    pullback (pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i))
        (pullback.fst (pullback.snd X.hom T.hom) (𝒰.f j)) ⟶
      pullback X.hom (coverOverPairObj 𝒰 i j).hom :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, ← baseChangeOpenCover_condition, ← Category.assoc, pullback.condition,
        Category.assoc, baseChangeOpenCover_condition, Category.assoc])) (by
      have h2 : pullback.fst X.hom T.hom ≫ X.hom = pullback.snd X.hom T.hom ≫ T.hom :=
        pullback.condition
      change _ = _ ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom
      rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, h2,
        reassoc_of% (baseChangeOpenCover_condition (X := X) (𝒰 := 𝒰) i), Category.assoc])

/-- The first component of `AlgebraicGeometry.Scheme.baseChangeOpenCoverPairMap`. -/
theorem baseChangeOpenCoverPairMap_fst' (i j : 𝒰.I₀) :
    baseChangeOpenCoverPairMap (X := X) i j ≫ pullback.fst X.hom (coverOverPairObj 𝒰 i j).hom =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.Scheme.baseChangeOpenCoverPairMap`. -/
theorem baseChangeOpenCoverPairMap_snd' (i j : 𝒰.I₀) :
    baseChangeOpenCoverPairMap (X := X) i j ≫ pullback.snd X.hom (coverOverPairObj 𝒰 i j).hom =
      pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
        (by rw [Category.assoc, ← baseChangeOpenCover_condition, ← Category.assoc,
          pullback.condition, Category.assoc, baseChangeOpenCover_condition, Category.assoc]) :=
  pullback.lift_snd _ _ _

/-- `AlgebraicGeometry.Scheme.baseChangeOpenCoverPairMap` is compatible with the first projections
to the member `i`. -/
theorem baseChangeOpenCoverPairMap_fst (i j : 𝒰.I₀) :
    baseChangeOpenCoverPairMap (X := X) i j ≫ baseChangeMap X (coverOverPairFst 𝒰 i j) =
      pullback.fst _ _ ≫ (baseChangeOpenCoverIso X 𝒰 i).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeMap_fst, baseChangeOpenCoverPairMap_fst', Category.assoc]
    exact whisker_eq _ (pullbackLeftPullbackSndIso_hom_fst X.hom T.hom (𝒰.f i)).symm
  · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc, baseChangeOpenCoverPairMap_snd',
      Category.assoc]
    change pullback.lift _ _ _ ≫ pullback.fst (𝒰.f i) (𝒰.f j) = _
    rw [pullback.lift_fst]
    exact whisker_eq _ (pullbackLeftPullbackSndIso_hom_snd X.hom T.hom (𝒰.f i)).symm

/-- `AlgebraicGeometry.Scheme.baseChangeOpenCoverPairMap` is compatible with the second projections
to the member `j`. -/
theorem baseChangeOpenCoverPairMap_snd (i j : 𝒰.I₀) :
    baseChangeOpenCoverPairMap (X := X) i j ≫ baseChangeMap X (coverOverPairSnd 𝒰 i j) =
      pullback.snd _ _ ≫ (baseChangeOpenCoverIso X 𝒰 j).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeMap_fst, baseChangeOpenCoverPairMap_fst', Category.assoc,
      ← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
    exact whisker_eq _ (pullbackLeftPullbackSndIso_hom_fst X.hom T.hom (𝒰.f j)).symm
  · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc, baseChangeOpenCoverPairMap_snd',
      Category.assoc]
    change pullback.lift _ _ _ ≫ pullback.snd (𝒰.f i) (𝒰.f j) = _
    rw [pullback.lift_snd]
    exact whisker_eq _ (pullbackLeftPullbackSndIso_hom_snd X.hom T.hom (𝒰.f j)).symm

variable (hφ : ∀ i j, endBaseChange X (coverOverPairFst 𝒰 i j) (φ i) =
  endBaseChange X (coverOverPairSnd 𝒰 i j) (φ j))
include hφ

/-- The first components `X_{U_i} ⟶ X` of compatible endomorphisms agree on the overlaps of the
induced cover of `X_T`. -/
theorem endGlue_compat (i j : 𝒰.I₀) :
    pullback.fst ((baseChangeOpenCover X 𝒰).f i) ((baseChangeOpenCover X 𝒰).f j) ≫
        (baseChangeOpenCoverIso X 𝒰 i).hom ≫ (φ i).left ≫ pullback.fst _ _ =
      pullback.snd ((baseChangeOpenCover X 𝒰).f i) ((baseChangeOpenCover X 𝒰).f j) ≫
        (baseChangeOpenCoverIso X 𝒰 j).hom ≫ (φ j).left ≫ pullback.fst _ _ := by
  rw [← reassoc_of% (baseChangeOpenCoverPairMap_fst (X := X) i j),
    ← reassoc_of% (baseChangeOpenCoverPairMap_snd (X := X) i j),
    ← endBaseChange_left_fst, ← endBaseChange_left_fst, hφ i j]

/-- The first component `X_T ⟶ X` of the glued endomorphism. -/
def endGlueFst : pullback X.hom T.hom ⟶ X.left :=
  (baseChangeOpenCover X 𝒰).glueMorphisms
    (fun i ↦ (baseChangeOpenCoverIso X 𝒰 i).hom ≫ (φ i).left ≫ pullback.fst _ _)
    (endGlue_compat φ hφ)

/-- The restriction of `AlgebraicGeometry.Scheme.endGlueFst` to the `i`-th member of the induced
cover is the first component of `φ i`. -/
@[reassoc]
theorem baseChangeOpenCover_f_endGlueFst (i : 𝒰.I₀) :
    pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) ≫ endGlueFst φ hφ =
      (baseChangeOpenCoverIso X 𝒰 i).hom ≫ (φ i).left ≫ pullback.fst _ _ :=
  (baseChangeOpenCover X 𝒰).ι_glueMorphisms _ _ i

/-- `AlgebraicGeometry.Scheme.endGlueFst` followed by `X ⟶ S` equals the projection `X_T ⟶ T`
followed by `T ⟶ S`. -/
theorem endGlueFst_comp_hom :
    endGlueFst φ hφ ≫ X.hom = pullback.snd X.hom T.hom ≫ T.hom := by
  refine (baseChangeOpenCover X 𝒰).hom_ext _ _ fun i ↦ ?_
  have h2 : pullback.fst X.hom (coverOverObj 𝒰 i).hom ≫ X.hom =
      pullback.snd X.hom (coverOverObj 𝒰 i).hom ≫ (coverOverObj 𝒰 i).hom := pullback.condition
  have hw : (φ i).left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (φ i)
  change pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) ≫ endGlueFst φ hφ ≫ X.hom =
    pullback.fst (pullback.snd X.hom T.hom) (𝒰.f i) ≫ pullback.snd X.hom T.hom ≫ T.hom
  rw [baseChangeOpenCover_f_endGlueFst_assoc, h2, reassoc_of% hw]
  simp only [Over.mk_hom, pullbackLeftPullbackSndIso_hom_snd_assoc]
  rw [reassoc_of% (baseChangeOpenCover_condition (X := X) (𝒰 := 𝒰) i)]

/-- **The glued endomorphism of `X_T` over `T`.** -/
def endGlue : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X :=
  Over.homMk (pullback.lift (endGlueFst φ hφ) (pullback.snd X.hom T.hom) (endGlueFst_comp_hom φ hφ))
    (pullback.lift_snd _ _ _)

/-- **The glued endomorphism restricts to the given ones.** -/
theorem endBaseChange_endGlue (i : 𝒰.I₀) :
    endBaseChange X (coverOverι 𝒰 i) (endGlue φ hφ) = φ i := by
  apply endo_ext
  rw [endBaseChange_left_fst, ← cancel_epi (baseChangeOpenCoverIso X 𝒰 i).hom,
    baseChangeOpenCoverIso_hom_baseChangeMap_assoc]
  simp only [endGlue, Over.homMk_left, pullback.lift_fst]
  exact baseChangeOpenCover_f_endGlueFst φ hφ i

omit hφ

/-- **Automorphisms glue.** Automorphisms of the base changes `X_{U_i}` of `X` to the members
of an open cover of `T`, whose base changes to the overlaps agree, are the base changes of an
automorphism of `X_T`. -/
theorem exists_autFunctor_map_eq_of_openCover
    (ψ : ∀ i, Aut ((Over.pullback (coverOverObj 𝒰 i).hom).obj X))
    (hψ : ∀ i j, (autFunctor X).map (coverOverPairFst 𝒰 i j).op (ψ i) =
      (autFunctor X).map (coverOverPairSnd 𝒰 i j).op (ψ j)) :
    ∃ ψ₀ : (autFunctor X).obj (op T), ∀ i, (autFunctor X).map (coverOverι 𝒰 i).op ψ₀ = ψ i := by
  have h₁ : ∀ i j, endBaseChange X (coverOverPairFst 𝒰 i j) (ψ i).asIso.hom =
      endBaseChange X (coverOverPairSnd 𝒰 i j) (ψ j).asIso.hom := fun i j ↦
    congrArg (·.asIso.hom) (hψ i j)
  have h₂ : ∀ i j, endBaseChange X (coverOverPairFst 𝒰 i j) (ψ i).asIso.inv =
      endBaseChange X (coverOverPairSnd 𝒰 i j) (ψ j).asIso.inv := fun i j ↦
    congrArg (·.asIso.inv) (hψ i j)
  refine ⟨.of ⟨endGlue (fun i ↦ (ψ i).asIso.hom) h₁, endGlue (fun i ↦ (ψ i).asIso.inv) h₂, ?_, ?_⟩,
    fun i ↦ Aut.ext (Iso.ext (endBaseChange_endGlue _ h₁ i))⟩ <;>
  refine endo_ext_of_openCover X 𝒰 fun i ↦ ?_ <;>
  rw [endBaseChange_comp, endBaseChange_endGlue, endBaseChange_endGlue, endBaseChange_id] <;>
  first | exact (ψ _).asIso.hom_inv_id | exact (ψ _).asIso.inv_hom_id

end AlgebraicGeometry.Scheme
