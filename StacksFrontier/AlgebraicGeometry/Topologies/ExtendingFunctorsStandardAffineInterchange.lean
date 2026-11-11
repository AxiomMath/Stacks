module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineStage

/-!
# The filtered-colimit interchange for the restricted sheaf condition

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a), (b) and (c). This file carries out
the last step of the deduction of the restricted sheaf condition
`AlgebraicGeometry.ExtendingFunctors.IsStandardAffineSheaf` for the extension of `F` from
condition (c), and so removes the hypothesis `hstd` of
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension`. Stacks 0GDW follows, and with it
Stacks 0EUX in the form the source states it: the extension of a `τ`-sheaf on `𝒞` satisfying
property (b) of Stacks 0EUW is a sheaf for every `τ`-covering of `Sch/S`, with no further
hypothesis.

## The interchange

`AlgebraicGeometry.ExtendingFunctors.exists_baseChangePresentation_of_isStandardCovering` writes
an affine object `V` of `Sch/S` lying over an affine open of `S` as the limit of a directed
inverse system `E` with a least stage, every stage affine and of finite presentation over one
affine open of `S`, and exhibits a standard `τ`-covering `{W i ⟶ V}` of `V` as the base change
along `V ⟶ E_⊥` of a standard `τ`-covering `{T i ⟶ E_⊥}`. The extension turns each of the three
systems

* `E`, with limit `V`,
* `baseChange E (s i)`, with limit `W i`,
* `baseChange E (pullback.fst (s i) (s j) ≫ s i)`, with limit `W i ×_V W j`,

into a filtered colimit, so finitely many sections over the `W i` and finitely many pairwise
compatibilities between them are all defined at one stage `m`. At that stage the sheaf condition
holds by `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isStandardCovering`,
because `E_m` is an object of the subcategory which is affine and of finite presentation over an
affine open of `S` and the base-changed covering of `E_m` is standard
(`AlgebraicGeometry.IsStandardCovering.pullback_fst`); pushing the section it produces forward to
`V` amalgamates the given family, and the same argument at the level of two sections gives
uniqueness.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.baseChangeInterFst`,
  `AlgebraicGeometry.ExtendingFunctors.baseChangeInterSnd`: the two projections exhibiting
  `X ×_Z (Y₁ ×_Z Y₂)` as the fibre product of `X ×_Z Y₁` and `X ×_Z Y₂` over `X`, which is the
  third system above read at a stage.
* `AlgebraicGeometry.ExtendingFunctors.exists_lift_baseChangeInter`: the factorization through it
  of a pair of morphisms agreeing over `X`, which is what turns the finitely many pairwise
  compatibilities into the compatibility of a family of sections.
* `AlgebraicGeometry.ExtendingFunctors.baseChangeTrans`,
  `AlgebraicGeometry.ExtendingFunctors.baseChangeConeπ`: the transition maps of a base-changed
  system and the projections of its limit, with source and target written as the fibre products
  they are, together with their composites with the two projections of those fibre products.
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_pullback_fst_of_presentation`: the interchange
  itself, for a standard `τ`-covering exhibited as the base change of a standard `τ`-covering of
  the least stage of a presentation.
* `AlgebraicGeometry.ExtendingFunctors.isStandardAffineSheaf_extension`: the restricted sheaf
  condition for the extension, which is the hypothesis `hstd` of
  `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension`.
* `ExtendingFunctors.isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory`, in the
  namespace `AlgebraicGeometry`, is Stacks 0GDW: the extension of a functor satisfying conditions
  (a), (b) and (c) is a sheaf for every `τ`-covering of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'`
  is **Stacks 0EUX**, for all five topologies and with no hypothesis beyond those of the source:
  the extension of a `τ`-sheaf on `𝒞` satisfying property (b) of Stacks 0EUW is a sheaf for every
  `τ`-covering of `Sch/S`. It is the unconditional form of
  `AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory`,
  whose hypothesis `hstd` is redundant but which cannot cite the discharge, that statement living
  below this file in the import order.

## Implementation notes

The three systems are not related by a natural transformation constructed as such: only the
components of the comparison maps and their naturality squares are needed, and those are proved
by `CategoryTheory.Limits.pullback.hom_ext` from the description of the maps of a base-changed
system on the two factors.

`AlgebraicGeometry.ExtendingFunctors.baseChange` is a composite of functors, so the source and
target of its action on a morphism are the fibre products `E_m ×_{E_⊥} T` only definitionally;
a term combining such a map with a projection of the fibre product is therefore not type-correct
until those definitions are unfolded, which puts it out of reach of rewriting. The wrappers
`AlgebraicGeometry.ExtendingFunctors.baseChangeTrans` and
`AlgebraicGeometry.ExtendingFunctors.baseChangeConeπ` restate the maps with the fibre products
written out, and everything below is phrased with them.

Common stages for finitely many indices are produced by `Finite.exists_le`, the index type of a
standard covering being finite; the index type of the pairwise compatibilities is its square.

## References

* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
* [Stacks Project, Tag 0EUX](https://stacks.math.columbia.edu/tag/0EUX)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.ExtendingFunctors

/-! ### The base change of a fibre product -/

section Inter

variable {C : Type*} [Category C] [HasPullbacks C] {X Z Y₁ Y₂ : C}
  (a : X ⟶ Z) (p : Y₁ ⟶ Z) (q : Y₂ ⟶ Z)

/-- The projection of `X ×_Z (Y₁ ×_Z Y₂)` to `X ×_Z Y₁`. -/
noncomputable def baseChangeInterFst :
    Limits.pullback a (Limits.pullback.fst p q ≫ p) ⟶ Limits.pullback a p :=
  Limits.pullback.lift (Limits.pullback.fst a (Limits.pullback.fst p q ≫ p))
    (Limits.pullback.snd a (Limits.pullback.fst p q ≫ p) ≫ Limits.pullback.fst p q)
    (Limits.pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The projection of `X ×_Z (Y₁ ×_Z Y₂)` to `X ×_Z Y₂`. -/
noncomputable def baseChangeInterSnd :
    Limits.pullback a (Limits.pullback.fst p q ≫ p) ⟶ Limits.pullback a q :=
  Limits.pullback.lift (Limits.pullback.fst a (Limits.pullback.fst p q ≫ p))
    (Limits.pullback.snd a (Limits.pullback.fst p q ≫ p) ≫ Limits.pullback.snd p q)
    (by
      rw [Category.assoc, ← Limits.pullback.condition]
      exact Limits.pullback.condition)

/-- The composite of `baseChangeInterFst` with the first projection of `X ×_Z Y₁` is the first
projection of `X ×_Z (Y₁ ×_Z Y₂)`. -/
@[simp]
lemma baseChangeInterFst_fst :
    baseChangeInterFst a p q ≫ Limits.pullback.fst a p
      = Limits.pullback.fst a (Limits.pullback.fst p q ≫ p) :=
  Limits.pullback.lift_fst _ _ _

/-- The composite of `baseChangeInterFst` with the second projection of `X ×_Z Y₁` is the second
projection of `X ×_Z (Y₁ ×_Z Y₂)` followed by the projection `Y₁ ×_Z Y₂ ⟶ Y₁`. -/
@[simp]
lemma baseChangeInterFst_snd :
    baseChangeInterFst a p q ≫ Limits.pullback.snd a p
      = Limits.pullback.snd a (Limits.pullback.fst p q ≫ p) ≫ Limits.pullback.fst p q :=
  Limits.pullback.lift_snd _ _ _

/-- The composite of `baseChangeInterSnd` with the first projection of `X ×_Z Y₂` is the first
projection of `X ×_Z (Y₁ ×_Z Y₂)`. -/
@[simp]
lemma baseChangeInterSnd_fst :
    baseChangeInterSnd a p q ≫ Limits.pullback.fst a q
      = Limits.pullback.fst a (Limits.pullback.fst p q ≫ p) :=
  Limits.pullback.lift_fst _ _ _

/-- The composite of `baseChangeInterSnd` with the second projection of `X ×_Z Y₂` is the second
projection of `X ×_Z (Y₁ ×_Z Y₂)` followed by the projection `Y₁ ×_Z Y₂ ⟶ Y₂`. -/
@[simp]
lemma baseChangeInterSnd_snd :
    baseChangeInterSnd a p q ≫ Limits.pullback.snd a q
      = Limits.pullback.snd a (Limits.pullback.fst p q ≫ p) ≫ Limits.pullback.snd p q :=
  Limits.pullback.lift_snd _ _ _

/-- The two projections of `X ×_Z (Y₁ ×_Z Y₂)` agree over `X`. -/
lemma baseChangeInter_condition :
    baseChangeInterFst a p q ≫ Limits.pullback.fst a p
      = baseChangeInterSnd a p q ≫ Limits.pullback.fst a q := by
  rw [baseChangeInterFst_fst, baseChangeInterSnd_fst]

/-- **`X ×_Z (Y₁ ×_Z Y₂)` is the fibre product of `X ×_Z Y₁` and `X ×_Z Y₂` over `X`**, in the
form in which it is used: a pair of morphisms to the two base changes agreeing over `X` factors
through it. -/
lemma exists_lift_baseChangeInter {A : C} (α : A ⟶ Limits.pullback a p)
    (β : A ⟶ Limits.pullback a q)
    (h : α ≫ Limits.pullback.fst a p = β ≫ Limits.pullback.fst a q) :
    ∃ γ : A ⟶ Limits.pullback a (Limits.pullback.fst p q ≫ p),
      γ ≫ baseChangeInterFst a p q = α ∧ γ ≫ baseChangeInterSnd a p q = β := by
  have hc : (α ≫ Limits.pullback.snd a p) ≫ p = (β ≫ Limits.pullback.snd a q) ≫ q := by
    rw [Category.assoc, Category.assoc, ← Limits.pullback.condition,
      ← Limits.pullback.condition, ← Category.assoc, ← Category.assoc, h]
  refine ⟨Limits.pullback.lift (α ≫ Limits.pullback.fst a p)
    (Limits.pullback.lift (α ≫ Limits.pullback.snd a p) (β ≫ Limits.pullback.snd a q) hc)
    ?_, ?_, ?_⟩
  · rw [Limits.pullback.lift_fst_assoc, Category.assoc, Category.assoc,
      ← Limits.pullback.condition]
  · refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeInterFst_fst, Limits.pullback.lift_fst]
    · rw [Category.assoc, baseChangeInterFst_snd, ← Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.lift_fst]
  · refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeInterSnd_fst, Limits.pullback.lift_fst, h]
    · rw [Category.assoc, baseChangeInterSnd_snd, ← Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd]

end Inter

/-- Maps between base changes that are compatible with the two projections are compatible with
`baseChangeInterFst` and `baseChangeInterSnd`. -/
private lemma baseChangeInter_comp_comm {C : Type*} [Category C] [HasPullbacks C]
    {X X' Z : C} {a : X ⟶ Z} {a' : X' ⟶ Z} {u : X ⟶ X'}
    (g : ∀ {Y : C} (r : Y ⟶ Z), Limits.pullback a r ⟶ Limits.pullback a' r)
    (hf : ∀ {Y : C} (r : Y ⟶ Z), g r ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ u)
    (hs : ∀ {Y : C} (r : Y ⟶ Z), g r ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)
    {Y₁ Y₂ : C} (p : Y₁ ⟶ Z) (q : Y₂ ⟶ Z) :
    g (Limits.pullback.fst p q ≫ p) ≫ baseChangeInterFst a' p q
        = baseChangeInterFst a p q ≫ g p ∧
      g (Limits.pullback.fst p q ≫ p) ≫ baseChangeInterSnd a' p q
        = baseChangeInterSnd a p q ≫ g q := by
  constructor <;> refine Limits.pullback.hom_ext ?_ ?_ <;>
    simp [hf, reassoc_of% (hs (Limits.pullback.fst p q ≫ p)), hs,
      reassoc_of% (baseChangeInterFst_fst a p q), reassoc_of% (baseChangeInterSnd_fst a p q)]

/-! ### The first projection of a base change is natural -/

/-- **The first projection of a base change is natural.** For `f : X ⟶ Y` the morphisms
`Z ×_Y X ⟶ Z`, taken over all objects `Z` of `Over Y`, are the components of the counit of the
adjunction `CategoryTheory.Over.mapPullbackAdj`, read through the forgetful functor. -/
lemma pullback_fst_naturality {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {g h : Over Y} (k : g ⟶ h) :
    ((Over.pullback f).map k).left ≫ Limits.pullback.fst h.hom f
      = Limits.pullback.fst g.hom f ≫ k.left := by
  simpa only [Functor.comp_map, Over.forget_map, Over.comp_left, Over.map_map_left,
    Over.mapPullbackAdj_counit_app, Over.homMk_left, Functor.id_map] using
    congrArg (fun j => (Over.forget Y).map j) ((Over.mapPullbackAdj f).counit.naturality k)

/-! ### The transition maps of a base-changed system -/

/-- A functor on `Λᵒᵖ` sends the composite of the maps for `k ≤ l` and `l ≤ m` to the map for
`k ≤ m`. -/
private lemma map_homOfLE_op_comp {C : Type*} [Category C] {Λ : Type*} [PartialOrder Λ]
    (D : Λᵒᵖ ⥤ C) {k l m : Λ} (h₁ : k ≤ l) (h₂ : l ≤ m) (h₃ : k ≤ m) :
    D.map (homOfLE h₂).op ≫ D.map (homOfLE h₁).op = D.map (homOfLE h₃).op :=
  (D.map_comp _ _).symm.trans (congrArg D.map (Subsingleton.elim _ _))

section BaseChangeMaps

variable {S : Scheme.{u}} {Λ : Type u} [PartialOrder Λ] [OrderBot Λ]
  (E : Λᵒᵖ ⥤ Over S) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))

/-- The transition map of a base-changed system, with its source and target written as the fibre
products they are.

`AlgebraicGeometry.ExtendingFunctors.baseChange` is a composite of functors, so the source and
target of its action on a morphism are only definitionally the fibre products
`E_m ×_{E_⊥} T`; writing them out makes the composites with the projections of those fibre
products type-correct for rewriting. -/
noncomputable def baseChangeTrans {m n : Λᵒᵖ} (φ : m ⟶ n) :
    Limits.pullback ((toBottom E).app m) t ⟶ Limits.pullback ((toBottom E).app n) t :=
  (baseChange E t).map φ

/-- The projection of the limit of a base-changed system to a stage of it, with source and target
written as fibre products. -/
noncomputable def baseChangeConeπ (c : Cone E) (m : Λᵒᵖ) :
    Limits.pullback (c.π.app (op (⊥ : Λ))) t ⟶ Limits.pullback ((toBottom E).app m) t :=
  (baseChangeCone E t c).π.app m

/-- On the first factor, the transition map `E_m ×_{E_⊥} T ⟶ E_n ×_{E_⊥} T` is the transition map
`E_m ⟶ E_n` of `E`. -/
lemma baseChangeTrans_comp_fst {m n : Λᵒᵖ} (φ : m ⟶ n) :
    baseChangeTrans E t φ ≫ Limits.pullback.fst ((toBottom E).app n) t
      = Limits.pullback.fst ((toBottom E).app m) t ≫ E.map φ :=
  pullback_fst_naturality t ((overBottom E).map φ)

/-- On the second factor, the transition map `E_m ×_{E_⊥} T ⟶ E_n ×_{E_⊥} T` is the identity of
`T`. -/
lemma baseChangeTrans_comp_snd {m n : Λᵒᵖ} (φ : m ⟶ n) :
    baseChangeTrans E t φ ≫ Limits.pullback.snd ((toBottom E).app n) t
      = Limits.pullback.snd ((toBottom E).app m) t :=
  Over.w ((Over.pullback t).map ((overBottom E).map φ))

/-- On the first factor, the projection `c.pt ×_{E_⊥} T ⟶ E_m ×_{E_⊥} T` is the projection
`c.pt ⟶ E_m` of the cone. -/
lemma baseChangeConeπ_comp_fst (c : Cone E) (m : Λᵒᵖ) :
    baseChangeConeπ E t c m ≫ Limits.pullback.fst ((toBottom E).app m) t
      = Limits.pullback.fst (c.π.app (op (⊥ : Λ))) t ≫ c.π.app m :=
  pullback_fst_naturality t
    ((Over.liftCone E (toBottom E) c (c.π.app (op (⊥ : Λ))) (toBottom_app_fac E c)).π.app m)

/-- On the second factor, the projection `c.pt ×_{E_⊥} T ⟶ E_m ×_{E_⊥} T` is the identity of
`T`. -/
lemma baseChangeConeπ_comp_snd (c : Cone E) (m : Λᵒᵖ) :
    baseChangeConeπ E t c m ≫ Limits.pullback.snd ((toBottom E).app m) t
      = Limits.pullback.snd (c.π.app (op (⊥ : Λ))) t :=
  Over.w ((Over.pullback t).map
    ((Over.liftCone E (toBottom E) c (c.π.app (op (⊥ : Λ))) (toBottom_app_fac E c)).π.app m))

/-- The transition maps of a base-changed system compose: for `k ≤ l ≤ m` the maps for `l ≤ m`
and `k ≤ l` compose to the map for `k ≤ m`. -/
lemma baseChangeTrans_comp {k l m : Λ} (h₁ : k ≤ l) (h₂ : l ≤ m) (h₃ : k ≤ m) :
    baseChangeTrans E t (homOfLE h₂).op ≫ baseChangeTrans E t (homOfLE h₁).op
      = baseChangeTrans E t (homOfLE h₃).op :=
  map_homOfLE_op_comp (baseChange E t) h₁ h₂ h₃

/-- The projections of the limit of a base-changed system commute with its transition maps. -/
lemma baseChangeConeπ_comp_trans (c : Cone E) {m n : Λᵒᵖ} (φ : m ⟶ n) :
    baseChangeConeπ E t c m ≫ baseChangeTrans E t φ = baseChangeConeπ E t c n :=
  (baseChangeCone E t c).w φ

end BaseChangeMaps

/-! ### Composing restriction maps along a system -/

section Push

variable {S : Scheme.{u}} {Λ : Type u} [PartialOrder Λ] {G : (Over S)ᵒᵖ ⥤ Type w}

/-- Two successive restriction maps along an inverse system indexed by the opposite of a poset
compose to the restriction map of the composite inequality. -/
lemma map_system_map_apply (D : Λᵒᵖ ⥤ Over S) {k l m : Λ} (h₁ : k ≤ l) (h₂ : l ≤ m)
    (h₃ : k ≤ m) (z : G.obj (op (D.obj (op k)))) :
    G.map (D.map (homOfLE h₂).op).op (G.map (D.map (homOfLE h₁).op).op z)
      = G.map (D.map (homOfLE h₃).op).op z := by
  simp only [map_map_apply]
  rw [map_homOfLE_op_comp D h₁ h₂ h₃]

variable [OrderBot Λ] (E : Λᵒᵖ ⥤ Over S) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))

/-- For `k ≤ l ≤ m`, restricting a section of `G` along the transition maps of a base-changed
system for `k ≤ l` and then `l ≤ m` is restricting it along the transition map for `k ≤ m`. -/
lemma map_baseChangeTrans_apply {k l m : Λ} (h₁ : k ≤ l) (h₂ : l ≤ m) (h₃ : k ≤ m)
    (z : G.obj (op (Limits.pullback ((toBottom E).app (op k)) t))) :
    G.map (baseChangeTrans E t (homOfLE h₂).op).op
        (G.map (baseChangeTrans E t (homOfLE h₁).op).op z)
      = G.map (baseChangeTrans E t (homOfLE h₃).op).op z := by
  simp only [map_map_apply]
  rw [baseChangeTrans_comp]

/-- Restricting a section over a stage of a system to the corresponding stage of a base-changed
system commutes with passing to a later stage. -/
lemma map_baseChange_fst_push {k l : Λ} (hkl : k ≤ l) (r : G.obj (op (E.obj (op k)))) :
    G.map (baseChangeTrans E t (homOfLE hkl).op).op
        (G.map (Limits.pullback.fst ((toBottom E).app (op k)) t).op r)
      = G.map (Limits.pullback.fst ((toBottom E).app (op l)) t).op
        (G.map (E.map (homOfLE hkl).op).op r) := by
  simp only [map_map_apply]
  rw [baseChangeTrans_comp_fst]

variable [Nonempty Λ] [IsDirectedOrder Λ] (c : Cone E)

omit [Nonempty Λ] [IsDirectedOrder Λ] in
/-- A section over the limit of a base-changed system comes from a stage, the stage being written
as a fibre product. -/
lemma exists_map_baseChangeConeπ_eq
    (hcol : IsColimit (G.mapCocone (baseChangeCone E t c).op))
    (z : G.obj (op (Limits.pullback (c.π.app (op (⊥ : Λ))) t))) :
    ∃ (l : Λ) (y : G.obj (op (Limits.pullback ((toBottom E).app (op l)) t))),
      G.map (baseChangeConeπ E t c (op l)).op y = z :=
  exists_map_eq_of_isColimit_op G (baseChange E t) (baseChangeCone E t c) hcol z

/-- Two sections over a stage of a base-changed system with the same image over the limit agree at
a later stage, the stages being written as fibre products. -/
lemma exists_le_map_baseChangeTrans_eq
    (hcol : IsColimit (G.mapCocone (baseChangeCone E t c).op)) {l : Λ}
    (y y' : G.obj (op (Limits.pullback ((toBottom E).app (op l)) t)))
    (h : G.map (baseChangeConeπ E t c (op l)).op y
      = G.map (baseChangeConeπ E t c (op l)).op y') :
    ∃ (m : Λ) (hm : l ≤ m), G.map (baseChangeTrans E t (homOfLE hm).op).op y
      = G.map (baseChangeTrans E t (homOfLE hm).op).op y' :=
  exists_le_map_eq_of_isColimit_op G (baseChange E t) (baseChangeCone E t c) hcol y y' h

end Push

/-! ### The base change of a fibre product, along a system -/

section InterSystem

variable {S : Scheme.{u}} {Λ : Type u} [PartialOrder Λ] [OrderBot Λ] (E : Λᵒᵖ ⥤ Over S)
  {T₁ T₂ : Over S} (t₁ : T₁ ⟶ E.obj (op (⊥ : Λ))) (t₂ : T₂ ⟶ E.obj (op (⊥ : Λ)))

/-- The projections `baseChangeInterFst` at the stages of a system commute with the transition
maps of the base-changed systems. -/
lemma baseChangeInterFst_naturality {m n : Λᵒᵖ} (φ : m ⟶ n) :
    baseChangeTrans E (Limits.pullback.fst t₁ t₂ ≫ t₁) φ
        ≫ baseChangeInterFst ((toBottom E).app n) t₁ t₂
      = baseChangeInterFst ((toBottom E).app m) t₁ t₂ ≫ baseChangeTrans E t₁ φ :=
  (baseChangeInter_comp_comm (fun r => baseChangeTrans E r φ)
    (fun r => baseChangeTrans_comp_fst E r φ) (fun r => baseChangeTrans_comp_snd E r φ) t₁ t₂).1

/-- The projections `baseChangeInterSnd` at the stages of a system commute with the transition
maps of the base-changed systems. -/
lemma baseChangeInterSnd_naturality {m n : Λᵒᵖ} (φ : m ⟶ n) :
    baseChangeTrans E (Limits.pullback.fst t₁ t₂ ≫ t₁) φ
        ≫ baseChangeInterSnd ((toBottom E).app n) t₁ t₂
      = baseChangeInterSnd ((toBottom E).app m) t₁ t₂ ≫ baseChangeTrans E t₂ φ :=
  (baseChangeInter_comp_comm (fun r => baseChangeTrans E r φ)
    (fun r => baseChangeTrans_comp_fst E r φ) (fun r => baseChangeTrans_comp_snd E r φ) t₁ t₂).2

/-- The projections `baseChangeInterFst` at the limit and at a stage of a system commute with the
projections of the limits of the base-changed systems. -/
lemma baseChangeInterFst_cone (c : Cone E) (m : Λᵒᵖ) :
    baseChangeConeπ E (Limits.pullback.fst t₁ t₂ ≫ t₁) c m
        ≫ baseChangeInterFst ((toBottom E).app m) t₁ t₂
      = baseChangeInterFst (c.π.app (op (⊥ : Λ))) t₁ t₂ ≫ baseChangeConeπ E t₁ c m :=
  (baseChangeInter_comp_comm (fun r => baseChangeConeπ E r c m)
    (fun r => baseChangeConeπ_comp_fst E r c m) (fun r => baseChangeConeπ_comp_snd E r c m) t₁ t₂).1

/-- The projections `baseChangeInterSnd` at the limit and at a stage of a system commute with the
projections of the limits of the base-changed systems. -/
lemma baseChangeInterSnd_cone (c : Cone E) (m : Λᵒᵖ) :
    baseChangeConeπ E (Limits.pullback.fst t₁ t₂ ≫ t₁) c m
        ≫ baseChangeInterSnd ((toBottom E).app m) t₁ t₂
      = baseChangeInterSnd (c.π.app (op (⊥ : Λ))) t₁ t₂ ≫ baseChangeConeπ E t₂ c m :=
  (baseChangeInter_comp_comm (fun r => baseChangeConeπ E r c m)
    (fun r => baseChangeConeπ_comp_fst E r c m) (fun r => baseChangeConeπ_comp_snd E r c m) t₁ t₂).2

variable {G : (Over S)ᵒᵖ ⥤ Type w}

/-- **Pairwise compatibility at a stage passes to a later stage.** -/
lemma map_baseChangeInter_eq_of_le {k l : Λ} (hkl : k ≤ l)
    (zi : G.obj (op (Limits.pullback ((toBottom E).app (op k)) t₁)))
    (zj : G.obj (op (Limits.pullback ((toBottom E).app (op k)) t₂)))
    (h : G.map (baseChangeInterFst ((toBottom E).app (op k)) t₁ t₂).op zi
      = G.map (baseChangeInterSnd ((toBottom E).app (op k)) t₁ t₂).op zj) :
    G.map (baseChangeInterFst ((toBottom E).app (op l)) t₁ t₂).op
        (G.map (baseChangeTrans E t₁ (homOfLE hkl).op).op zi)
      = G.map (baseChangeInterSnd ((toBottom E).app (op l)) t₁ t₂).op
        (G.map (baseChangeTrans E t₂ (homOfLE hkl).op).op zj) := by
  have hk := congrArg (fun y => G.map
    (baseChangeTrans E (Limits.pullback.fst t₁ t₂ ≫ t₁) (homOfLE hkl).op).op y) h
  simp only [map_map_apply] at hk ⊢
  rw [← baseChangeInterFst_naturality, ← baseChangeInterSnd_naturality]
  exact hk

end InterSystem

/-! ### The interchange -/

section Interchange

variable {S : Scheme.{u}}

/-- **The restricted sheaf condition for a standard covering written as a base change.** Let `V`
be the limit of a directed inverse system `E` with a least stage, every stage an object of the
locally-finitely-presented part of the subcategory which is affine and of finite presentation
over one affine open `U` of `S`, and let `{T i ⟶ E_⊥}` be a standard `τ`-covering of the least
stage. Then the extension satisfies the sheaf condition for the base-changed family
`{V ×_{E_⊥} T i ⟶ V}`.

This is the filtered-colimit interchange of Stacks 0GDW. The finitely many sections and the
finitely many pairwise compatibilities between them are refined to a common stage `m` of the
three systems `E`, `baseChange E (s i)` and
`baseChange E (pullback.fst (s i) (s j) ≫ s i)`, whose limits are `V`, the members of the
covering and their pairwise fibre products; at that stage the sheaf condition holds by
`AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isStandardCovering`, and the section
it produces is pushed forward to `V`. Uniqueness is the same argument applied to two sections. -/
theorem isSheafFor_pullback_fst_of_presentation (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsStandardAffineSheafOnSubcategory.{max w (u + 1), u, v} τ P F)
    {M : Type u} [PartialOrder M] [OrderBot M] [IsDirectedOrder M] (E : Mᵒᵖ ⥤ Over S)
    (haff : ∀ m, IsAffine (E.obj m).left) (c : Cone E) (hc : IsLimit c)
    (U : S.affineOpens) (gU : ∀ m, (E.obj m).left ⟶ U.1.toScheme)
    {ι : Type v} (T : ι → Over S) (s : ∀ i, T i ⟶ E.obj (op (⊥ : M)))
    (hPE : ∀ m, lfpPart P (E.obj m)) (hgU : ∀ m, gU m ≫ U.1.ι = (E.obj m).hom)
    (hgfp : ∀ m, FinitePresentation (gU m))
    (hTstd : @IsStandardCovering τ (E.obj (op (⊥ : M))).left (haff _) ι
      (fun i => (T i).left) (fun i => (s i).left)) :
    (Presieve.ofArrows (fun i => Limits.pullback (c.π.app (op (⊥ : M))) (s i))
      (fun i => Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i))).IsSheafFor
      (extension P F) := by
  classical
  have hne : Nonempty M := ⟨⊥⟩
  have hfin : Finite ι := hTstd.finite_index
  have hTaff : ∀ i, IsAffine (T i).left := hTstd.affine_source
  have hbotaff : IsAffine (E.obj (op (⊥ : M))).left := haff _
  have hTfp : ∀ i, FinitePresentation (s i).left := fun i =>
    finitePresentation_of_isStandardCovering τ hTstd i
  -- the three systems are carried to filtered colimits
  have hcolE : IsColimit ((extension P F).mapCocone c.op) :=
    (preservesAffineLimits_extension F hP1 hP2 haF M E haff c hc).some
  have hcolW : ∀ i, IsColimit ((extension P F).mapCocone (baseChangeCone E (s i) c).op) :=
    fun i => (nonempty_isColimit_extension_baseChange F hP1 hP2 haF E haff (s i)
      (hTaff i) c hc).some
  have hcolQ : ∀ i j, IsColimit ((extension P F).mapCocone
      (baseChangeCone E (Limits.pullback.fst (s i) (s j) ≫ s i) c).op) := fun i j =>
    (nonempty_isColimit_extension_baseChange F hP1 hP2 haF E haff
      (Limits.pullback.fst (s i) (s j) ≫ s i)
      (isAffine_pullback_left (s i) (s j) hbotaff (hTaff i) (hTaff j)) c hc).some
  -- the sheaf condition at a stage
  have hstage : ∀ m : Mᵒᵖ,
      (Presieve.ofArrows (fun i => Limits.pullback ((toBottom E).app m) (s i))
        (fun i => Limits.pullback.fst ((toBottom E).app m) (s i))).IsSheafFor
        (extension P F) := by
    intro m
    have hmaff : IsAffine (E.obj m).left := haff m
    refine isSheafFor_extension_of_isStandardCovering τ F hP1 hP2 haF hbF hcF
      (hPE m).1 hmaff U (gU m) (hgU m) (hgfp m) _ _ (fun i => ?_) ?_
    · obtain ⟨Y, hY, hYiso⟩ := exists_lfpPart_iso_baseChange hP2 E haff U gU hgU hgfp
        (s i) (hTaff i) (hTfp i) m
      exact ⟨Y, hY.1, hYiso⟩
    · refine (hTstd.pullback_fst ((toBottom E).app m).left).of_iso_source
        (fun i => (isPullback_left ((toBottom E).app m) (s i)).isoPullback) _ fun i => ?_
      exact ((isPullback_left ((toBottom E).app m) (s i)).isoPullback_hom_fst).symm
  -- uniqueness
  have hsep : (Presieve.ofArrows (fun i => Limits.pullback (c.π.app (op (⊥ : M))) (s i))
      (fun i => Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i))).IsSeparatedFor
      (extension P F) := by
    intro y t₁ t₂ ht₁ ht₂
    have hagree : ∀ i, (extension P F).map
          (Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i)).op t₁
        = (extension P F).map (Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i)).op t₂ := by
      intro i
      rw [ht₁ _ (Presieve.ofArrows.mk i), ht₂ _ (Presieve.ofArrows.mk i)]
    obtain ⟨n, r₁, r₂, hr₁, hr₂⟩ :
        ∃ (n : M) (r₁ r₂ : (extension P F).obj (op (E.obj (op n)))),
          (extension P F).map (c.π.app (op n)).op r₁ = t₁ ∧
            (extension P F).map (c.π.app (op n)).op r₂ = t₂ := by
      obtain ⟨n₁, y₁, hy₁⟩ := exists_map_eq_of_isColimit_op (extension P F) E c hcolE t₁
      obtain ⟨n₂, y₂, hy₂⟩ := exists_map_eq_of_isColimit_op (extension P F) E c hcolE t₂
      obtain ⟨n, hn₁, hn₂⟩ := exists_ge_ge n₁ n₂
      refine ⟨n, (extension P F).map (E.map (homOfLE hn₁).op).op y₁,
        (extension P F).map (E.map (homOfLE hn₂).op).op y₂, ?_, ?_⟩
      · rw [map_map_apply, c.w, hy₁]
      · rw [map_map_apply, c.w, hy₂]
    have hlift : ∀ (i : ι) (r : (extension P F).obj (op (E.obj (op n))))
        (t : (extension P F).obj (op c.pt)),
        (extension P F).map (c.π.app (op n)).op r = t →
        (extension P F).map (baseChangeConeπ E (s i) c (op n)).op
            ((extension P F).map
              (Limits.pullback.fst ((toBottom E).app (op n)) (s i)).op r)
          = (extension P F).map
            (Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i)).op t := by
      intro i r t hrt
      rw [← hrt]
      simp only [map_map_apply]
      rw [baseChangeConeπ_comp_fst]
    have hEq : ∀ i, (extension P F).map (baseChangeConeπ E (s i) c (op n)).op
          ((extension P F).map
            (Limits.pullback.fst ((toBottom E).app (op n)) (s i)).op r₁)
        = (extension P F).map (baseChangeConeπ E (s i) c (op n)).op
          ((extension P F).map
            (Limits.pullback.fst ((toBottom E).app (op n)) (s i)).op r₂) := by
      intro i
      rw [hlift i r₁ t₁ hr₁, hlift i r₂ t₂ hr₂, hagree i]
    have hone : ∀ i, ∃ (q : M) (hq : n ≤ q),
        (extension P F).map
            (Limits.pullback.fst ((toBottom E).app (op q)) (s i)).op
            ((extension P F).map (E.map (homOfLE hq).op).op r₁)
          = (extension P F).map
            (Limits.pullback.fst ((toBottom E).app (op q)) (s i)).op
            ((extension P F).map (E.map (homOfLE hq).op).op r₂) := by
      intro i
      obtain ⟨q, hq, hqe⟩ := exists_le_map_baseChangeTrans_eq E (s i) c (hcolW i) _ _ (hEq i)
      refine ⟨q, hq, ?_⟩
      rw [← map_baseChange_fst_push E (s i) hq r₁, ← map_baseChange_fst_push E (s i) hq r₂]
      exact hqe
    choose q hq hqe using hone
    obtain ⟨q₀, hq₀⟩ := Finite.exists_le q
    obtain ⟨Q, hnQ, hq₀Q⟩ := exists_ge_ge n q₀
    have hqQ : ∀ i, q i ≤ Q := fun i => le_trans (hq₀ i) hq₀Q
    have hQe : ∀ i, (extension P F).map
          (Limits.pullback.fst ((toBottom E).app (op Q)) (s i)).op
          ((extension P F).map (E.map (homOfLE hnQ).op).op r₁)
        = (extension P F).map
          (Limits.pullback.fst ((toBottom E).app (op Q)) (s i)).op
          ((extension P F).map (E.map (homOfLE hnQ).op).op r₂) := by
      intro i
      rw [← map_system_map_apply E (hq i) (hqQ i) hnQ r₁,
        ← map_system_map_apply E (hq i) (hqQ i) hnQ r₂,
        ← map_baseChange_fst_push E (s i) (hqQ i)
          ((extension P F).map (E.map (homOfLE (hq i)).op).op r₁),
        ← map_baseChange_fst_push E (s i) (hqQ i)
          ((extension P F).map (E.map (homOfLE (hq i)).op).op r₂),
        hqe i]
    have hRQ : (extension P F).map (E.map (homOfLE hnQ).op).op r₁
        = (extension P F).map (E.map (homOfLE hnQ).op).op r₂ := by
      refine (hstage (op Q)).isSeparatedFor.ext ?_
      intro A h hh
      obtain ⟨i⟩ := hh
      exact hQe i
    have hmove : ∀ r : (extension P F).obj (op (E.obj (op n))),
        (extension P F).map (c.π.app (op n)).op r
          = (extension P F).map (c.π.app (op Q)).op
            ((extension P F).map (E.map (homOfLE hnQ).op).op r) := by
      intro r
      rw [map_map_apply, c.w]
    rw [← hr₁, ← hr₂, hmove r₁, hmove r₂, hRQ]
  -- existence
  refine hsep.isSheafFor ?_
  intro x hx
  have hy : ∀ (i j : ι) (A : Over S)
      (α : A ⟶ Limits.pullback (c.π.app (op (⊥ : M))) (s i))
      (β : A ⟶ Limits.pullback (c.π.app (op (⊥ : M))) (s j)),
      α ≫ Limits.pullback.fst (c.π.app (op (⊥ : M))) (s i)
          = β ≫ Limits.pullback.fst (c.π.app (op (⊥ : M))) (s j) →
      (extension P F).map α.op (x _ (Presieve.ofArrows.mk i))
        = (extension P F).map β.op (x _ (Presieve.ofArrows.mk j)) :=
    fun i j A α β h => hx α β (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) h
  obtain ⟨m₀, z, hz⟩ : ∃ (m₀ : ι → M) (z : ∀ i, (extension P F).obj
        (op (Limits.pullback ((toBottom E).app (op (m₀ i))) (s i)))),
      ∀ i, (extension P F).map (baseChangeConeπ E (s i) c (op (m₀ i))).op (z i)
        = x _ (Presieve.ofArrows.mk i) := by
    choose m₀ z hz using fun i => exists_map_baseChangeConeπ_eq E (s i) c (hcolW i)
      (x _ (Presieve.ofArrows.mk i))
    exact ⟨m₀, z, hz⟩
  obtain ⟨m₁, hm₁⟩ := Finite.exists_le m₀
  obtain ⟨w, hw⟩ : ∃ w : ∀ i, (extension P F).obj
        (op (Limits.pullback ((toBottom E).app (op m₁)) (s i))),
      ∀ i, (extension P F).map (baseChangeConeπ E (s i) c (op m₁)).op (w i)
        = x _ (Presieve.ofArrows.mk i) := by
    refine ⟨fun i => (extension P F).map
      (baseChangeTrans E (s i) (homOfLE (hm₁ i)).op).op (z i), fun i => ?_⟩
    rw [map_map_apply, baseChangeConeπ_comp_trans, hz i]
  obtain ⟨m₂, hm₁₂, W₂, hW₂c, hW₂y⟩ :
      ∃ (m₂ : M) (_ : m₁ ≤ m₂) (W₂ : ∀ i, (extension P F).obj
          (op (Limits.pullback ((toBottom E).app (op m₂)) (s i)))),
        (∀ i j, (extension P F).map
              (baseChangeInterFst ((toBottom E).app (op m₂)) (s i) (s j)).op (W₂ i)
            = (extension P F).map
              (baseChangeInterSnd ((toBottom E).app (op m₂)) (s i) (s j)).op (W₂ j)) ∧
          ∀ i, (extension P F).map (baseChangeConeπ E (s i) c (op m₂)).op (W₂ i)
            = x _ (Presieve.ofArrows.mk i) := by
    have hmid : ∀ i j, (extension P F).map
          (baseChangeConeπ E (Limits.pullback.fst (s i) (s j) ≫ s i) c (op m₁)).op
          ((extension P F).map
            (baseChangeInterFst ((toBottom E).app (op m₁)) (s i) (s j)).op (w i))
        = (extension P F).map
          (baseChangeConeπ E (Limits.pullback.fst (s i) (s j) ≫ s i) c (op m₁)).op
          ((extension P F).map
            (baseChangeInterSnd ((toBottom E).app (op m₁)) (s i) (s j)).op (w j)) := by
      intro i j
      have e₁ := hy i j _ (baseChangeInterFst (c.π.app (op (⊥ : M))) (s i) (s j))
        (baseChangeInterSnd (c.π.app (op (⊥ : M))) (s i) (s j))
        (baseChangeInter_condition (c.π.app (op (⊥ : M))) (s i) (s j))
      rw [← hw i, ← hw j] at e₁
      simp only [map_map_apply] at e₁
      simp only [map_map_apply]
      rw [baseChangeInterFst_cone, baseChangeInterSnd_cone]
      exact e₁
    have hpair : ∀ i j, ∃ (k : M) (hk : m₁ ≤ k),
        (extension P F).map
            (baseChangeInterFst ((toBottom E).app (op k)) (s i) (s j)).op
            ((extension P F).map (baseChangeTrans E (s i) (homOfLE hk).op).op (w i))
          = (extension P F).map
            (baseChangeInterSnd ((toBottom E).app (op k)) (s i) (s j)).op
            ((extension P F).map (baseChangeTrans E (s j) (homOfLE hk).op).op (w j)) := by
      intro i j
      obtain ⟨k, hk, hke⟩ := exists_le_map_baseChangeTrans_eq E
        (Limits.pullback.fst (s i) (s j) ≫ s i) c (hcolQ i j) _ _ (hmid i j)
      refine ⟨k, hk, ?_⟩
      simp only [map_map_apply] at hke
      simp only [map_map_apply]
      rw [← baseChangeInterFst_naturality, ← baseChangeInterSnd_naturality]
      exact hke
    choose k hk hke using hpair
    obtain ⟨p₀, hp₀⟩ := Finite.exists_le (fun pr : ι × ι => k pr.1 pr.2)
    obtain ⟨m₂, hm₁₂, hp₀m₂⟩ := exists_ge_ge m₁ p₀
    refine ⟨m₂, hm₁₂, fun i => (extension P F).map
      (baseChangeTrans E (s i) (homOfLE hm₁₂).op).op (w i), fun i j => ?_, fun i => ?_⟩
    · dsimp only
      have hle : k i j ≤ m₂ := le_trans (hp₀ (i, j)) hp₀m₂
      rw [← map_baseChangeTrans_apply E (s i) (hk i j) hle hm₁₂ (w i),
        ← map_baseChangeTrans_apply E (s j) (hk i j) hle hm₁₂ (w j)]
      exact map_baseChangeInter_eq_of_le E (s i) (s j) hle _ _ (hke i j)
    · dsimp only
      rw [map_map_apply, baseChangeConeπ_comp_trans, hw i]
  have hfull : ∀ (i j : ι) (A : Over S)
      (α : A ⟶ Limits.pullback ((toBottom E).app (op m₂)) (s i))
      (β : A ⟶ Limits.pullback ((toBottom E).app (op m₂)) (s j)),
      α ≫ Limits.pullback.fst ((toBottom E).app (op m₂)) (s i)
          = β ≫ Limits.pullback.fst ((toBottom E).app (op m₂)) (s j) →
      (extension P F).map α.op (W₂ i) = (extension P F).map β.op (W₂ j) := by
    intro i j A α β hαβ
    obtain ⟨γ, hγ₁, hγ₂⟩ := exists_lift_baseChangeInter ((toBottom E).app (op m₂))
      (s i) (s j) α β hαβ
    rw [← hγ₁, ← hγ₂,
      ← map_map_apply (extension P F) γ
        (baseChangeInterFst ((toBottom E).app (op m₂)) (s i) (s j)) (W₂ i),
      ← map_map_apply (extension P F) γ
        (baseChangeInterSnd ((toBottom E).app (op m₂)) (s i) (s j)) (W₂ j),
      hW₂c i j]
  obtain ⟨t, ht⟩ := exists_section_of_isSheafFor_ofArrows
    (fun i => Limits.pullback ((toBottom E).app (op m₂)) (s i))
    (fun i => Limits.pullback.fst ((toBottom E).app (op m₂)) (s i))
    (hstage (op m₂)) W₂ hfull
  refine ⟨(extension P F).map (c.π.app (op m₂)).op t, ?_⟩
  intro A h hh
  obtain ⟨i⟩ := hh
  rw [map_map_apply, ← baseChangeConeπ_comp_fst,
    ← map_map_apply (extension P F) (baseChangeConeπ E (s i) c (op m₂))
      (Limits.pullback.fst ((toBottom E).app (op m₂)) (s i)) t,
    ht i, hW₂y i]

/-- **Condition (c) of Stacks 0GDW gives the restricted sheaf condition for the extension.** Let
`S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2) of
Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a), (b) and (c). Then the extension of
`F` to `Sch/S` satisfies the sheaf condition for every standard `τ`-covering of every affine
object of `Sch/S` lying over an affine open of `S`.

This is the deduction the source performs and which
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension` carries as the hypothesis
`hstd`: the affine object is written as a directed inverse limit of affines of finite
presentation over an affine open of `S` (Stacks 00QN,
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_finitePresentation`), the standard
covering is descended to a stage of that limit (Stacks 049N,
`AlgebraicGeometry.ExtendingFunctors.exists_stage_standardCovering`) and one passes to the
filtered colimit
(`AlgebraicGeometry.ExtendingFunctors.isSheafFor_pullback_fst_of_presentation`). -/
theorem isStandardAffineSheaf_extension (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsStandardAffineSheafOnSubcategory.{max w (u + 1), u, v} τ P F) :
    IsStandardAffineSheaf.{max w (u + 1), u, v} τ (extension P F) := by
  classical
  intro ι V hV W f hstd
  obtain ⟨M, _, _, _, E, haff, π, hπ, U, gU, T, s, hPE, hgU, hgfp, hTstd, hWiso⟩ :=
    exists_baseChangePresentation_of_isStandardCovering τ hP2 hV W f hstd
  choose e he using hWiso
  refine isSheafFor_ofArrows_of_iso (Iso.refl V) e f
    (fun i => Limits.pullback.fst (π.app (op (⊥ : M))) (s i))
    (fun i => by rw [he i, Iso.refl_hom, Category.comp_id])
    (isSheafFor_pullback_fst_of_presentation τ F hP1 hP2 haF hbF hcF E haff
      (Cone.mk V π) hπ U gU T s hPE hgU hgfp hTstd)

/-- **Stacks 0GDW.** Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying
conditions (1) and (2) of Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a), (b) and
(c). Then the extension `F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to `Sch/S` is
a sheaf for each of the five topologies — Zariski, étale, smooth, syntomic and fppf.

The proof follows the source: the restricted sheaf condition for the extension, on the standard
`τ`-coverings of the affine objects of `Sch/S` lying over an affine open of `S`, is deduced from
condition (c) by `AlgebraicGeometry.ExtendingFunctors.isStandardAffineSheaf_extension` (the
special case of the source's proof), and the general case is
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_of_isStandardAffineSheaf`, applied to the
extension, which is a Zariski sheaf by condition (a). -/
@[stacks 0GDW "for each of the five topologies Zariski, étale, smooth, syntomic and fppf: the
extension F' of a functor F satisfying conditions (a), (b) and (c), from a full subcategory of
Sch/S satisfying conditions (1) and (2) of Tag 0EUW, satisfies the sheaf condition for every
τ-covering of Sch/S"]
theorem isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory (τ : CoveringTopology)
    (P : ObjectProperty (Over S)) (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsStandardAffineSheafOnSubcategory.{max w (u + 1), u, v} τ P F) :
    IsCoveringSheaf.{max w (u + 1), u, v} τ (extension P F) :=
  isCoveringSheaf_of_isStandardAffineSheaf τ (isZariskiSheaf_extension P F hP1 hP2 haF)
    (isStandardAffineSheaf_extension τ F hP1 hP2 haF hbF hcF)

/-! ### The extension of a `τ`-sheaf on the site -/

section Descent

universe t

/-- **Reindexing a family of arrows along `ULift.down` leaves the presieve it generates
unchanged**, the two families having the same image. -/
private lemma ofArrows_ulift {C : Type*} [Category C] {X : C} {κ : Type*}
    (Y : κ → C) (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows (fun i : ULift.{t} κ => Y i.down) (fun i => f i.down)
      = Presieve.ofArrows Y f := by
  funext Z
  ext g
  constructor
  · rintro ⟨i⟩
    exact .mk i.down
  · rintro ⟨i⟩
    exact .mk (ULift.up i)

/-- **The `τ`-sheaf condition on a full subcategory descends to a smaller universe of index
types.** A covering family indexed by a type of `Type v` generates the same presieve as its
reindexing along `ULift.down` to an index type of `Type (max v t)`, so the sheaf condition for
the larger universe of index types applies to it. -/
private lemma isCoveringSheafOnSubcategory_of_ulift (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (hF : IsCoveringSheafOnSubcategory.{w, u, max v t} τ P F) :
    IsCoveringSheafOnSubcategory.{w, u, v} τ P F := by
  intro κ X Y f hf
  have hobj : Presieve.ofArrows (fun i : ULift.{t} κ => (Y i.down).obj)
        (fun i => P.ι.map (f i.down))
      = Presieve.ofArrows (fun i => (Y i).obj) (fun i => P.ι.map (f i)) :=
    ofArrows_ulift (fun i => (Y i).obj) (fun i => P.ι.map (f i))
  rw [← hobj] at hf
  have h := hF X (fun i : ULift.{t} κ => Y i.down) (fun i => f i.down) hf
  rwa [ofArrows_ulift Y f] at h

end Descent

/-- **Stacks 0EUX.** Let `τ` be one of Zariski, étale, smooth, syntomic and fppf, let `S` be a
scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2) of Stacks
0EUW — the big site `(Sch/S)_τ` is such a subcategory — and let `F : 𝒞ᵒᵖ ⥤ Set` be a `τ`-sheaf
on `𝒞` satisfying property (b) of Stacks 0EUW. Then the extension `F'` of `F` to all schemes over
`S` satisfies the sheaf condition for all `τ`-coverings.

This is the unconditional form of
`AlgebraicGeometry.ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory`,
which carries the sheaf condition of the extension for the standard `τ`-coverings of the affine
objects of `Sch/S` lying over an affine open of `S` as a hypothesis only because that condition
is proved in this file, which sits above it in the import order. The ingredients are conditions
(a) and (c) of Stacks 0GDW, which a `τ`-sheaf on `𝒞` satisfies by
`AlgebraicGeometry.ExtendingFunctors.isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory`
and `ExtendingFunctors.isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory`, and
Stacks 0GDW itself,
`ExtendingFunctors.isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory`.

Condition (a) is read on open coverings indexed by the points of a scheme, so the `τ`-sheaf
condition is asked of `F` for index types of `Type (max u v)`, where `u` is the universe of the
objects of `Sch/S` and `Type v` is the universe of the index types for which the conclusion is
drawn. For `v = u` — the case of the big site `(Sch/S)_τ`, whose coverings are indexed in the
universe of its objects, which is the situation of the source — hypothesis and conclusion are
both read on index types of `Type u`. -/
@[stacks 0EUX "all five topologies: Zariski, étale, smooth, syntomic and fppf"]
theorem isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'
    (τ : CoveringTopology) (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, max u v} τ P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    IsCoveringSheaf.{max w (u + 1), u, v} τ (extension P F) :=
  have hFu : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} τ P F :=
    isCoveringSheafOnSubcategory_of_ulift τ hF
  have hFv : IsCoveringSheafOnSubcategory.{max w (u + 1), u, v} τ P F :=
    isCoveringSheafOnSubcategory_of_ulift τ hF
  isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory τ P F hP1 hP2
    (isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hP1 hFu) hbF
    (isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hFv)

/-- **Stacks 0EUX for the big site.** Let `τ` be one of Zariski, étale, smooth, syntomic and
fppf, let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1)
and (2) of Stacks 0EUW, and let `F : 𝒞ᵒᵖ ⥤ Set` be a `τ`-sheaf on `𝒞` satisfying property (b)
of Stacks 0EUW. Then the extension `F'` of `F` to all schemes over `S` satisfies the sheaf
condition for all `τ`-coverings.

This is
`ExtendingFunctors.isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory'`
read on index types of `Type u`, the universe of the objects of `Sch/S`. That is the situation
of the source: the subcategory it takes is the big site `(Sch/S)_τ`, whose covering families are
indexed in the universe of its own objects, so the `τ`-sheaf condition hypothesis and the sheaf
condition concluded are read on the same index types. -/
@[stacks 0EUX "all five topologies, for coverings indexed in the universe of the objects of
Sch/S, which is the big site of the source"]
theorem isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory_of_univ
    (τ : CoveringTopology) (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hF : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} τ P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    IsCoveringSheaf.{max w (u + 1), u, u} τ (extension P F) :=
  isCoveringSheaf_extension_of_isCoveringSheafOnSubcategory' τ P F hP1 hP2 hF hbF

end Interchange

end AlgebraicGeometry.ExtendingFunctors

end
