module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

/-!
# The constant sheaf `ℤ` is the sheaf of locally constant integer-valued functions

For a topological space `X`, the presheaf `locallyConstantIntPresheaf X` of locally constant
`ℤ`-valued functions is a sheaf, and it is the constant sheaf with value `ℤ`: the map from the
constant presheaf sending `n` to the constant function `n` is locally injective and locally
surjective, so it becomes an isomorphism after sheafification.

## Main definitions

* `locallyConstantIntSheaf X`: the sheaf of locally constant `ℤ`-valued functions on `X`.
* `constToLocallyConstantInt X`: the map from the constant presheaf with value `ℤ`, sending `n`
  to the constant function `n`.
* `constantSheafIsoLocallyConstantInt X`: the isomorphism between Mathlib's constant sheaf
  `(constantSheaf _ AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))` and
  `locallyConstantIntSheaf X`.

## Main results

* `isSheaf_locallyConstantIntPresheaf`: the sheaf condition, by unique gluing.
* `isLocallyInjective_constToLocallyConstantInt` and
  `isLocallySurjective_constToLocallyConstantInt`: the comparison is locally bijective.

## Implementation notes

The value of the constant sheaf is `ULift ℤ`, the coefficient group `Sheaf.H` uses, so that the
isomorphism lives in `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` for a space in any
universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

variable (X : TopCat.{u})

/-- Two members of a compatible family of locally constant functions agree at every point of the
overlap of their domains. -/
theorem locallyConstantIntPresheaf_isCompatible_apply {ι : Type u} {U : ι → Opens X}
    {sf : ∀ i, ToType ((locallyConstantIntPresheaf X).obj (op (U i)))}
    (h : Presheaf.IsCompatible (locallyConstantIntPresheaf X) U sf) (i j : ι) (y : X)
    (hi : y ∈ U i) (hj : y ∈ U j) :
    (sf i : LocallyConstant (U i : Set X) ℤ) ⟨y, hi⟩ =
      (sf j : LocallyConstant (U j : Set X) ℤ) ⟨y, hj⟩ :=
  congrArg (fun f : LocallyConstant ((U i ⊓ U j : Opens X) : Set X) ℤ => f ⟨y, hi, hj⟩) (h i j)

/-- **The locally constant `ℤ`-valued functions form a sheaf.** A compatible family glues
pointwise, and the glued function is locally constant because near each point it agrees with one
member of the family. -/
theorem isSheaf_locallyConstantIntPresheaf : (locallyConstantIntPresheaf X).IsSheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hpt := locallyConstantIntPresheaf_isCompatible_apply X hsf
  have hmem : ∀ y : ((iSup U : Opens X) : Set X), ∃ i, y.1 ∈ U i :=
    fun y => Opens.mem_iSup.mp y.2
  choose idx hidx using hmem
  let g : ((iSup U : Opens X) : Set X) → ℤ := fun y =>
    (sf (idx y) : LocallyConstant (U (idx y) : Set X) ℤ) ⟨y.1, hidx y⟩
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y₀
    set i₀ := idx y₀
    set s₀ : LocallyConstant (U i₀ : Set X) ℤ := sf i₀
    set F : Set (U i₀ : Set X) := {p | s₀ p = s₀ ⟨y₀.1, hidx y₀⟩}
    set T : Set X := (Subtype.val : ↥(U i₀ : Set X) → X) '' F
    have hF : IsOpen T :=
      (U i₀).isOpen.isOpenMap_subtype_val _ (s₀.isLocallyConstant.isOpen_fiber _)
    refine ⟨Subtype.val ⁻¹' T, hF.preimage continuous_subtype_val,
      ⟨⟨y₀.1, hidx y₀⟩, rfl, rfl⟩, ?_⟩
    rintro y ⟨p, hp, hpy⟩
    have hy : y.1 ∈ U i₀ := hpy ▸ p.2
    change (sf (idx y) : LocallyConstant (U (idx y) : Set X) ℤ) ⟨y.1, hidx y⟩ = s₀ ⟨y₀.1, hidx y₀⟩
    rw [hpt (idx y) i₀ y.1 (hidx y) hy, ← hp]
    exact congrArg s₀ (Subtype.ext hpy.symm)
  refine ⟨(⟨g, hg⟩ : LocallyConstant ((iSup U : Opens X) : Set X) ℤ), ?_, ?_⟩
  · intro i
    refine LocallyConstant.ext fun y => ?_
    change (sf (idx _) : LocallyConstant (U (idx _) : Set X) ℤ) ⟨y.1, hidx _⟩ =
      (sf i : LocallyConstant (U i : Set X) ℤ) y
    exact hpt _ i y.1 _ y.2
  · intro s hs
    refine LocallyConstant.ext fun y => ?_
    have h := congrArg (fun f : LocallyConstant (U (idx y) : Set X) ℤ => f ⟨y.1, hidx y⟩)
      (hs (idx y))
    exact h

/-- The sheaf of locally constant `ℤ`-valued functions on `X`. -/
def locallyConstantIntSheaf :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨locallyConstantIntPresheaf X, isSheaf_locallyConstantIntPresheaf X⟩

/-- The underlying presheaf of `locallyConstantIntSheaf X` is `locallyConstantIntPresheaf X`. -/
@[simp]
theorem locallyConstantIntSheaf_obj :
    (locallyConstantIntSheaf X).obj = locallyConstantIntPresheaf X := rfl

/-- The map from the constant presheaf with value `ℤ` to the locally constant functions: on every
open it sends `n` to the constant function `n`. -/
def constToLocallyConstantInt :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      locallyConstantIntPresheaf X where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun n => LocallyConstant.const _ n.down
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- The comparison sends `n` to the constant function `n`. -/
@[simp]
theorem constToLocallyConstantInt_app_apply (V : (Opens X)ᵒᵖ) (n : ULift.{u} ℤ)
    (y : (V.unop : Set X)) :
    ((constToLocallyConstantInt X).app V n : LocallyConstant (V.unop : Set X) ℤ) y = n.down :=
  rfl

/-- The comparison is locally injective: two integers with the same constant function on an
open agree as soon as that open has a point. -/
instance isLocallyInjective_constToLocallyConstantInt :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (constToLocallyConstantInt X) where
  equalizerSieve_mem {V} m n h := by
    intro y hy
    refine ⟨V.unop, 𝟙 _, ?_, hy⟩
    have hmn : m.down = n.down :=
      congrArg (fun f : LocallyConstant (V.unop : Set X) ℤ => f ⟨y, hy⟩) h
    change m = n
    exact ULift.ext hmn

/-- The comparison is locally surjective: a locally constant function is constant on an open
neighbourhood of each point. -/
instance isLocallySurjective_constToLocallyConstantInt :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (constToLocallyConstantInt X) where
  imageSieve_mem {V} s := by
    intro y hy
    let s' : LocallyConstant (V : Set X) ℤ := s
    let F : Set (V : Set X) := {p | s' p = s' ⟨y, hy⟩}
    set T : Set X := (Subtype.val : ↥(V : Set X) → X) '' F
    have hF : IsOpen T :=
      V.isOpen.isOpenMap_subtype_val _ (s'.isLocallyConstant.isOpen_fiber _)
    have hle : (⟨T, hF⟩ : Opens X) ≤ V := by
      rintro _ ⟨p, -, rfl⟩
      exact p.2
    refine ⟨⟨T, hF⟩, homOfLE hle, ⟨ULift.up (s' ⟨y, hy⟩), ?_⟩, ⟨⟨y, hy⟩, rfl, rfl⟩⟩
    refine LocallyConstant.ext fun q => ?_
    obtain ⟨p, hp, hpq⟩ := q.2
    change s' ⟨y, hy⟩ = s' ⟨q.1, hle q.2⟩
    rw [← hp]
    exact congrArg s' (Subtype.ext hpq)

/-- The comparison from the constant presheaf becomes an isomorphism after sheafification, being
locally bijective. -/
instance isIso_presheafToSheaf_map_constToLocallyConstantInt :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (constToLocallyConstantInt X)) :=
  ((Opens.grothendieckTopology X).W_iff _).mp
    ((Opens.grothendieckTopology X).W_of_isLocallyBijective _)

/-- **The constant sheaf `ℤ` is the sheaf of locally constant `ℤ`-valued functions.** The
comparison from the constant presheaf is locally bijective, hence inverted by sheafification. -/
noncomputable def constantSheafIsoLocallyConstantInt :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ≅ locallyConstantIntSheaf X :=
  @asIso _ _ _ _ ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (constToLocallyConstantInt X)) (isIso_presheafToSheaf_map_constToLocallyConstantInt X) ≪≫
    (sheafificationIso (locallyConstantIntSheaf X)).symm

end TopCat
