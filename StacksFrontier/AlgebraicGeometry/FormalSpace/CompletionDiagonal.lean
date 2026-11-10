module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion

/-!
# The diagonal of a completed morphism

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
presheaves on the big fppf site of `S` and let `T` be a set of points of `X`. Write `T'` for
the inverse image of `T` in the points of `X'`, so that the completion functor produces
`f_{/T} : X'_{/T'} ⟶ X_{/T}`.

**Stacks 0GDF** identifies the fibre product of two completions with the completion of the
fibre product: for `f : X' ⟶ X` and `g : Y ⟶ X`, inside the fibre product `X' ×_X Y` one has

`X'_{/T'} ×_{X_{/T}} Y_{/T₂} = (X' ×_X Y)_{/T''}`,

where `T''` is the inverse image of `T` in the points of `X' ×_X Y`. Taking `g = f` and
reading off the morphism induced by the two identity maps, the diagonal of the completed
morphism is the completion of the diagonal: `Δ_{f_{/T}} = (Δ_f)_{/T''}`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackPoints` is the set `T''` of points of `X' ×_X Y` lying
  over `T`.
* `AlgebraicGeometry.Space.completionSheafPullbackFst` and
  `AlgebraicGeometry.Space.completionSheafPullbackSnd` are the two projections of
  `(X' ×_X Y)_{/T''}` to `X'_{/T'}` and to `Y_{/T₂}`, characterised by their composites with
  the inclusions into the ambient sheaves.
* `AlgebraicGeometry.Space.completionSheafDiagonal` is the diagonal `Δ_{f_{/T}}` of the
  completed morphism, viewed through that identification as a morphism
  `X'_{/T'} ⟶ (X' ×_X X')_{/T''}`.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionSheafPullback`: **Stacks 0GDF**, the
  completion of a fibre product is the fibre product of the completions, the two projections
  being the ones above.
* `AlgebraicGeometry.Space.completionSheafDiagonal_eq_completionSheafMap_diagonal` and
  `AlgebraicGeometry.Space.completionSheafDiagonal_comp_completionSheafInclusion`:
  **Stacks 0GDF**, the diagonal of `f_{/T}` is the completion of the diagonal of `f`, both as
  an equality of morphisms into `(X' ×_X X')_{/T''}` and as an equality of morphisms over
  the ambient sheaf of `X' ×_X X'`.
* `AlgebraicGeometry.Space.mono_completionSheafInclusion`: a completion includes into the
  ambient sheaf by a monomorphism, so that all of the above are statements about subobjects
  of the ambient sheaf, as in the source.

## Implementation notes

The identification is proved by pasting cartesian squares, with no reference to how the
completion is built: the only inputs are that the completion square of a morphism is
cartesian (`AlgebraicGeometry.Space.isPullback_completionSheafMap`, Stacks 0APV) and that
sheafification of the universe lift turns a cartesian square of presheaves into a cartesian
square of sheaves (`AlgebraicGeometry.Space.isPullback_sheafifiedULiftMap`, which holds
because the universe lift and the fppf sheafification both preserve finite limits). Because
of this the projections are *constructed*, as the morphisms induced by the universal property
of the completion square of `f` respectively `g`, rather than merely asserted to exist.

Two completions of one presheaf along propositionally equal sets of points are equal objects
but not definitionally so, and the source of `(Δ_f)_{/T''}` is the completion of `X'` along
the inverse image of `T''` under `|Δ_f|`, which is `T'` only after
`AlgebraicGeometry.Space.pointsMap_diagonal_preimage_pullbackPoints`. The equality of
diagonals therefore carries one `eqToHom` for that set equality; the variant stated over the
ambient sheaf of `X' ×_X X'` is free of it, and is the form the source uses, an equality of
morphisms of subfunctors of `X' ×_X X'`.

Closedness of `T` and algebraicity of `X`, `X'` and `Y` are used nowhere: they are what make
the completions formal algebraic spaces, which is a separate assertion, so everything here is
proved for an arbitrary set of points of an arbitrary presheaf.

## References

* [Stacks Project, Tag 0GDF](https://stacks.math.columbia.edu/tag/0GDF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Functoriality of the sheafified universe lift -/

/-- The sheafified universe lift of an identity morphism is the identity. -/
@[simp]
theorem sheafifiedULiftMap_id (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    sheafifiedULiftMap B S hS (𝟙 Z) = 𝟙 (sheafifiedULift B S hS Z) := by
  apply ObjectProperty.hom_ext
  unfold sheafifiedULiftMap sheafifiedULift
  simp

/-- The sheafified universe lift of a composite is the composite of the sheafified universe
lifts. -/
@[simp]
theorem sheafifiedULiftMap_comp (g : X' ⟶ Y) (h : Y ⟶ X) :
    sheafifiedULiftMap B S hS (g ≫ h) =
      sheafifiedULiftMap B S hS g ≫ sheafifiedULiftMap B S hS h := by
  apply ObjectProperty.hom_ext
  unfold sheafifiedULiftMap
  change (BigFppfOver.topology B S hS).sheafifyMap
      (Functor.whiskerRight (g ≫ h) uliftFunctor.{u + 1}) = _
  rw [Functor.whiskerRight_comp,
    CategoryTheory.GrothendieckTopology.sheafifyMap_comp]
  rfl

/-- The sheafified universe lift carries the fibre product of two morphisms of presheaves to
the fibre product of the sheafified universe lifts: the universe lift and the fppf
sheafification both preserve finite limits. -/
theorem isPullback_sheafifiedULiftMap (f : X' ⟶ X) (g : Y ⟶ X) :
    IsPullback (sheafifiedULiftMap B S hS (pullback.fst f g))
      (sheafifiedULiftMap B S hS (pullback.snd f g))
      (sheafifiedULiftMap B S hS f) (sheafifiedULiftMap B S hS g) := by
  let C := BigFppfOver B S hS
  let H : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type (u + 1)) :=
    (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  exact ((IsPullback.of_isLimit (pullback.isLimit f g)).map H).map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-! ### The completion includes into the ambient sheaf by a monomorphism -/

/-- The completion of a presheaf along a set of points includes into the sheafified universe
lift of that presheaf by a monomorphism: the inclusion of the subfunctor of sections with
image in the set is a monomorphism, and fppf sheafification preserves finite limits, hence
monomorphisms. -/
theorem mono_completionSheafInclusion (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS Z)) : Mono (completionSheafInclusion B S hS Z T) := by
  have hker : IsKernelPair (completionSubfunctor B S hS Z T).ι (𝟙 _) (𝟙 _) :=
    IsKernelPair.id_of_mono _
  have h := hker.map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  rw [CategoryTheory.Functor.map_id] at h
  constructor
  intro W a b hab
  have ha := h.lift_fst a b hab
  have hb := h.lift_snd a b hab
  rw [Category.comp_id] at ha hb
  exact ha.symm.trans hb

/-! ### The completion of a fibre product -/

/-- The set `T''` of points of a fibre product `X' ×_X Y` lying over a set `T` of points of
`X`, that is, the inverse image of `T` under the map on points induced by either projection
followed by the corresponding morphism to `X`. -/
def pullbackPoints (f : X' ⟶ X) (g : Y ⟶ X) (T : Set (points B S hS X)) :
    Set (points B S hS (pullback f g)) :=
  pointsMap B S hS (pullback f g) (pullback.fst f g ≫ f) ⁻¹' T

/-- The set `T''` is also the inverse image of `T` along the second projection. -/
theorem pullbackPoints_eq_preimage_snd (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    pullbackPoints B S hS f g T =
      pointsMap B S hS (pullback f g) (pullback.snd f g ≫ g) ⁻¹' T := by
  rw [pullbackPoints, pullback.condition]

/-- The set `T''` of points of `X' ×_X Y` lying over `T` is the inverse image along the first
projection of the set `T'` of points of `X'` lying over `T`. -/
theorem pullbackPoints_eq_preimage_fst (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    pullbackPoints B S hS f g T =
      pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹'
        (pointsMap B S hS X' f ⁻¹' T) := by
  rw [pullbackPoints, pointsMap_comp, Set.preimage_comp]

/-- The first projection `(X' ×_X Y)_{/T''} ⟶ X'_{/T'}`, induced by the universal property of
the cartesian completion square of `f` from the first projection of `X' ×_X Y` and the
completion of `X' ×_X Y ⟶ X`. -/
def completionSheafPullbackFst (f : X' ⟶ X) (g : Y ⟶ X) (T : Set (points B S hS X)) :
    completionSheaf B S hS (pullback f g) (pullbackPoints B S hS f g T) ⟶
      completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T) :=
  (isPullback_completionSheafMap B S hS f T).lift
    (completionSheafInclusion B S hS (pullback f g) (pullbackPoints B S hS f g T) ≫
      sheafifiedULiftMap B S hS (pullback.fst f g))
    (completionSheafMap B S hS (pullback.fst f g ≫ f) T)
    (by
      rw [Category.assoc, ← sheafifiedULiftMap_comp]
      exact (isPullback_completionSheafMap B S hS (pullback.fst f g ≫ f) T).w)

/-- The second projection `(X' ×_X Y)_{/T''} ⟶ Y_{/T₂}`, induced by the universal property of
the cartesian completion square of `g` from the second projection of `X' ×_X Y` and the
completion of `X' ×_X Y ⟶ X`. -/
def completionSheafPullbackSnd (f : X' ⟶ X) (g : Y ⟶ X) (T : Set (points B S hS X)) :
    completionSheaf B S hS (pullback f g) (pullbackPoints B S hS f g T) ⟶
      completionSheaf B S hS Y (pointsMap B S hS Y g ⁻¹' T) :=
  (isPullback_completionSheafMap B S hS g T).lift
    (completionSheafInclusion B S hS (pullback f g) (pullbackPoints B S hS f g T) ≫
      sheafifiedULiftMap B S hS (pullback.snd f g))
    (completionSheafMap B S hS (pullback.fst f g ≫ f) T)
    (by
      rw [Category.assoc, ← sheafifiedULiftMap_comp, ← pullback.condition]
      exact (isPullback_completionSheafMap B S hS (pullback.fst f g ≫ f) T).w)

/-- The first projection of the completed fibre product is the first projection of the fibre
product, read inside the ambient sheaf of `X' ×_X Y`. -/
@[simp]
theorem completionSheafPullbackFst_comp_completionSheafInclusion (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafPullbackFst B S hS f g T ≫
        completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T) =
      completionSheafInclusion B S hS (pullback f g) (pullbackPoints B S hS f g T) ≫
        sheafifiedULiftMap B S hS (pullback.fst f g) :=
  (isPullback_completionSheafMap B S hS f T).lift_fst _ _ _

/-- The first projection of the completed fibre product is compatible with the structure
morphisms to `X_{/T}`. -/
@[simp]
theorem completionSheafPullbackFst_comp_completionSheafMap (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafPullbackFst B S hS f g T ≫ completionSheafMap B S hS f T =
      completionSheafMap B S hS (pullback.fst f g ≫ f) T :=
  (isPullback_completionSheafMap B S hS f T).lift_snd _ _ _

/-- The second projection of the completed fibre product is the second projection of the
fibre product, read inside the ambient sheaf of `X' ×_X Y`. -/
@[simp]
theorem completionSheafPullbackSnd_comp_completionSheafInclusion (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafPullbackSnd B S hS f g T ≫
        completionSheafInclusion B S hS Y (pointsMap B S hS Y g ⁻¹' T) =
      completionSheafInclusion B S hS (pullback f g) (pullbackPoints B S hS f g T) ≫
        sheafifiedULiftMap B S hS (pullback.snd f g) :=
  (isPullback_completionSheafMap B S hS g T).lift_fst _ _ _

/-- The second projection of the completed fibre product is compatible with the structure
morphisms to `X_{/T}`. -/
@[simp]
theorem completionSheafPullbackSnd_comp_completionSheafMap (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafPullbackSnd B S hS f g T ≫ completionSheafMap B S hS g T =
      completionSheafMap B S hS (pullback.fst f g ≫ f) T :=
  (isPullback_completionSheafMap B S hS g T).lift_snd _ _ _

/-- **Stacks 0GDF.** The completion of a fibre product is the fibre product of the
completions: for morphisms `f : X' ⟶ X` and `g : Y ⟶ X` of presheaves on the big fppf site of
`S` and a set `T` of points of `X`, the square formed by `(X' ×_X Y)_{/T''}`, the two
completions `X'_{/T'}` and `Y_{/T₂}` and `X_{/T}` is cartesian, so that
`X'_{/T'} ×_{X_{/T}} Y_{/T₂} = (X' ×_X Y)_{/T''}` as subobjects of the ambient sheaf of
`X' ×_X Y`. -/
@[stacks 0GDF "fibre product of completions"]
theorem isPullback_completionSheafPullback (f : X' ⟶ X) (g : Y ⟶ X)
    (T : Set (points B S hS X)) :
    IsPullback (completionSheafPullbackFst B S hS f g T)
      (completionSheafPullbackSnd B S hS f g T)
      (completionSheafMap B S hS f T) (completionSheafMap B S hS g T) := by
  set p₁ := completionSheafPullbackFst B S hS f g T
  set p₂ := completionSheafPullbackSnd B S hS f g T
  have hp₂q := completionSheafPullbackSnd_comp_completionSheafMap B S hS f g T
  have hA' : IsPullback
      (completionSheafInclusion B S hS (pullback f g) (pullbackPoints B S hS f g T))
      (p₂ ≫ completionSheafMap B S hS g T)
      (sheafifiedULiftMap B S hS (pullback.snd f g) ≫ sheafifiedULiftMap B S hS g)
      (completionSheafInclusion B S hS X T) := by
    rw [hp₂q, ← sheafifiedULiftMap_comp, ← pullback.condition]
    exact isPullback_completionSheafMap B S hS (pullback.fst f g ≫ f) T
  have houter := (hA'.of_bot
    (completionSheafPullbackSnd_comp_completionSheafInclusion B S hS f g T).symm
    (isPullback_completionSheafMap B S hS g T)).paste_horiz
      (isPullback_sheafifiedULiftMap B S hS f g)
  rw [← completionSheafPullbackFst_comp_completionSheafInclusion B S hS f g T,
    (isPullback_completionSheafMap B S hS g T).w] at houter
  exact houter.of_right
    ((completionSheafPullbackFst_comp_completionSheafMap B S hS f g T).trans hp₂q.symm)
    (isPullback_completionSheafMap B S hS f T)

/-! ### The diagonal of a completed morphism -/

/-- The diagonal `Δ_{f_{/T}}` of the completed morphism `f_{/T} : X'_{/T'} ⟶ X_{/T}`, viewed
through the identification of `X'_{/T'} ×_{X_{/T}} X'_{/T'}` with `(X' ×_X X')_{/T''}`: the
unique morphism whose composites with the two projections are the identity. -/
def completionSheafDiagonal (f : X' ⟶ X) (T : Set (points B S hS X)) :
    completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T) ⟶
      completionSheaf B S hS (pullback f f) (pullbackPoints B S hS f f T) :=
  (isPullback_completionSheafPullback B S hS f f T).lift (𝟙 _) (𝟙 _) rfl

/-- The diagonal of a completed morphism is a section of the first projection. -/
@[simp]
theorem completionSheafDiagonal_comp_fst (f : X' ⟶ X) (T : Set (points B S hS X)) :
    completionSheafDiagonal B S hS f T ≫ completionSheafPullbackFst B S hS f f T = 𝟙 _ :=
  (isPullback_completionSheafPullback B S hS f f T).lift_fst _ _ _

/-- The diagonal of a completed morphism is a section of the second projection. -/
@[simp]
theorem completionSheafDiagonal_comp_snd (f : X' ⟶ X) (T : Set (points B S hS X)) :
    completionSheafDiagonal B S hS f T ≫ completionSheafPullbackSnd B S hS f f T = 𝟙 _ :=
  (isPullback_completionSheafPullback B S hS f f T).lift_snd _ _ _

/-- **Stacks 0GDF.** The diagonal of the completed morphism is the diagonal of the original
morphism, read inside the ambient sheaf of `X' ×_X X'`: this is the equality
`Δ_{f_{/T}} = (Δ_f)_{/T''}` of morphisms of subobjects of `X' ×_X X'`, the inclusion of a
completion into the ambient sheaf being a monomorphism. -/
@[stacks 0GDF "diagonals agree over the fibre product"]
theorem completionSheafDiagonal_comp_completionSheafInclusion (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafDiagonal B S hS f T ≫
        completionSheafInclusion B S hS (pullback f f) (pullbackPoints B S hS f f T) =
      completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T) ≫
        sheafifiedULiftMap B S hS (pullback.diagonal f) := by
  apply (isPullback_sheafifiedULiftMap B S hS f f).hom_ext
  · rw [Category.assoc, ← completionSheafPullbackFst_comp_completionSheafInclusion B S hS f f T,
      ← Category.assoc]
    simp [← sheafifiedULiftMap_comp]
  · rw [Category.assoc, ← completionSheafPullbackSnd_comp_completionSheafInclusion B S hS f f T,
      ← Category.assoc]
    simp [← sheafifiedULiftMap_comp]

/-- The points of `X'` lying over the set `T''` of points of `X' ×_X X'` under the diagonal
are exactly the points lying over `T`, because the diagonal followed by a projection is the
identity. -/
theorem pointsMap_diagonal_preimage_pullbackPoints (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    pointsMap B S hS X' (pullback.diagonal f) ⁻¹' pullbackPoints B S hS f f T =
      pointsMap B S hS X' f ⁻¹' T := by
  rw [pullbackPoints, ← Set.preimage_comp, ← pointsMap_comp, ← Category.assoc,
    pullback.diagonal_fst, Category.id_comp]

private theorem eqToHom_comp_completionSheafInclusion (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {T₁ T₂ : Set (points B S hS Z)} (h : T₁ = T₂) :
    eqToHom (congrArg (completionSheaf B S hS Z) h) ≫ completionSheafInclusion B S hS Z T₂ =
      completionSheafInclusion B S hS Z T₁ := by
  subst h
  simp

/-- **Stacks 0GDF.** The diagonal of the completed morphism is the completion of the diagonal:
`Δ_{f_{/T}} = (Δ_f)_{/T''}` as morphisms `X'_{/T'} ⟶ (X' ×_X X')_{/T''}`. The `eqToHom`
transports the source of `(Δ_f)_{/T''}`, the completion of `X'` along the inverse image of
`T''` under the diagonal, to the completion of `X'` along `T'`; the two sets of points are
equal by `AlgebraicGeometry.Space.pointsMap_diagonal_preimage_pullbackPoints`. -/
@[stacks 0GDF "equality of diagonals"]
theorem completionSheafDiagonal_eq_completionSheafMap_diagonal (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheafDiagonal B S hS f T =
      eqToHom (congrArg (completionSheaf B S hS X')
          (pointsMap_diagonal_preimage_pullbackPoints B S hS f T).symm) ≫
        completionSheafMap B S hS (pullback.diagonal f) (pullbackPoints B S hS f f T) := by
  have := mono_completionSheafInclusion B S hS (pullback f f) (pullbackPoints B S hS f f T)
  rw [← cancel_mono
    (completionSheafInclusion B S hS (pullback f f) (pullbackPoints B S hS f f T)),
    completionSheafDiagonal_comp_completionSheafInclusion, Category.assoc,
    ← (isPullback_completionSheafMap B S hS (pullback.diagonal f)
      (pullbackPoints B S hS f f T)).w,
    ← Category.assoc, eqToHom_comp_completionSheafInclusion B S hS X'
      (pointsMap_diagonal_preimage_pullbackPoints B S hS f T).symm]

end AlgebraicGeometry.Space

end
