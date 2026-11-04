module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatBaseChange

/-!
# The upper shriek of the diagonal applied to `L pr₁^* f^!𝒪_Y`

Let `S` be Noetherian, `f : X ⟶ Y` a flat morphism of `AlgebraicGeometry.FTS S` and `W ⊆ X ×_Y X`
an open through which the diagonal factors as a closed immersion `Δ : X ⟶ W`. With `p = pr₁|_W`
and `K = f^!𝒪_Y` computed at any compactification, there is an isomorphism

`Δ^!(Lp^*K) ≅ 𝒪_X`

in `D_QCoh(𝒪_X)`, which is the computation of the proof of [Stacks, Tag 0E9W]:
`𝒪_X = Δ^! q^! 𝒪_X = Δ^! (Lp^* f^!𝒪_Y)` for `q = pr₂|_W`, using the flat base change
`Lpr₁^* ∘ f^! ≅ pr₂^! ∘ Lf^*` of [Stacks, Tag 0E9U], the restriction of `pr₂^!` to `W`, and
`Δ^! ∘ q^! ≅ (Δ ≫ q)^! = 𝟙^!` ([Stacks, Tag 0ATX]).

## Main definitions

* `Stacks.Duality.DiagonalUpperShriek.openFTS`: `W` as an object of `FTS S`.
* `Stacks.Duality.diagonalUpperShriekIso`: the isomorphism `Δ^!(Lp^* f^!𝒪_Y) ≅ 𝒪_X`, with `Δ^!` the
  right adjoint of `RΔ_*` on `D_QCoh`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

namespace DiagonalUpperShriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- `X ×_Y X` as an object of `FTS S`, over `S` through the first projection. -/
abbrev productFTS : FTS S := FTS.mk (pullback.fst f.left f.left ≫ X.hom)

/-- The first projection `X ×_Y X ⟶ X` in `FTS S`. -/
abbrev fstHom : productFTS f ⟶ X := MorphismProperty.Over.homMk (pullback.fst f.left f.left) rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The two projections `X ×_Y X ⟶ X` agree over `S`. -/
theorem snd_comp_hom : pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom := by
  have h : f.left ≫ Y.hom = X.hom := MorphismProperty.Over.w f
  rw [← h, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- The second projection `X ×_Y X ⟶ X` in `FTS S`. -/
abbrev sndHom : productFTS f ⟶ X :=
  MorphismProperty.Over.homMk (pullback.snd f.left f.left) (snd_comp_hom f)

/-- The cartesian square `X ×_Y X` over `X ⟶ Y ⟵ X`. -/
theorem isPullback_fst_snd :
    IsPullback (fstHom f).left (sndHom f).left f.left f.left :=
  IsPullback.of_hasPullback f.left f.left

/-- The fibre product `X ×_Y X` is Noetherian. -/
instance isNoetherian_pullback : IsNoetherian (pullback f.left f.left) :=
  FTS.isNoetherian (productFTS f)

variable (D : f.left.DiagonalOpen)

/-- The inclusion `W ⟶ X ×_Y X` is an open immersion. -/
instance isOpenImmersion_ι : IsOpenImmersion D.ι := D.isOpenImmersion

/-- The diagonal `Δ : X ⟶ W` is a closed immersion. -/
instance isClosedImmersion_diag : IsClosedImmersion D.diag := D.isClosedImmersion

/-- The open `W ⊆ X ×_Y X` as an object of `FTS S`. -/
abbrev openFTS : FTS S := FTS.mk (D.ι ≫ pullback.fst f.left f.left ≫ X.hom)

/-- The open immersion `W ⟶ X ×_Y X` in `FTS S`. -/
abbrev ιHom : openFTS f D ⟶ productFTS f := MorphismProperty.Over.homMk D.ι rfl

/-- The underlying morphism of `ιHom f D` is an open immersion. -/
instance : IsOpenImmersion (ιHom f D).left := D.isOpenImmersion

/-- The diagonal `Δ : X ⟶ W` in `FTS S`. -/
abbrev diagHom : X ⟶ openFTS f D :=
  MorphismProperty.Over.homMk D.diag (by
    change D.diag ≫ D.ι ≫ pullback.fst f.left f.left ≫ X.hom = X.hom
    rw [← Category.assoc, D.fac, ← Category.assoc, pullback.diagonal_fst, Category.id_comp])

/-- The underlying morphism of `diagHom f D` is a closed immersion. -/
instance : IsClosedImmersion (diagHom f D).left := D.isClosedImmersion

/-- The open `W` is quasi-compact. -/
instance compactSpace_W : CompactSpace D.W := inferInstanceAs (CompactSpace (openFTS f D).left)

/-- The open `W` is quasi-separated. -/
instance quasiSeparatedSpace_W : QuasiSeparatedSpace D.W :=
  inferInstanceAs (QuasiSeparatedSpace (openFTS f D).left)

/-- `q = pr₂|_W : W ⟶ X` in `FTS S`. -/
abbrev sndRestrict : openFTS f D ⟶ X := ιHom f D ≫ sndHom f

/-- `Δ` followed by `pr₂|_W` is the identity of `X`. -/
theorem diagHom_comp_sndRestrict : diagHom f D ≫ sndRestrict f D = 𝟙 X := by
  ext1
  show D.diag ≫ D.ι ≫ pullback.snd f.left f.left = 𝟙 X.left
  rw [← Category.assoc, D.fac, pullback.diagonal_snd]

/-- The composite `Δ ≫ pr₂|_W : X ⟶ X` is proper. -/
instance isProper_diagHom_comp_sndRestrict : IsProper (diagHom f D ≫ sndRestrict f D).left := by
  rw [diagHom_comp_sndRestrict]
  exact inferInstanceAs (IsProper (𝟙 X.left))

/-- The identity of `X` is proper. -/
instance isProper_id_left : IsProper (𝟙 X : X ⟶ X).left := inferInstanceAs (IsProper (𝟙 X.left))

/-- `𝒪_X` as an object of `D⁺_QCoh(𝒪_X)`. -/
abbrev structureSheafPlus (Z : Scheme.{u}) : quasiCoherentDerivedCategoryPlusOfModel Z :=
  ⟨DerivedPushforward.derivedStructureSheaf Z,
    Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _⟩

end DiagonalUpperShriek

open DiagonalUpperShriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) (D : f.left.DiagonalOpen) [Flat f.left]

/-- `Lpr₁^*(f^!𝒪_Y) ≅ pr₂^!𝒪_X` on `X ×_Y X`, for the base change compactification of `pr₂`:
the flat base change isomorphism of [Stacks, Tag 0E9U] at `𝒪_Y`, followed by `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackFstUpperShriekIso :
    (quasiCoherentDerivedPullback' (pullback.fst f.left f.left)).obj
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)) ≅
      (upperShriek (sndHom f) (baseChangeCompactification (isPullback_fst_snd f) j)).obj
        (DerivedPushforward.derivedStructureSheaf X.left) :=
  @asIso _ _ _ _ ((upperShriekBaseChangeMap (isPullback_fst_snd f) j).app
      (DerivedPushforward.derivedStructureSheaf Y.left))
    (isIso_upperShriekBaseChangeMap_app (isPullback_fst_snd f) j
      (DerivedPushforward.derivedStructureSheaf Y.left) (structureSheafPlus Y.left).property) ≪≫
    (upperShriek (sndHom f) (baseChangeCompactification (isPullback_fst_snd f) j)).mapIso
      (ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso f.left))

/-- The compactification of `pr₂|_W` restricted from the base change compactification of `pr₂`. -/
abbrev sndRestrictCompactification : CompactificationOf (Over.mk (sndRestrict f D).left) :=
  (baseChangeCompactification (isPullback_fst_snd f) j).precompOpen (ιHom f D).left

/-- `Lp^*(f^!𝒪_Y) ≅ q^!𝒪_X` on `W`, `p = pr₁|_W`, `q = pr₂|_W`. -/
def pullbackProjUpperShriekIso :
    (quasiCoherentDerivedPullback' D.proj).obj
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)) ≅
      (upperShriek (sndRestrict f D) (sndRestrictCompactification f j D)).obj
        (DerivedPushforward.derivedStructureSheaf X.left) :=
  ((quasiCoherentDerivedPullbackCompIso D.ι (pullback.fst f.left f.left)).app _).symm ≪≫
    (quasiCoherentDerivedPullback' D.ι).mapIso (pullbackFstUpperShriekIso f j) ≪≫
    ((upperShriekPrecompOpenIso (ιHom f D) (sndHom f)
      (baseChangeCompactification (isPullback_fst_snd f) j)).app _).symm

/-- `Δ^!(q^!𝒪_X) ≅ 𝒪_X`, through `Δ^! ∘ q^! ≅ (Δ ≫ q)^! = 𝟙^! ≅ 𝟭` on `D⁺_QCoh`. -/
def diagUpperShriekSndRestrictIso :
    (upperShriek (diagHom f D) (properCompactification (diagHom f D))).obj
        ((upperShriek (sndRestrict f D) (sndRestrictCompactification f j D)).obj
          (DerivedPushforward.derivedStructureSheaf X.left)) ≅
      DerivedPushforward.derivedStructureSheaf X.left :=
  (ObjectProperty.ι _).mapIso ((upperShriekCompIso (diagHom f D) (sndRestrict f D)
      (properCompactification (diagHom f D)) (sndRestrictCompactification f j D)
      (properCompactification (diagHom f D ≫ sndRestrict f D))).app
        (structureSheafPlus X.left)).symm ≪≫
    (ObjectProperty.ι _).mapIso ((upperShriekPlusCongr (diagHom_comp_sndRestrict f D)
      (properCompactification (diagHom f D ≫ sndRestrict f D))
      (properCompactification (𝟙 X))).app (structureSheafPlus X.left)) ≪≫
    (upperShriekProperIso (𝟙 X)).app _ ≪≫
    (twistedInverseImageIdIso X.left _).app _

/-- **The computation of the proof of [Stacks, Tag 0E9W].** For `f : X ⟶ Y` a flat morphism of
`FTS S`, `S` Noetherian, any compactification `j` of `f` and any open `W ⊆ X ×_Y X` through which
the diagonal factors as a closed immersion `Δ : X ⟶ W`, with `p = pr₁|_W`:
`Δ^!(Lp^* f^!𝒪_Y) ≅ 𝒪_X` in `D_QCoh(𝒪_X)`, `Δ^!` the right adjoint of `RΔ_*`. -/
def diagonalUpperShriekIso :
    (twistedInverseImage D.diag (isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag)).obj
        ((quasiCoherentDerivedPullback' D.proj).obj
          ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))) ≅
      DerivedPushforward.derivedStructureSheaf X.left :=
  (twistedInverseImage D.diag (isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag)).mapIso
      (pullbackProjUpperShriekIso f j D) ≪≫
    ((upperShriekProperIso (diagHom f D)).app _).symm ≪≫
    diagUpperShriekSndRestrictIso f j D

end Stacks.Duality

end
