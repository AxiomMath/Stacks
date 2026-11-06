module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional

/-!
# Algebraicity of the sheaf of glueing-data morphisms, from a size bound

In a formal glueing situation write `P = homPresheaf D G` for the sheaf of glueing-data
morphisms into a triple `G` with affine legs. Granted clause (1) of Stacks 0AF4 over affine
bases, `P` is affine over `X` in the sense of Stacks 03WF
(`AlgebraicGeometry.Space.FormalGlueingSituation.isAffineHom_homPresheafProjection`): its base
change to every affine object over `X` is an affine object. This module shows that `P` is an
algebraic space as soon as these affine base changes, taken over the affine opens of one
surjective étale chart `h_U ⟶ X`, have uniformly bounded size: the base change `P ×_X h_U` is
then glued from them into an object of the site (relative Stacks 03JH under a size bound,
`AlgebraicGeometry.Space.exists_representing_over_of_openCover_of_size_le`), and `P` receives
the representable, surjective, étale morphism `P ×_X h_U ⟶ P` (Stacks 0BGR).

The size bound cannot be dropped: the site is size-bounded, and an affine morphism to an affine
object can have a source of any size below the cutoff, so a family of affine pieces indexed by
the affine opens of `U` need not glue inside the site.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isAlgebraicSpace_homPresheaf_of_size_le`.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_FormalGlueingSpacesHomSheafAlgebraic
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-- The size condition on the affine base changes of the sheaf of glueing-data morphisms over a
chart `x : h_U ⟶ X`: one cardinal below the cutoff bounds every affine object representing the
base change of `P` to an affine open of `U`. -/
def HomPresheafSizeBound (D : FormalGlueingSituation B S hS) (G : glueingData D)
    {U : BigFppfOver B S hS} (x : yoneda.obj U ⟶ D.X) : Prop :=
  ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS) (v : V ⟶ U),
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    ∀ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ homPresheaf D G) (q : W ⟶ V),
      IsPullback p (yoneda.map q) (homPresheafProjection D G) (yoneda.map v ≫ x) →
      ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ

/-- **The sheaf of glueing-data morphisms is an algebraic space under a size bound**, granted
clause (1) of Stacks 0AF4 over affine bases: if over some surjective étale chart of `X` the
affine base changes of the sheaf are uniformly bounded in size, the sheaf is an algebraic
space. -/
theorem isAlgebraicSpace_homPresheaf_of_size_le (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) (G : glueingData D) (hG : affineLegs D G)
    {U : BigFppfOver B S hS} (x : yoneda.obj U ⟶ D.X)
    (hxs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf x)
    (hxe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf x)
    (hsize : HomPresheafSizeBound D G x) :
    IsAlgebraicSpace B S hS (homPresheaf D G) := by
  obtain ⟨μ, hμ, hbound⟩ := hsize
  let π := homPresheafProjection D G
  have hPs := isSheaf_homPresheaf D G
  have hFs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback π x) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj π x hPs D.algebraicSpace_X.isSheaf
  have hπ := isAffineHom_homPresheafProjection hA D G hG
  choose V u hu hurange hVaff using fun O => BigFppfOver.exists_affineOpen_restrict B S hS U O
  choose W p q hpb using fun O => hπ ⟨V O, hVaff O⟩ (yoneda.map (u O) ≫ x)
  let q' : ∀ O, yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (W O)) ⟶ pullback π x :=
    fun O => pullback.lift (p O) (yoneda.map (q O) ≫ yoneda.map (u O)) (by
      rw [(hpb O).w, Category.assoc])
  have hpb' : ∀ O, IsPullback (q' O) (yoneda.map (q O)) (pullback.snd π x) (yoneda.map (u O)) :=
    fun O => IsPullback.of_right (by rw [pullback.lift_fst]; exact hpb O)
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π x)
  have hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ O, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u O)) := by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨O, by rw [hurange O]; exact hO⟩
  obtain ⟨Y, e, P, -, -⟩ := exists_representing_over_of_openCover_of_size_le B S hS
    (Q := (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u}))
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine)
    hFs (pullback.snd π x)
    (u := u) (p := q) (q := q') hu hucov hpb' (fun O => by
      have := hVaff O
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (W O))) := (W O).property
      infer_instance) hμ
    (fun O => hbound (V O) (u O) (hu O) (hVaff O) _ (p O) (q O) (hpb O))
  have hbc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf x →
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst π x) :=
    fun P _ hx => by
      have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS P
      exact (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
        (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).of_isPullback
        (IsPullback.of_hasPullback π x).flip hx
  exact isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS
    ((isAlgebraicSpace_yoneda B S hS Y).of_iso e.symm) hPs (pullback.fst π x)
    (hbc _ hxs) (hbc _ hxe)

end AlgebraicGeometry.Space.FormalGlueingSituation

end
