module

public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyAffine

/-!
# Affine schemes of finite presentation over a limit come from an affine stage

Let `X = lim Xᵢ` be a cofiltered limit of affine schemes with affine transition morphisms. An
affine scheme `N` of finite presentation over `X` is the base change of an *affine* scheme of
finite presentation over some stage: Stacks 01ZM part (1) gives a model of finite presentation,
and Stacks 09ZM makes it affine at a later stage, because the limit of the base changes of the
model is the affine `N`.

This is the form in which the proof of Stacks 0GI5 descends the affine charts of a witness and
the affine étale neighbourhoods of a point to a finite stage.

## Main results

* `AlgebraicGeometry.Scheme.exists_affine_model_of_isLimit`: the statement above.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]

include hc in
/-- **An affine scheme of finite presentation over a limit of affine schemes comes from an affine
scheme of finite presentation over a stage**, as the base change along the projection. -/
theorem exists_affine_model_of_isLimit {N : Scheme.{u}} [IsAffine N] (n : N ⟶ c.pt)
    [LocallyOfFinitePresentation n] :
    ∃ (i : I) (Ni : Scheme.{u}) (ni : Ni ⟶ D.obj i) (θ : N ⟶ Ni),
      IsAffine Ni ∧ LocallyOfFinitePresentation ni ∧ IsPullback θ n ni (c.π.app i) := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have hπ (i : I) : IsAffineHom (c.π.app i) := isAffineHom_π_app_of_initiallySmall D c hc i
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffine c.pt := by
    have := hπ i₀
    exact isAffine_of_isAffineHom (c.π.app i₀)
  have : QuasiCompact n := quasiCompact_of_compactSpace n
  have : QuasiSeparated n := QuasiSeparated.of_quasiSeparatedSpace n
  obtain ⟨i, Xi, hfp, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk n)
      ⟨inferInstanceAs (LocallyOfFinitePresentation n), inferInstanceAs (QuasiCompact n),
        inferInstanceAs (QuasiSeparated n)⟩
  have : LocallyOfFinitePresentation Xi.hom := hfp.1
  have : QuasiCompact Xi.hom := hfp.2.1
  have : QuasiSeparated Xi.hom := hfp.2.2
  -- the model, as a cartesian square
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have he : e.hom.left ≫ pullback.snd Xi.hom (c.π.app i) = n := Over.w e.hom
  have hbig : IsPullback (e.hom.left ≫ pullback.fst Xi.hom (c.π.app i)) n Xi.hom (c.π.app i) := by
    have h₀ := IsPullback.of_hasPullback Xi.hom (c.π.app i)
    refine IsPullback.of_iso h₀ (asIso e.hom.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ (by simp) (by simp)
    · simp
    · simp [← he]
  -- the base changes of the model to the later stages are eventually affine
  have hcX : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  have hqX : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  have hcomp (j : Over i) : CompactSpace ((baseChangeDiagram D i Xi).obj j) := by
    rw [baseChangeDiagram_obj]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) Xi.hom)
  have hqs (j : Over i) : QuasiSeparatedSpace ((baseChangeDiagram D i Xi).obj j) := by
    rw [baseChangeDiagram_obj]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) Xi.hom)
  have haff (j k : Over i) (g : j ⟶ k) : IsAffineHom ((baseChangeDiagram D i Xi).map g) :=
    isAffineHom_baseChangeDiagram_map D i Xi g
  have : IsAffine (pullback (c.π.app i) Xi.hom) :=
    IsAffine.of_isIso (Y := N) ((pullbackSymmetry _ _).hom ≫ inv e.hom.left)
  have hf : IsAffineHom (pullback.snd (c.π.app i) Xi.hom ≫ Xi.hom) := inferInstance
  have hft : (baseChangeCone D i Xi c).π ≫ baseChangeStructureMap D i Xi =
      (Functor.const (Over i)).map (pullback.snd (c.π.app i) Xi.hom ≫ Xi.hom) := by
    ext j
    simp only [NatTrans.comp_app, baseChangeStructureMap_app, Functor.const_map_app]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ Xi.hom) (baseChangeCone_π_snd D i Xi c j))
  have : EssentiallySmall.{u} (Over i) := essentiallySmall_over (I := I) i
  obtain ⟨j, hj⟩ := @eventually_isAffineHom_of_isLimit_of_essentiallySmall (Over i) _ _ _
    (D.obj i) _ _ (baseChangeDiagram D i Xi) (baseChangeStructureMap D i Xi)
    (baseChangeCone D i Xi c) (isLimitBaseChangeCone D i Xi c hc)
    (pullback.snd (c.π.app i) Xi.hom ≫ Xi.hom) hft hcomp hqs (fun {j k} g => haff j k g) hf
  have hj' : IsAffineHom (pullback.snd (D.map j.hom) Xi.hom ≫ Xi.hom) := by
    simpa using hj (𝟙 j)
  have : IsAffine (pullback (D.map j.hom) Xi.hom) := isAffine_of_isAffineHom
    (pullback.snd (D.map j.hom) Xi.hom ≫ Xi.hom)
  have hw : (n ≫ c.π.app j.left) ≫ D.map j.hom =
      (e.hom.left ≫ pullback.fst Xi.hom (c.π.app i)) ≫ Xi.hom := by
    rw [Category.assoc, c.w j.hom, hbig.w]
  refine ⟨j.left, pullback (D.map j.hom) Xi.hom, pullback.fst (D.map j.hom) Xi.hom,
    pullback.lift _ _ hw, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map j.hom) Xi.hom) (h₂₂ := D.map j.hom)
    ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback (D.map j.hom) Xi.hom).flip
  rw [pullback.lift_snd, c.w j.hom]
  exact hbig

end AlgebraicGeometry.Scheme

end
