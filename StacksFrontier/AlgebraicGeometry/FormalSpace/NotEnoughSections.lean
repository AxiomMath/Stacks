module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NotMcQuillanExample
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsRepresentable

/-!
# The structure sheaf of a formal algebraic space need not have enough sections

Stacks 0DEK observes that the structure sheaf of a formal algebraic space does not always have
"enough sections": there are affine formal algebraic spaces which are not McQuillan, and there
are even ones whose points are not separated by regular functions. Both phenomena occur in the
single example of Stacks 0CBD, `X = colim Spec(A_s)` over a field of characteristic zero: its
ring of regular functions `lim Γ(X_λ, O_{X_λ})` is a field, while its reduction has
infinitely many points.

## Main results

* `AlgebraicGeometry.FormalSpace.not_hasSomeSurjectivePresentation_of_isField_of_infinite`:
  an affine formal algebraic space with a presentation whose section limit is a field and one of
  whose stages has infinitely many points is not McQuillan.
* `AlgebraicGeometry.FormalSpace.pointsULiftEquivStage`: the points of an affine formal
  algebraic space are the points of any stage of a presentation by affine thickenings.
* `AlgebraicGeometry.FormalSpace.exists_isAffineFormalAlgebraicSpace_not_enough_sections`:
  there is an affine formal algebraic space which is not McQuillan and whose points are not
  separated by regular functions.

## Implementation notes

The regular functions of `X` are the elements of the inverse limit of the rings of global
sections of the stages of a presentation `X = colim X_λ` by affine thickenings, as in the rule
defining `O_X(U_red) = lim Γ(U_λ, O_{U_λ})` before Stacks 0DEJ; this limit does not depend on the
presentation (`AlgebraicGeometry.FormalSpace.sectionsRingEquivOfPresentations`). A regular
function `f` is evaluated at a point `x` of a stage `X_λ` through its component in
`Γ(X_λ, O_{X_λ})`, and it vanishes at `x` exactly when `x` lies outside the basic open of that
component. As every stage is a thickening of the reduction, the points of the stages are the
points of `X`. When the limit is a field every regular function is zero or a unit, so each one
vanishes either at every point or at none, and no regular function separates any two points.

## References

* [Stacks Project, Tag 0DEK](https://stacks.math.columbia.edu/tag/0DEK)
* [Stacks Project, Tag 0CBC](https://stacks.math.columbia.edu/tag/0CBC)
* [Stacks Project, Tag 0CBD](https://stacks.math.columbia.edu/tag/0CBD)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projection from the inverse limit of the section rings of an affine presentation to the
ring of global sections of one stage, as a ring homomorphism. -/
noncomputable def sectionsProjection {I : Type (u + 1)} [Category I]
    (D : I ⥤ BigAffineFppf B S hS) (i : I) :
    (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections →+*
      Γ((BigAffineFppf.toScheme B S hS).obj (D.obj i), ⊤) :=
  (Pi.evalRingHom (fun j ↦ ((sectionDiagram B S hS D).obj j : Type u)) (op i)).comp
    (RingCat.sectionsSubring (sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u})).subtype

/-- The projection `sectionsProjection B S hS D i` sends an element of the inverse limit to its
component at the stage `i`. -/
@[simp]
theorem sectionsProjection_apply {I : Type (u + 1)} [Category I]
    (D : I ⥤ BigAffineFppf B S hS) (i : I)
    (f : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections) :
    sectionsProjection B S hS D i f = f.1 (op i) := rfl

/-- If the inverse limit of the section rings of an affine presentation is a field, then no
element of it separates two points of a stage: the component of each element at a stage either
vanishes at every point of the stage or at none. -/
theorem mem_basicOpen_iff_of_isField {I : Type (u + 1)} [Category I]
    (D : I ⥤ BigAffineFppf B S hS)
    (hfield : IsField (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections)
    (f : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections) (i : I)
    (x y : (BigAffineFppf.toScheme B S hS).obj (D.obj i)) :
    x ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen (f.1 (op i)) ↔
      y ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen (f.1 (op i)) := by
  change x ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen
      (sectionsProjection B S hS D i f) ↔
    y ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen
      (sectionsProjection B S hS D i f)
  by_cases hf : f = 0
  · rw [hf, map_zero, Scheme.basicOpen_zero]
    simp
  · obtain ⟨g, hg⟩ := hfield.mul_inv_cancel hf
    have hu : IsUnit (sectionsProjection B S hS D i f) :=
      (Units.mkOfMulEqOne f g hg).isUnit.map _
    rw [Scheme.basicOpen_of_isUnit _ hu]
    simp

/-- If the inverse limit of the section rings of one presentation of `X` by affine thickenings is
a field, then so is the one of any other such presentation. -/
private theorem isField_sections_of_presentations (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hfield : IsField (sectionDiagram B S hS D₀ ⋙ forget CommRingCat.{u}).sections)
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    IsField (sectionDiagram B S hS D₁ ⋙ forget CommRingCat.{u}).sections :=
  MulEquiv.isField hfield
    (sectionsRingEquivOfPresentations B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁).symm.toMulEquiv

/-- An affine formal algebraic space is not McQuillan, i.e. fails condition (4) of Stacks 0AIC,
as soon as it has a presentation by affine thickenings whose inverse limit of section rings is
a field and one of whose stages has infinitely many points: a stage of any competing
presentation receives a thickening from that infinite stage, while a surjection out of a field
leaves it at most one point. -/
theorem not_hasSomeSurjectivePresentation_of_isField_of_infinite (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hfield : IsField (sectionDiagram B S hS D₀ ⋙ forget CommRingCat.{u}).sections)
    (i₀ : I₀) [Infinite ((BigAffineFppf.toScheme B S hS).obj (D₀.obj i₀))] :
    ¬ HasSomeSurjectivePresentation B S hS X := by
  classical
  rintro ⟨-, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨e₁⟩, hsurj⟩
  let : Preorder I₁ := pre₁
  have : Nonempty I₁ := hne₁
  have : IsDirected I₁ (· ≤ ·) := hdir₁
  have hfield₁ := isField_sections_of_presentations B S hS X I₀ D₀ hD₀ e₀ hfield I₁ D₁ hD₁ e₁
  obtain ⟨k, g, hg⟩ := exists_factor_to_affine_stage B S hS X I₁ D₁ hD₁ e₁ (D₀.obj i₀)
    (colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i₀ ≫ e₀.inv)
  have hthick : Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map g) :=
    isThickening_of_factor_stage B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁ i₀ k g hg
  have : Infinite ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k)) :=
    Infinite.of_injective (Stacks.Thickenings.IsThickening.homeomorph hthick)
      (Stacks.Thickenings.IsThickening.homeomorph hthick).injective
  let : Field (sectionDiagram B S hS D₁ ⋙ forget CommRingCat.{u}).sections := hfield₁.toField
  have hπ : Function.Surjective (sectionsProjection B S hS D₁ k) := fun y ↦
    (hsurj k y).imp fun _ h ↦ h
  have hsub : Subsingleton
      (PrimeSpectrum Γ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k), ⊤)) :=
    (PrimeSpectrum.comap_injective_of_surjective _ hπ).subsingleton
  have : Subsingleton (Spec Γ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k), ⊤)) := hsub
  have hspace : Subsingleton ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k) : Type u) :=
    (Scheme.homeoOfIso
      ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k)).isoSpec).injective.subsingleton
  exact not_subsingleton _ hspace

/-- The points of an affine formal algebraic space are the points of any stage of a presentation
by affine thickenings: the reduction of the stage is the reduction of the space, which has the
same points as the space, and the reduction of the stage is a thickening of the stage. -/
noncomputable def pointsULiftEquivStage (X : FppfSheaf B S hS)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X) (i : I) :
    Space.pointsULift.{u + 1} B S hS X.obj ≃ (BigAffineFppf.toScheme B S hS).obj (D.obj i) :=
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda JT
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  let ε : F ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  let α : (uliftYoneda.{u + 1}).obj Tred ≅ (F.obj Tred).obj := (ε.app Tred).symm
  let eα : Space.pointsULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj Tred) ≃
      Space.pointsULift.{u + 1} B S hS (F.obj Tred).obj :=
    { toFun := Space.pointsMapULift.{u + 1} B S hS _ α.hom
      invFun := Space.pointsMapULift.{u + 1} B S hS _ α.inv
      left_inv := fun x ↦ by
        change (Space.pointsMapULift.{u + 1} B S hS _ α.inv ∘
          Space.pointsMapULift.{u + 1} B S hS _ α.hom) x = x
        rw [← Space.pointsMapULift_comp, α.hom_inv_id, Space.pointsMapULift_id, id]
      right_inv := fun x ↦ by
        change (Space.pointsMapULift.{u + 1} B S hS _ α.hom ∘
          Space.pointsMapULift.{u + 1} B S hS _ α.inv) x = x
        rw [← Space.pointsMapULift_comp, α.inv_hom_id, Space.pointsMapULift_id, id] }
  let eRed := Equiv.ofBijective _
    (isReduction_siteReduction_stage B S hS D hD X e i).bijective_pointsMapULift
  eRed.symm.trans (eα.symm.trans ((Space.pointsEquivSchemeULift.{u + 1} B S hS Tred).trans
    (Stacks.Thickenings.IsThickening.homeomorph
      (isThickening_toScheme_map_siteReductionMap B S hS T₀)).toEquiv))

/-- The structure sheaf of a formal algebraic space does not always have enough sections. There
is an affine formal algebraic space `X` which is not McQuillan (it fails condition (4) of Stacks
0AIC) and whose points are not separated by regular functions, in the sense of Stacks 0CBD:
* for every presentation `X = colim X_λ` by affine thickenings as in Stacks 0AI7, the ring
  `lim Γ(X_λ, O_{X_λ})` of regular functions is a field, every stage `X_λ` has infinitely many
  points (they are the points of `X`, see
  `AlgebraicGeometry.FormalSpace.pointsULiftEquivStage`), and each regular function vanishes
  either at all points of a stage or at none, so it separates no two points;
* `X` has infinitely many points, and its reduction `X_red` is represented by a scheme of the
  site with infinitely many points. -/
@[stacks 0DEK]
theorem exists_isAffineFormalAlgebraicSpace_not_enough_sections :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧
      ¬ HasSomeSurjectivePresentation B S hS X ∧
      (∀ (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : I ⥤ BigAffineFppf B S hS),
        (∀ ⦃i j : I⦄ (f : i ⟶ j),
          Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f))) →
        Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) →
        IsField (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections ∧
        (∀ i : I, Infinite ((BigAffineFppf.toScheme B S hS).obj (D.obj i))) ∧
        ∀ (f : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections) (i : I)
          (x y : (BigAffineFppf.toScheme B S hS).obj (D.obj i)),
          x ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen (f.1 (op i)) ↔
            y ∈ ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).basicOpen (f.1 (op i))) ∧
      Infinite (Space.pointsULift.{u + 1} B S hS X.obj) ∧
      ∃ (T : BigFppfOver B S hS)
        (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
        IsReduction B S hS X ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T) ι ∧
        Infinite ((BigFppfOver.toScheme B S hS).obj T) := by
  classical
  obtain ⟨B, S, hS, X, hAff, I₀, pre₀, hne₀, hdir₀, D₀, hD₀, ⟨e₀⟩, hfield, i₀, hinf⟩ :=
    exists_isAffineFormalAlgebraicSpace_sections_isField_infinite_stage.{u}
  let : Preorder I₀ := pre₀
  have : Nonempty I₀ := hne₀
  have : IsDirected I₀ (· ≤ ·) := hdir₀
  have := hinf
  -- the regular functions form a field for every presentation
  have hfieldAll : ∀ (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : I ⥤ BigAffineFppf B S hS),
      (∀ ⦃i j : I⦄ (f : i ⟶ j),
        Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f))) →
      Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) →
      IsField (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections := by
    rintro I _ _ _ D hD ⟨e⟩
    exact isField_sections_of_presentations B S hS X I₀ D₀ hD₀ e₀ hfield I D hD e
  -- the reduction of the infinite stage is the reduction of `X`
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D₀.obj i₀)
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  have hTinf : Infinite ((BigFppfOver.toScheme B S hS).obj Tred) :=
    (Stacks.Thickenings.IsThickening.homeomorph
      (isThickening_toScheme_map_siteReductionMap B S hS T₀)).toEquiv.infinite_iff.mpr hinf
  -- the points of `X` are the points of the infinite stage
  have hXinf : Infinite (Space.pointsULift.{u + 1} B S hS X.obj) :=
    (pointsULiftEquivStage B S hS X D₀ hD₀ e₀.symm i₀).symm.infinite_iff.mp hinf
  refine ⟨B, S, hS, X, hAff,
    not_hasSomeSurjectivePresentation_of_isField_of_infinite B S hS X I₀ D₀ hD₀ e₀ hfield i₀,
    fun I _ _ _ D hD he ↦ ⟨hfieldAll I D hD he,
      fun i ↦ (pointsULiftEquivStage B S hS X D hD he.some.symm i).infinite_iff.mp hXinf,
      fun f i x y ↦ mem_basicOpen_iff_of_isField B S hS D (hfieldAll I D hD he) f i x y⟩,
    hXinf, Tred, _, isReduction_siteReduction_stage B S hS D₀ hD₀ X e₀.symm i₀, hTinf⟩

end AlgebraicGeometry.FormalSpace

end
