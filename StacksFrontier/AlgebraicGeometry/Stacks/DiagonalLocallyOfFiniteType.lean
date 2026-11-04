module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre

/-!
# The diagonal of a limit preserving category fibred in groupoids is locally of finite type

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` whose diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. If `𝒳` is limit preserving then `Δ` is
locally of finite type.

## Main results

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.exists_restrict_eq_of_descentHom`: a
  vertical morphism over the vertex of a cone is the restriction of one at a stage, as soon as
  vertical morphisms descend.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal`: **Stacks 0CXI**.

## Implementation notes

The base change of `Δ` along a scheme-valued point `(x₁, x₂)` of `𝒳 × 𝒳` over a scheme `U` is the
presheaf of vertical morphisms `x₁ ⟶ x₂`, by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`; so a section of the algebraic
space representing it over an object `T` of the big fppf site of `U` is a vertical morphism
`x₁|_T ⟶ x₂|_T`, and a section coming from a stage of an inverse system is such a morphism
defined at that stage.

That reduces local finite presentation of the representing space over `U` to the surjectivity
criterion of Stacks 0CM6, whose hypothesis asks exactly that every vertical morphism over an
affine inverse limit descend to a stage. For a limit preserving `𝒳` that is the fullness half of
the equivalence of Stacks 07XL, in the shape `Deformation.Artin.DescentHom`. Local finite type
then follows by Stacks 0464, and the passage between the property of the representing space read
over `U` and read over `S` is Stacks 04SG, in the form
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`.

Running the criterion over `U` rather than over `S` is what makes the argument independent of
Stacks 07XN: the inverse systems tested are systems of affine schemes over `U`, which are systems
over `S` through `CategoryTheory.Over.map`, so the limit preservation of `𝒳` applies to them
directly and the structure morphism of the representing space never has to be compared with `S`.
The affine hypotheses of Stacks 07WI are therefore not used in the local step, only its reduction
of the relative property to affine bases.

*The index system.* The diagram of affine objects over `U` is pushed to one over `S` by
`CategoryTheory.ObjectProperty.lift` into the affine full subcategory; the lift composed with the
inclusion is the original diagram definitionally, and the forgetful functor to schemes does not
see the change of base, so the limiting cone and the affineness hypotheses transfer unchanged.

*The target of the criterion.* The structure morphism used is the one to the terminal object of
the big fppf site of `U`, whose presheaf of sections is pointwise a subsingleton; the colimit of
the sections over the stages of a filtered system is then a subsingleton too, so the component of
the criterion's conclusion which concerns the target holds for every element.

## References

* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
* [Stacks Project, Tag 07WI](https://stacks.math.columbia.edu/tag/07WI)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

universe u₁ v₁ u₂ v₂ u₃ v₃ vI wI

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y₁ Y₂ : 𝒯 ⥤ X}

/-- Two morphisms into the source of a strongly cartesian morphism which lie over one and the
same morphism of the base and become equal after composition with it are equal. -/
private theorem eq_of_comp_isStronglyCartesian {W W' W'' : 𝒞} {a b a' : X} {f : W ⟶ W'}
    {φ : a ⟶ b} (hφ : p.IsStronglyCartesian f φ) {g : W'' ⟶ W} {ψ ψ' : a' ⟶ a}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  have := hφ
  have := hψ
  have := hψ'
  exact Functor.IsStronglyCartesian.ext p f φ g h

/-- **A vertical morphism over the vertex of a cone descends to a stage.** If vertical morphisms
between pullbacks of stage objects come from a stage, then every vertical morphism between the
two components over the vertex is the restriction of a vertical morphism between the components
at some stage.

This is the surjectivity of the comparison from the colimit of the presheaves of vertical
morphisms over the stages, written without colimits. -/
theorem exists_restrict_eq_of_descentHom (hp : p.IsFiberedInGroupoids)
    (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯)
    {I : Type vI} [Category.{wI} I] [Nonempty I] (D : I ⥤ 𝒯) (c : Cone D)
    (hdesc : Deformation.Artin.DescentHom p (D ⋙ p𝒯) (p𝒯.mapCone c))
    (φ : VertHom p p𝒯 Y₁ Y₂ c.pt) :
    ∃ (k : I) (χ : VertHom p p𝒯 Y₁ Y₂ (D.obj k)),
      restrict hp h₁ h₂ (c.π.app k) χ = φ := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := inferInstance
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, hdx, hdy, hδk, hψ, e1, e2⟩ :=
    hdesc i₀ ⟨Y₁.obj (D.obj i₀), Functor.congr_obj h₁ (D.obj i₀)⟩
      ⟨Y₂.obj (D.obj i₀), Functor.congr_obj h₂ (D.obj i₀)⟩
      ⟨Y₁.obj c.pt, Functor.congr_obj h₁ c.pt⟩ ⟨Y₂.obj c.pt, Functor.congr_obj h₂ c.pt⟩
      (Y₁.map (c.π.app i₀)) (Y₂.map (c.π.app i₀))
      (isHomLift_map h₁ (c.π.app i₀)) (isHomLift_map h₂ (c.π.app i₀)) φ.1 φ.2
  have hdxc : p.IsStronglyCartesian ((D ⋙ p𝒯).map s) dx := by
    have := hdx
    exact hp.isStronglyCartesian_homLift _ _
  have hY1s : p.IsHomLift ((D ⋙ p𝒯).map s) (Y₁.map (D.map s)) := isHomLift_map h₁ (D.map s)
  have hY2s : p.IsHomLift ((D ⋙ p𝒯).map s) (Y₂.map (D.map s)) := isHomLift_map h₂ (D.map s)
  have hY2sc : p.IsStronglyCartesian ((D ⋙ p𝒯).map s) (Y₂.map (D.map s)) := by
    have := hY2s
    exact hp.isStronglyCartesian_homLift _ _
  have := hdxc
  have := hY1s
  have := hY2s
  have := hY2sc
  have := hdy
  have := hψ
  -- the comparison of the first components at the stage `k`
  set u := Functor.IsStronglyCartesian.map p ((D ⋙ p𝒯).map s) dx
    (Category.id_comp ((D ⋙ p𝒯).map s)).symm (Y₁.map (D.map s)) with hudef
  have hufac : u ≫ dx = Y₁.map (D.map s) :=
    Functor.IsStronglyCartesian.fac p ((D ⋙ p𝒯).map s) dx
      (Category.id_comp ((D ⋙ p𝒯).map s)).symm (Y₁.map (D.map s))
  have hu : p.IsHomLift (𝟙 ((D ⋙ p𝒯).obj k)) u := by rw [hudef]; infer_instance
  -- the comparison of the second components at the stage `k`
  set v := Functor.IsStronglyCartesian.map p ((D ⋙ p𝒯).map s) (Y₂.map (D.map s))
    (Category.id_comp ((D ⋙ p𝒯).map s)).symm dy with hvdef
  have hvfac : v ≫ Y₂.map (D.map s) = dy :=
    Functor.IsStronglyCartesian.fac p ((D ⋙ p𝒯).map s) (Y₂.map (D.map s))
      (Category.id_comp ((D ⋙ p𝒯).map s)).symm dy
  have hv : p.IsHomLift (𝟙 ((D ⋙ p𝒯).obj k)) v := by rw [hvdef]; infer_instance
  have := hu
  have := hv
  -- the descended vertical morphism
  have hχ : p.IsHomLift (𝟙 ((D ⋙ p𝒯).obj k)) (u ≫ ψ ≫ v) := by
    have h : p.IsHomLift (𝟙 ((D ⋙ p𝒯).obj k) ≫ 𝟙 ((D ⋙ p𝒯).obj k) ≫
        𝟙 ((D ⋙ p𝒯).obj k)) (u ≫ ψ ≫ v) := inferInstance
    simpa using h
  -- the first comparison identifies the two descents of the first component
  have hA : Y₁.map (c.π.app k) ≫ u = δk := by
    refine eq_of_comp_isStronglyCartesian hdxc (g := p𝒯.map (c.π.app k)) ?_ hδk ?_
    · have h1 : p.IsHomLift (p𝒯.map (c.π.app k)) (Y₁.map (c.π.app k)) := isHomLift_map h₁ _
      have := h1
      have h : p.IsHomLift (p𝒯.map (c.π.app k) ≫ 𝟙 ((D ⋙ p𝒯).obj k))
        (Y₁.map (c.π.app k) ≫ u) := inferInstance
      simpa using h
    · rw [Category.assoc, hufac, ← Functor.map_comp, c.w s]
      exact e1.symm
  refine ⟨k, ⟨u ≫ ψ ≫ v, hχ⟩, (restrict_uniq hp h₁ h₂ (c.π.app k) ⟨u ≫ ψ ≫ v, hχ⟩ φ ?_).symm⟩
  refine eq_of_comp_isStronglyCartesian hY2sc (g := p𝒯.map (c.π.app k)) ?_ ?_ ?_
  · have h1 : p.IsHomLift (p𝒯.map (c.π.app k)) (Y₂.map (c.π.app k)) := isHomLift_map h₂ _
    have := h1
    have := φ.2
    have h : p.IsHomLift (𝟙 (p𝒯.obj c.pt) ≫ p𝒯.map (c.π.app k)) (φ.1 ≫ Y₂.map (c.π.app k)) :=
      inferInstance
    simpa using h
  · have h1 : p.IsHomLift (p𝒯.map (c.π.app k)) (Y₁.map (c.π.app k)) := isHomLift_map h₁ _
    have := h1
    have := hχ
    have h : p.IsHomLift (p𝒯.map (c.π.app k) ≫ 𝟙 ((D ⋙ p𝒯).obj k))
      (Y₁.map (c.π.app k) ≫ u ≫ ψ ≫ v) := inferInstance
    simpa using h
  · calc (φ.1 ≫ Y₂.map (c.π.app k)) ≫ Y₂.map (D.map s)
        = φ.1 ≫ Y₂.map (c.π.app i₀) := by
          rw [Category.assoc, ← Functor.map_comp, c.w s]
      _ = δk ≫ ψ ≫ dy := e2.symm
      _ = (Y₁.map (c.π.app k) ≫ u) ≫ ψ ≫ dy := by rw [hA]
      _ = (Y₁.map (c.π.app k) ≫ u ≫ ψ ≫ v) ≫ Y₂.map (D.map s) := by
          rw [← hvfac]; simp only [Category.assoc]

end CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

namespace AlgebraicGeometry.Space

universe u v

/-- **Stacks 041S at the fppf precoverage.** Being locally of finite type, as a property of
morphisms of algebraic spaces over `S`, is local on the target for the fppf precoverage.

The relative properties of Stacks 03YK are stated at the fppf precoverage and take locality at
the target as an instance argument, so this is what instance search needs in order to state them
for this property; the content is the fpqc statement
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc`. -/
instance locallyOfFiniteTypeProperty_isLocalAtTarget_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  (isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, v} B S hS).of_le
    (fppfPrecoverage_le_fpqcPrecoverage.{u, v} B S hS)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u v w

/-- A filtered colimit of subsingletons is a subsingleton. -/
private theorem subsingleton_colimit {J : Type v} [Category.{w} J] [IsFiltered J]
    (G : J ⥤ Type u) [HasColimit G] (hG : ∀ j, Subsingleton (G.obj j)) :
    Subsingleton (colimit G) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' a
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' b
  rw [← colimit.w_apply (F := G) (IsFiltered.leftToMax i j) x,
    ← colimit.w_apply (F := G) (IsFiltered.rightToMax i j) y,
    (hG (IsFiltered.max i j)).elim (G.map (IsFiltered.leftToMax i j) x)
      (G.map (IsFiltered.rightToMax i j) y)]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Stacks 0CXI.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme
`S` whose diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. If `𝒳` is limit
preserving then `Δ` is locally of finite type.

The base change of `Δ` along a scheme-valued point of `𝒳 × 𝒳` over `U` is the presheaf of
vertical morphisms between the two components of that point, so a section of the representing
algebraic space over an affine inverse limit is a vertical morphism there, and limit preservation
of `𝒳` makes it the restriction of one at a finite stage. The surjectivity criterion of Stacks
0CM6 turns that into local finite presentation of the representing space over `U`, and Stacks
0464 into local finite type. -/
@[stacks 0CXI]
theorem isLocallyOfFiniteType_diagonal
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (diagonal.{u, u, u + 1} B S hS 𝒳).hom)
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.locallyOfFiniteTypeProperty B S hS)
      (diagonal.{u, u, u + 1} B S hS 𝒳) hΔ := by
  classical
  refine hasRelativeProperty_of_affine_locallyOfFinitePresentation B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) (diagonal.{u, u, u + 1} B S hS 𝒳) hΔ
    (isLimitPreservingOnObjects_toTerminalCFG_product B S hS 𝒳 h𝒳) ?_
  intro U _hUaff _hUlfp y hy F hF ⟨eF⟩
  -- the property of the representing space does not depend on the base
  have hri : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  rw [prop_algebraicSpaceMap_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS) U F hF]
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) F).mpr ?_
  refine Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B U.left.1 U.left.2 ?_
  refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B U.left.1 U.left.2 hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  intro I _ _ D c hc hDaff hcaff x yy _hxy
  have : Nonempty I := IsCofiltered.nonempty
  -- the representing space is the presheaf of vertical morphisms
  have hp := 𝒳.isFiberedInGroupoids
  have hfib : 𝒳.val.p.IsFibered := hp.isFibered
  obtain ⟨e⟩ :=
    (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp hy F).mp ⟨eF⟩
  let pe := PresheafOfCategories.PointwiseEquiv.ofUliftIso e
  -- the system of affine schemes over `U` as a system over `S`
  have haff : ∀ i, IsAffineOver B S hS ((D ⋙ Over.map U.hom).obj i) := fun i => hDaff i
  have hcaff' : IsAffineOver B S hS ((Over.map U.hom).obj c.pt) := hcaff
  set D' : I ⥤ BigAffineFppf B S hS :=
    (IsAffineOver B S hS).lift (D ⋙ Over.map U.hom) haff with hD'def
  set c' : Cone D' :=
    { pt := ⟨(Over.map U.hom).obj c.pt, hcaff'⟩
      π :=
        { app := fun i => ObjectProperty.homMk ((Over.map U.hom).map (c.π.app i))
          naturality := fun i j f => by
            apply ObjectProperty.hom_ext
            show 𝟙 _ ≫ (Over.map U.hom).map (c.π.app j) =
              (Over.map U.hom).map (c.π.app i) ≫ (Over.map U.hom).map (D.map f)
            rw [Category.id_comp, ← Functor.map_comp, c.w f] } } with hc'def
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
  -- limit preservation of `𝒳` gives descent of vertical morphisms
  have : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')).Full := (h𝒳 I D' c' hc').full
  have hdesc : Deformation.Artin.DescentHom 𝒳.val.p (D ⋙ Over.map U.hom)
      ((Over.map U.hom).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒳.val.p hp
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')
  -- descend the section
  obtain ⟨k, χ, hχ⟩ :=
    TwoFibreProductOver.DiagonalFibre.VertHom.exists_restrict_eq_of_descentHom hp
      (TwoFibreProductOver.DiagonalFibre.h1' hy) (TwoFibreProductOver.DiagonalFibre.h2' hy)
      D c hdesc ((pe.equiv (op c.pt)).symm x)
  refine ⟨colimit.ι (D.op ⋙ F) (op k) (pe.equiv (op (D.obj k)) χ), ?_, ?_⟩
  · rw [colimit.ι_desc_apply]
    refine Eq.trans ?_ ((pe.equiv (op c.pt)).apply_symm_apply x)
    rw [← hχ, ← TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_map]
    exact (pe.naturality (c.π.app k).op χ).symm
  · have : Subsingleton (colimit (D.op ⋙ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) := by
      refine subsingleton_colimit _ (fun j => ?_)
      exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩
    exact this.elim _ _

end AlgebraicGeometry.Stack

end
