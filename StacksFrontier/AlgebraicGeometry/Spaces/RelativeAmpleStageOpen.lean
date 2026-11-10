module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleStagePullback

/-!
# The open neighbourhood of claim (A) of Stacks 0D3D, read off a stage

The last step of the proof of claim (A) of Stacks 0D3D: let `f' : X' ⟶ h_U` and
`fᵢ : Xᵢ ⟶ h_T` be morphisms of algebraic spaces to schemes of the site, with a commutative
square `b ≫ fᵢ = f' ≫ h_a` whose horizontal morphisms `a : U ⟶ T` and `b : X' ⟶ Xᵢ` are affine
(as are the projections from a limit with affine transition morphisms to a stage). If an
invertible `𝒪_{Xᵢ}`-module `Lᵢ` is ample on the base change of `fᵢ` to an open `Vᵢ` of `T`, then
`b^* Lᵢ` is ample on the base change of `f'` to the preimage `a⁻¹ Vᵢ` ("letting `V ⊂ Y` be the
inverse image of `Vᵢ` finishes the proof").

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_preimage_open_of_stage`: the statement above.
* `AlgebraicGeometry.Space.exists_open_isRelativelyAmple_of_stage`: claim (A) over `U` at a point
  `u`, from ampleness of `Lᵢ` on the base change of `fᵢ` along `Spec κ(u) ⟶ U ⟶ T` and Stacks 0D3A
  for `fᵢ`; the field reduction is the fpqc case of Stacks 0D3C.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Ampleness over the preimage of an open of a stage.** -/
theorem isRelativelyAmple_preimage_open_of_stage {U T : BigFppfOver B S hS}
    {X' Xᵢ : AlgebraicSpaces B S hS} {f' : X' ⟶ representedAlgebraicSpace B S hS U}
    {fᵢ : Xᵢ ⟶ representedAlgebraicSpace B S hS T} {a : U ⟶ T} {b : X' ⟶ Xᵢ}
    (hw : b ≫ fᵢ = f' ≫ ObjectProperty.homMk (yoneda.map a))
    (ha : IsAffineHom B S hS (yoneda.map a)) (hb : IsAffineHom B S hS b.hom)
    (Lᵢ : Modules.{u, u} B S hS Xᵢ.1 Xᵢ.2)
    (hLᵢ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Xᵢ.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Xᵢ.1 Xᵢ.2).O)).property Lᵢ)
    {L' : Modules.{u, u} B S hS X'.1 X'.2} (e : L' ≅ (modulePullback B S hS b).obj Lᵢ)
    (Vᵢ : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hVᵢ : ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ Xᵢ)
      (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub T Vᵢ)),
      IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T Vᵢ))) →
      IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj Lᵢ)) :
    ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
      (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS
        (openSub U ((BigFppfOver.toScheme B S hS).map a ⁻¹ᵁ Vᵢ))),
      IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map
        (openSubHom U ((BigFppfOver.toScheme B S hS).map a ⁻¹ᵁ Vᵢ)))) →
      IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L') := by
  intro X₁ p₁ f₁ hsq₁
  let aₛ : representedAlgebraicSpace B S hS U ⟶ representedAlgebraicSpace B S hS T :=
    ObjectProperty.homMk (yoneda.map a)
  -- ampleness over the open subspace of the stage, and over its preimage
  have hZ := AlgebraicSpaces.isPullback_fiberProduct B S hS fᵢ aₛ
  have hover := isRelativelyAmpleOver_preimage_of_isAffineHom_lift hw hZ
    (isAffineHom_lift_of_isAffineHom hw hZ hb ha) Lᵢ hLᵢ e
    (isRelativelyAmpleOver_range_openSubHom fᵢ Lᵢ Vᵢ hVᵢ)
  -- the open subobject of `U` maps into the preimage
  let V := (BigFppfOver.toScheme B S hS).map a ⁻¹ᵁ Vᵢ
  have hmem : ∀ y, (BigFppfOver.toScheme B S hS).map (openSubHom U V ≫ a) y ∈ Vᵢ := by
    intro y
    rw [Functor.map_comp, toScheme_map_openSubHom]
    exact y.2
  have hle : Subfunctor.range (yoneda.map (openSubHom U V)) ≤
      (Subfunctor.range (yoneda.map (openSubHom T Vᵢ))).preimage aₛ.hom := by
    rintro Z _ ⟨x, rfl⟩
    refine ⟨x ≫ openSubLift T Vᵢ (openSubHom U V ≫ a) hmem, ?_⟩
    change (x ≫ openSubLift T Vᵢ (openSubHom U V ≫ a) hmem) ≫ openSubHom T Vᵢ =
      (x ≫ openSubHom U V) ≫ a
    rw [Category.assoc, openSubLift_comp_openSubHom, Category.assoc]
  exact hover _ p₁ f₁ hsq₁ ⟨Subfunctor.lift (yoneda.map (openSubHom U V)) hle,
    Subfunctor.lift_ι _ _⟩

/-- The field-valued point `Spec κ(u) ⟶ U ⟶ T` of a scheme `T` of the site, for a point `u` of
`U` and a morphism `a : U ⟶ T`. -/
def residueFieldPointAlong {U T : BigFppfOver B S hS} (a : U ⟶ T)
    (u : (BigFppfOver.toScheme B S hS).obj U) : FieldValuedPoint B S hS (yoneda.obj T) :=
  ⟨U.left.1.residueField u, B.residueField_spec_contains U.left.property u,
    U.left.1.fromSpecResidueField u ≫ U.hom.1,
    residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u) ≫ a⟩

/-- The point of `T` underlying the field-valued point `residueFieldPointAlong a u` is the image
`a(u)` of `u`. -/
theorem schemePoint_residueFieldPointAlong {U T : BigFppfOver B S hS} (a : U ⟶ T)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    schemePoint B S hS T (residueFieldPointAlong a u) = (BigFppfOver.toScheme B S hS).map a u := by
  change (BigFppfOver.toScheme B S hS).map (residueFieldMap B S hS U u _ ≫ a) _ = _
  rw [Functor.map_comp]
  exact congrArg _ (Scheme.fromSpecResidueField_apply _ _)

/-- **Claim (A) of Stacks 0D3D over `U`, from a stage.** Let `b ≫ fᵢ = f' ≫ h_a` with `a : U ⟶ T`
and `b : X' ⟶ Xᵢ` affine and `L' ≅ b^* Lᵢ`, `Lᵢ` invertible. Suppose that `Lᵢ` is ample on the
base change of `fᵢ` along `Spec κ(u) ⟶ U ⟶ T`, and that Stacks 0D3A holds for `fᵢ` and `Lᵢ` at
every point of `T`. Then `L'` is ample on the base change of `f'` to an open neighbourhood of
`u`.

The field reduction of Stacks 0D3C (`isRelativelyAmple_residueField_of_fieldValuedPoint`) gives
ampleness at the residue field of `a(u)`, Stacks 0D3A an open `Vᵢ ∋ a(u)` of `T`, and
`isRelativelyAmple_preimage_open_of_stage` the open `a⁻¹ Vᵢ` of `U`. -/
theorem exists_open_isRelativelyAmple_of_stage (hdesc : RelativeAmpleFpqcDescends B S hS)
    {U T : BigFppfOver B S hS}
    {X' Xᵢ : AlgebraicSpaces B S hS} {f' : X' ⟶ representedAlgebraicSpace B S hS U}
    {fᵢ : Xᵢ ⟶ representedAlgebraicSpace B S hS T} {a : U ⟶ T} {b : X' ⟶ Xᵢ}
    (hw : b ≫ fᵢ = f' ≫ ObjectProperty.homMk (yoneda.map a))
    (ha : IsAffineHom B S hS (yoneda.map a)) (hb : IsAffineHom B S hS b.hom)
    (Lᵢ : Modules.{u, u} B S hS Xᵢ.1 Xᵢ.2)
    (hLᵢ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Xᵢ.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Xᵢ.1 Xᵢ.2).O)).property Lᵢ)
    {L' : Modules.{u, u} B S hS X'.1 X'.2} (e : L' ≅ (modulePullback B S hS b).obj Lᵢ)
    (u : (BigFppfOver.toScheme B S hS).obj U)
    (hfib : ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ Xᵢ)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS
        (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))),
      IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
        (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u) ≫ a))) →
      IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj Lᵢ))
    (h0D3A : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
      (∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ Xᵢ)
        (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS
          (residueFieldObject B S hS T y (B.residueField_spec_contains T.left.property y))),
        IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
          (residueFieldMap B S hS T y (B.residueField_spec_contains T.left.property y)))) →
        IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj Lᵢ)) →
      ∃ V : ((BigFppfOver.toScheme B S hS).obj T).Opens, y ∈ V ∧
        ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ Xᵢ)
          (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub T V)),
          IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
          IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj Lᵢ)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj U).Opens, u ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub U V)),
        IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map (openSubHom U V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L') := by
  let r := residueFieldPointAlong a u
  -- ampleness over `Spec κ(u)`, on the chosen base change
  let gW : representedAlgebraicSpace B S hS
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u)) ⟶
      representedAlgebraicSpace B S hS T :=
    ObjectProperty.homMk (yoneda.map
      (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u) ≫ a))
  have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS fᵢ gW
  have hg : (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ 𝟙 (yoneda.obj T)) :
      representedAlgebraicSpace B S hS r.siteObject ⟶ representedAlgebraicSpace B S hS T) = gW := by
    ext1
    rw [ObjectProperty.homMk_hom, Category.comp_id]
    rfl
  -- ampleness at the residue field of `a(u)`
  have hsq' : IsPullback (ObjectProperty.homMk (pullback.fst fᵢ.hom gW.hom))
      (ObjectProperty.homMk (pullback.snd fᵢ.hom gW.hom) :
        AlgebraicSpaces.fiberProduct B S hS fᵢ gW ⟶
          representedAlgebraicSpace B S hS r.siteObject) fᵢ
      (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ 𝟙 (yoneda.obj T)) :
        representedAlgebraicSpace B S hS r.siteObject ⟶ representedAlgebraicSpace B S hS T) := by
    rwa [hg]
  obtain ⟨V, hyV, hV⟩ := h0D3A (schemePoint B S hS T r)
    fun X₀ p₀ f₀ h₀ => isRelativelyAmple_residueField_of_fieldValuedPoint fᵢ Lᵢ hdesc hLᵢ T
      (𝟙 _) r _ _ hsq' (hfib _ _ hsq) (X' := X₀) p₀ f₀ (by rwa [Category.comp_id])
  refine ⟨(BigFppfOver.toScheme B S hS).map a ⁻¹ᵁ V, ?_,
    isRelativelyAmple_preimage_open_of_stage hw ha hb Lᵢ hLᵢ e V hV⟩
  change (BigFppfOver.toScheme B S hS).map a u ∈ V
  rw [← schemePoint_residueFieldPointAlong]
  exact hyV

end AlgebraicGeometry.Space

end
