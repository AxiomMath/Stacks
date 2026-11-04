module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Affineness of a representable morphism of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces. For an
affine scheme `T` of the site mapping to `Y`, the fibre product `X ×_Y T` is represented by an
affine scheme of the site, affine over `T`.

The file also proves that an algebraic space over `S` receiving a morphism which is surjective
on points from a quasi-compact algebraic space is quasi-compact, and that a sheaf which is an
algebraic space in the large value universe and receives a representable thickening from an
object of the site with compact underlying scheme has a quasi-compact model in the value universe
of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isAffineHom_isPullback_of_isRepresentable'`: for an
  affine test scheme `T`, the fibre product `X ×_Y T` is represented by an affine scheme of the
  site, affine over `T`.
* `AlgebraicGeometry.FormalSpace.exists_isAffineHom_isPullback_of_isRepresentable` and
  `AlgebraicGeometry.FormalSpace.exists_isAffineHom_isPullback_of_isRepresentable_of_isAffineBase`:
  the same, under a separatedness hypothesis on `Y`, respectively an affineness hypothesis on
  `S`.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_surjective_pointsMap`: an algebraic space
  receiving a morphism which is surjective on points from a quasi-compact algebraic space is
  quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_surjective_pointsMap_yoneda`: the same with
  the source represented by an object of the site whose underlying scheme is compact.
* `AlgebraicGeometry.Space.surjective_pointsMap_of_surjective_app_fieldSpec`:
  surjectivity on points from surjectivity on the sections over the spectra of fields.
* `AlgebraicGeometry.Space.exists_quasiCompact_model_of_relativeThickening`: a sheaf which is an
  algebraic space in the large value universe and receives a representable thickening from an
  object of the site with compact underlying scheme has a quasi-compact model in the value
  universe of the site.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` receiving a morphism surjective on points from a space with
compact point space is quasi-compact. -/
private theorem isQuasiCompactSpace_of_surjective_pointsMap_of_compactSpace
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hE : CompactSpace (points B S hS E)) (g : E ⟶ F)
    (hg : Function.Surjective (pointsMap B S hS E g)) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_of_compactSpace_points B S hS hF
    (@Function.Surjective.compactSpace _ _ _ _ _ (continuous_pointsMap B S hS g) hE hg)

/-- An algebraic space over `S` which receives a morphism surjective on points from a
quasi-compact algebraic space over `S` is quasi-compact. -/
theorem isQuasiCompactSpace_of_surjective_pointsMap
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hE : IsAlgebraicSpace B S hS E)
    (hEqc : IsQuasiCompactSpace B S hS E) (hF : IsAlgebraicSpace B S hS F) (g : E ⟶ F)
    (hg : Function.Surjective (pointsMap B S hS E g)) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_of_surjective_pointsMap_of_compactSpace B S hS hF
    (compactSpace_points_of_isQuasiCompactSpace B S hS hE hEqc) g hg

/-- An algebraic space over `S` which receives a morphism surjective on points from the
presheaf represented by an object of the site with compact underlying scheme is
quasi-compact. -/
theorem isQuasiCompactSpace_of_surjective_pointsMap_yoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (g : yoneda.obj W ⟶ F) (hg : Function.Surjective (pointsMap B S hS (yoneda.obj W) g)) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_of_surjective_pointsMap_of_compactSpace B S hS hF
    (@compactSpace_points_yoneda B S hS W hW) g hg

/-! ### Surjectivity on points from surjectivity on field-valued sections -/

/-- A morphism of presheaves of `Type u` which is surjective on the sections over the spectrum
of every field of the site is surjective on points. -/
theorem surjective_pointsMap_of_surjective_app_fieldSpec
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (hα : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S),
      Function.Surjective
        (α.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))))) :
    Function.Surjective (pointsMap B S hS F α) := by
  intro p
  induction p using Quot.ind with
  | _ p => ?_
  obtain ⟨x, hx⟩ := hα p.carrier p.contained p.toBase p.value
  refine ⟨Quot.mk _
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := x }, ?_⟩
  refine congrArg (Quot.mk (FieldValuedPoint.HasCommonExtension B S hS G)) ?_
  refine congrArg (fun v =>
    ({ carrier := p.carrier
       field := p.field
       contained := p.contained
       toBase := p.toBase
       value := v } : FieldValuedPoint B S hS G)) hx

/-! ### A quasi-compact model from a representable thickening -/

section Model

variable {B} {S} {hS}

/-- A sheaf is its own sheafification, the counit of the sheafification adjunction being an
isomorphism. -/
private noncomputable def sheafifyObjIsoSelf (Z : FormalSpace.FppfSheaf B S hS) :
    (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj Z.obj ≅ Z :=
  asIso ((sheafificationAdjunction (BigFppfOver.topology B S hS) (Type (u + 1))).counit.app Z)

/-- A sheaf which is an algebraic space in the large value universe and receives a representable
thickening from an object of the site with compact underlying scheme has a quasi-compact model in
the value universe of the site: an algebraic space `Z'` with values in `Type u` whose universe
lift sheafifies to `Z`. -/
theorem exists_quasiCompact_model_of_relativeThickening
    {Z : FormalSpace.FppfSheaf B S hS}
    (hZ : IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj)
    (V : BigFppfOver B S hS) (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ Z)
    (hι : (MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ι) :
    ∃ Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Z' ∧
      IsQuasiCompactSpace B S hS Z' ∧
      Nonempty ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (Z' ⋙ uliftFunctor.{u + 1}) ≅ Z) := by
  classical
  let topology := BigFppfOver.topology B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : topology.Subcanonical := inferInstance
  obtain ⟨Z', hZ'alg, ⟨eZ⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZ
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' topology
  let e₁ : uliftYoneda.{u + 1}.obj V ≅ ((Sheaf.sheafifiedYoneda topology).obj V).obj :=
    (sheafToPresheaf topology (Type (u + 1))).mapIso (eG.app V).symm
  let avatar : uliftYoneda.{u + 1}.obj V ⟶ Z' ⋙ uliftFunctor.{u + 1} :=
    e₁.hom ≫ ι.hom ≫ eZ.inv
  obtain ⟨ψ, hψ⟩ := Space.exists_whiskerRight_eq B S hS (F := yoneda.obj V) (G := Z') avatar
  have happ : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
      (b : Spec (.of K) ⟶ S), Function.Surjective
        (ψ.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS)))) := by
    intro K _ hK b
    have hbij : Function.Bijective
        (avatar.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS)))) := by
      have h₁ := ConcreteCategory.bijective_of_isIso
        (e₁.hom.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))))
      have h₃ := ConcreteCategory.bijective_of_isIso
        (eZ.inv.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))))
      have h₂ := FormalSpace.bijective_app_of_relativeThickening B S hS ι hι K hK b
      simp only [avatar, NatTrans.comp_app, types_comp]
      exact (h₃.comp h₂).comp h₁
    intro z
    obtain ⟨y, hy⟩ := hbij.2 ⟨z⟩
    refine ⟨y.down, ?_⟩
    have hval := congrArg
      (fun k : uliftYoneda.{u + 1}.obj V ⟶ Z' ⋙ uliftFunctor.{u + 1} =>
        k.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))) y) hψ
    exact congrArg ULift.down (hval.trans hy)
  refine ⟨Z', hZ'alg, isQuasiCompactSpace_of_surjective_pointsMap_yoneda B S hS hZ'alg V hV ψ
    (surjective_pointsMap_of_surjective_app_fieldSpec B S hS ψ happ), ?_⟩
  exact ⟨(presheafToSheaf topology (Type (u + 1))).mapIso eZ ≪≫ sheafifyObjIsoSelf Z⟩

end Model


end AlgebraicGeometry.Space


/-! ### Affineness of a representable morphism of affine formal algebraic spaces -/

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For `f : X ⟶ Y` a morphism of affine formal algebraic spaces over `S` representable by
algebraic spaces and `ξ : T ⟶ Y` a morphism from an affine scheme `T` over `S` in the site, the
fibre product `X ×_Y T` is represented by an affine scheme `W` of the site, and `W ⟶ T` is an
affine morphism. -/
theorem exists_isAffineHom_isPullback_of_isRepresentable'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ T)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
        IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f ξ := by
  obtain ⟨W, p, q, hpb, hW, hq⟩ :=
    exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf T hT ξ
  exact ⟨W, q, p, hW, hq, hpb⟩

/-- The statement of `exists_isAffineHom_isPullback_of_isRepresentable'`, with a separatedness
hypothesis on the target. -/
theorem exists_isAffineHom_isPullback_of_isRepresentable
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hYsep : FormalSpace.IsSeparated B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ T)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
        IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f ξ :=
  exists_isAffineHom_isPullback_of_isRepresentable' B S hS f hX hY hf T hT ξ

/-- The statement of `exists_isAffineHom_isPullback_of_isRepresentable'`, with an affineness
hypothesis on the base scheme `S`. -/
theorem exists_isAffineHom_isPullback_of_isRepresentable_of_isAffineBase
    (hSaff : IsAffine S) {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ T)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
        IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f ξ :=
  exists_isAffineHom_isPullback_of_isRepresentable' B S hS f hX hY hf T hT ξ


end AlgebraicGeometry.FormalSpace

end
