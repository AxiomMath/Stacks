module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalOfImmersionKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The conormal module of a section of a projective bundle, on an étale scheme point

Let `σ` be a section of the projective bundle `π : 𝐏(ℰ) ⟶ X` of a quasi-coherent module on an
algebraic space, and let `x : T ⟶ X` be an étale scheme point.  The point `x ≫ σ` of `𝐏(ℰ)` over
`x` lifts uniquely to a section `k_x : T ⟶ 𝐏(ℰ)_T` of the fibre `𝐏(ℰ)_T = T ×_X 𝐏(ℰ)` (Stacks
084B), and the square formed by `k_x`, `x`, `σ` and the projection `𝐏(ℰ)_T ⟶ 𝐏(ℰ)` is cartesian,
the outer rectangle with the cartesian square of the fibre being the identity of `x`.  The
projection is étale, so Stacks 09RR identifies the restriction to `T` of the conormal module of `σ`
with the conormal module of the morphism of schemes `k_x`.

## Main definitions

* `AlgebraicGeometry.Space.sectionFibreLift`: the section `k_x` of the fibre.
* `AlgebraicGeometry.Space.sectionConormalChartIso`: `x^*𝒞_σ ≅ k_x^*Ker(k_x^♯)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

include hσ in
/-- The underlying morphism of the section `σ`, composed with that of `π`, is the identity of
`X`. -/
theorem section_hom_comp_projectiveBundleπ_hom :
    σ.hom ≫ (projectiveBundleπ X E hE hb).hom = 𝟙 X.1 :=
  congrArg InducedCategory.Hom.hom hσ

include hσ in
/-- For a scheme point `x` of `X`, the point `x ≫ σ` of `𝐏(ℰ)` lies over `x`. -/
theorem point_comp_section_comp (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    (x ≫ σ.hom) ≫ (projectiveBundleπ X E hE hb).hom = yoneda.map (𝟙 T) ≫ x := by
  rw [Category.assoc, section_hom_comp_projectiveBundleπ_hom X E hE hb σ hσ, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The section of the fibre `𝐏(ℰ)_T` attached to a section `σ` and a scheme point `x`**: the
lift of the point `x ≫ σ` of Stacks 084B. -/
def sectionFibreLift (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    T ⟶ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T x :=
  ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver T x (𝟙 T)
    ⟨x ≫ σ.hom, point_comp_section_comp X E hE hb σ hσ T x⟩).1

/-- The lift `k_x` is a section of the projection `𝐏(ℰ)_T ⟶ T` of the fibre. -/
theorem sectionFibreLift_comp_fibreHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    sectionFibreLift X E hE hb σ hσ T x ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x = 𝟙 T :=
  ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver T x (𝟙 T)
    ⟨x ≫ σ.hom, point_comp_section_comp X E hE hb σ hσ T x⟩).2

/-- The lift `k_x`, composed with the projection `𝐏(ℰ)_T ⟶ 𝐏(ℰ)`, is the point `x ≫ σ`. -/
theorem yoneda_map_sectionFibreLift_comp (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    yoneda.map (sectionFibreLift X E hE hb σ hσ T x) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x = x ≫ σ.hom :=
  congrArg Subtype.val
    (((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver T x (𝟙 T)).left_inv
      ⟨x ≫ σ.hom, point_comp_section_comp X E hE hb σ hσ T x⟩)

/-- The square `k_x`, `x`, `σ`, `𝐏(ℰ)_T ⟶ 𝐏(ℰ)` is cartesian. -/
theorem isPullback_sectionFibreLift (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    IsPullback (pointHom x) (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x)) σ
      (pointHom ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x)) := by
  have H := ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T x).flip
  have outer : IsPullback (yoneda.map (sectionFibreLift X E hE hb σ hσ T x) ≫
      yoneda.map ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x)) x x
      (σ.hom ≫ (projectiveBundleπ X E hE hb).hom) := by
    have h1 : yoneda.map (sectionFibreLift X E hE hb σ hσ T x) ≫
        yoneda.map ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x) =
          𝟙 (yoneda.obj T) :=
      (yoneda.map_comp _ _).symm.trans (by
        rw [sectionFibreLift_comp_fibreHom]; exact yoneda.map_id T)
    rw [h1, section_hom_comp_projectiveBundleπ_hom X E hE hb σ hσ]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have sq := (IsPullback.of_right outer
    (yoneda_map_sectionFibreLift_comp X E hE hb σ hσ T x) H).flip
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq

/-- The projection `𝐏(ℰ)_T ⟶ 𝐏(ℰ)` of the fibre over an étale scheme point is étale. -/
theorem isEtale_fibreToSpace (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (hx : IsEtale B S hS x) :
    IsEtale B S hS ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x) :=
  have sq : IsPullback (pointHom
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x))
      (yonedaSpaceMap ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x))
      (projectiveBundleπ X E hE hb) (pointHom x) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T x)
  isEtale_of_isPullback B S hS _ _ _ _ sq.flip hx

/-- **The conormal module of the section `σ` is the degree-one piece of its conormal algebra**
(`AlgebraicGeometry.Space.conormalModuleOfImmersionIso`), typed against the conormal algebra of
the morphism `σ` itself, so that its uses in maps of conormal algebras along squares through `σ`
need no identification of `σ` with the morphism built from `σ.hom`. -/
def sectionConormalTargetPieceIso :
    conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)) ≅
      (conormalAlgebra B S hS σ).piece 1 :=
  conormalModuleOfImmersionIso B S hS _ _ _ _

/-- **The conormal module of a section, restricted to an étale scheme point `x`, is the conormal
module of the section `k_x` of the fibre** (Stacks 09RR along the étale projection of the fibre).
-/
def sectionConormalChartIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (hx : IsEtale B S hS x) :
    (modulePullback B S hS (pointHom x)).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
          (isImmersion_of_isClosedImmersion B S hS
            (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≅
      (conormalAlgebra B S hS (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))).piece 1 :=
  (modulePullback B S hS (pointHom x)).mapIso (sectionConormalTargetPieceIso X E hE hb σ hσ) ≪≫
    conormalAlgebraEtaleRestrictionPieceIso B S hS (pointHom x)
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x)) σ _
      (isPullback_sectionFibreLift X E hE hb σ hσ T x) (isEtale_fibreToSpace X E hE hb T x hx) 1

end AlgebraicGeometry.Space

end
