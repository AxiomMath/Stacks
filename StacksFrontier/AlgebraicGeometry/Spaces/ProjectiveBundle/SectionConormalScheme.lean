module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SectionsClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsClassification

/-!
# The conormal isomorphism of Stacks 0B3V at a scheme point of a projective bundle

Let `σ` be a section of the projective bundle `π : 𝐏(ℰ) ⟶ X` of a quasi-coherent module on an
algebraic space, corresponding to the class of an invertible quotient `q : ℰ ⟶ ℒ` under the
bijection of Stacks 0B4I, and let `x : T ⟶ X` be a scheme point.  Under Stacks 084B the point
`x ≫ σ` is a section `s_x` of the scheme projective bundle `𝐏((x^*ℰ)_Zar) ⟶ T`
(`AlgebraicGeometry.Space.pointsEquivSections`), and the characterization of the bijection at
scheme points says that `s_x` corresponds, under the bijection of Stacks 0B3V on `T`, to the
Zariski reading `q_x` of `x^*q`.  So Stacks 0B3V gives the canonical isomorphism
`Ker(q_x) ⊗ ℒ_x^{⊗ -1} ≅ 𝒞_{s_x}` on the scheme `T`; this is the scheme-level isomorphism the
conormal clause of Stacks 0B4I restricts to.

## Main definitions

* `AlgebraicGeometry.Space.situationProjectiveBundleIso`: the relative Proj of `Sym(ℱ)` read as a
  `SheafGradedAlgebra` is the projective bundle `𝐏(ℱ)` of Tag 01OB.
* `AlgebraicGeometry.Space.sectionPointSection`: the section `s_x`.
* `AlgebraicGeometry.Space.sectionPointBundleSection`: the section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T`.
* `AlgebraicGeometry.Space.sectionPointQuotient`: the invertible quotient `q_x`.
* `AlgebraicGeometry.Space.sectionPointConormalIso`: the isomorphism of Stacks 0B3V at `s_x`.
* `AlgebraicGeometry.Space.sectionPointConormalFibreIso`: the conormal sheaf of `s_x` is that of
  the section `k_x` of the fibre of Stacks 084B.

## Main results

* `AlgebraicGeometry.Space.symmetricSectionsEquivInvertibleQuotientClass_sectionPointSection`:
  `s_x` corresponds to `q_x`.
* `AlgebraicGeometry.Space.exists_sectionPointQuotient_iso`: `s_x^*𝒪(1) ≅ ℒ_x` compatibly with
  the quotient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Conormal

variable {X P Q : AlgebraicGeometry.Scheme.{u}} {σ : X ⟶ P} {τ : X ⟶ Q}
  [AlgebraicGeometry.IsImmersion σ] [AlgebraicGeometry.IsImmersion τ] {a : P ⟶ Q} [IsIso a]

/-- The identification `𝒞_τ ≅ 𝒞_σ` of the conormal sheaves of two immersions `σ`, `τ = σ ≫ a`
differing by an isomorphism `a`: the base-change map of the square with identity edge. -/
def conormalUnitSquareIso (sq : σ ≫ a = 𝟙 X ≫ τ) : conormalSheaf τ ≅ conormalSheaf σ :=
  (AlgebraicGeometry.Scheme.Modules.pullbackId X).symm.app _ ≪≫
    @asIso _ _ _ _ (conormalBaseChangeMap sq) (isIso_conormalBaseChangeMap_of_isIso sq)

end Stacks.Conormal

namespace AlgebraicGeometry.Space

section SchemeSide

variable {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent]

/-- **The relative Proj of `Sym(ℱ)` read as a `SheafGradedAlgebra` is the projective bundle
`𝐏(ℱ)`** (`situation_schemeSheafGradedAlgebra`), as an isomorphism of schemes. -/
def situationProjectiveBundleIso :
    Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) ≅
      Stacks.RelativeProj.projectiveBundle Y F :=
  Iso.refl _

/-- The identification lies over `Y`. -/
theorem situationProjectiveBundleIso_hom_toBase :
    Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) =
      (situationProjectiveBundleIso F).hom ≫ Stacks.RelativeProj.projectiveBundleToBase Y F :=
  (Category.id_comp _).symm

/-- The sections of the relative Proj of `Sym(ℱ)` read as a `SheafGradedAlgebra` are the
sections of `𝐏(ℱ) ⟶ Y`. -/
def situationSectionsEquiv :
    {σ : Y ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) //
      σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) = 𝟙 Y} ≃
      {σ : Y ⟶ Stacks.RelativeProj.projectiveBundle Y F //
        σ ≫ Stacks.RelativeProj.projectiveBundleToBase Y F = 𝟙 Y} :=
  Space.overEquivOfIso (situationProjectiveBundleIso F)
    (situationProjectiveBundleIso_hom_toBase F) (𝟙 Y)

/-- The section of `𝐏(ℱ)` attached to `σ` is `σ` followed by `situationProjectiveBundleIso`. -/
theorem situationSectionsEquiv_apply_coe
    (σ : {σ : Y ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) //
      σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) = 𝟙 Y}) :
    (situationSectionsEquiv F σ).1 = σ.1 ≫ (situationProjectiveBundleIso F).hom :=
  rfl

/-- `symmetricSectionsEquivInvertibleQuotientClass` is the bijection of Stacks 0B3V on
`𝐏(ℱ)`, through `situationSectionsEquiv`. -/
theorem symmetricSectionsEquivInvertibleQuotientClass_eq
    (σ : {σ : Y ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) //
      σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) = 𝟙 Y}) :
    symmetricSectionsEquivInvertibleQuotientClass F σ =
      Stacks.RelativeProj.projectiveBundleSectionsEquiv (situationSectionsEquiv F σ) :=
  congrArg Stacks.RelativeProj.projectiveBundleSectionsEquiv
    (Subtype.ext (Category.comp_id σ.1).symm)

end SchemeSide

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (Q : InvertibleQuotient X E)

/-- **The section `s_x` of the scheme projective bundle `𝐏((x^*ℰ)_Zar) ⟶ T`** attached by
Stacks 084B to the point `x ≫ σ` of `𝐏(ℰ)` over a scheme point `x`. -/
def sectionPointSection (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :=
  pointsEquivSections X E hE hb T x
    ⟨x ≫ σ.hom, comp_section_comp (projectiveBundleπ X E hE hb).hom x
      (congrArg InducedCategory.Hom.hom hσ)⟩

/-- **The section `s_x`, as a section of the projective bundle `𝐏((x^*ℰ)_Zar) ⟶ T`** of
Tag 01OB. -/
def sectionPointBundleSection (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    {s : (BigFppfOver.toScheme B S hS).obj T ⟶
        Stacks.RelativeProj.projectiveBundle _ (pointZariskiModule X E T x) //
      s ≫ Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T x) = 𝟙 _} :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T x
  situationSectionsEquiv (pointZariskiModule X E T x) (sectionPointSection X E hE hb σ hσ T x)

/-- **The invertible quotient `q_x` of `(x^*ℰ)_Zar`**: the Zariski reading of `x^*q`. -/
def sectionPointQuotient (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T)
      (pointZariskiModule X E T x) :=
  zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
    (Q.baseChange (pointHom x) (Iso.refl _))

/-- **The section `s_x` corresponds to `q_x` under Stacks 0B3V on `T`**, when `σ` corresponds to
`q` under Stacks 0B4I: the characterization of the bijection at scheme points. -/
theorem symmetricSectionsEquivInvertibleQuotientClass_sectionPointSection
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    symmetricSectionsEquivInvertibleQuotientClass (pointZariskiModule X E T x)
        (sectionPointSection X E hE hb σ hσ T x) =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid _ _)
        (sectionPointQuotient X E hE Q T x) := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have h := ((projectiveBundle_sections_invertibleQuotients X E hE hb).1 ⟨σ, hσ⟩ _).1 hQ T x
  have h' := congrArg (invertibleQuotientClassZariskiEquiv T _
    (isQuasicoherentOnSite_pointPullback X E hE T x)) h
  exact (Equiv.apply_symm_apply _ _).symm.trans h'

/-- **The section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T` corresponds to `q_x` under Stacks 0B3V on `T`.** -/
theorem projectiveBundleSectionsEquiv_sectionPointBundleSection
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    Stacks.RelativeProj.projectiveBundleSectionsEquiv
        (sectionPointBundleSection X E hE hb σ hσ T x) =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid _ _)
        (sectionPointQuotient X E hE Q T x) :=
  have := isQuasicoherent_pointZariskiModule X E hE T x
  (symmetricSectionsEquivInvertibleQuotientClass_eq (pointZariskiModule X E T x)
    (sectionPointSection X E hE hb σ hσ T x)).symm.trans
      (symmetricSectionsEquivInvertibleQuotientClass_sectionPointSection X E hE hb σ hσ Q hQ T x)

/-- The comparison of Stacks 0B3V between `s_x^*𝒪(1)` and `ℒ_x` exists. -/
theorem exists_sectionPointQuotient_iso
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    ∃ e : (Scheme.Modules.pullback (sectionPointBundleSection X E hE hb σ hσ T x).1).obj
        (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T x)).twist ≅
          (sectionPointQuotient X E hE Q T x).L,
      (Stacks.RelativeProj.tautologicalDatum (pointZariskiModule X E T x)).pullbackQuotientMap
          (sectionPointBundleSection X E hE hb σ hσ T x).1
          (sectionPointBundleSection X E hE hb σ hσ T x).2 ≫ e.hom =
        (sectionPointQuotient X E hE Q T x).q :=
  have := isQuasicoherent_pointZariskiModule X E hE T x
  (Stacks.RelativeProj.projectiveBundleSectionsEquiv_eq_iff (pointZariskiModule X E T x)
    (sectionPointBundleSection X E hE hb σ hσ T x).1
    (sectionPointBundleSection X E hE hb σ hσ T x).2
    (sectionPointQuotient X E hE Q T x)).1
    (projectiveBundleSectionsEquiv_sectionPointBundleSection X E hE hb σ hσ Q hQ T x)

attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

/-- **The conormal isomorphism of Stacks 0B3V at the section `s_x`**:
`Ker(q_x) ⊗ ℒ_x^{⊗ -1} ≅ 𝒞_{s_x}` on the scheme `T`. -/
def sectionPointConormalIso
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T x).1
      (sectionPointBundleSection X E hE hb σ hσ T x).2
    kernel (sectionPointQuotient X E hE Q T x).q ⊗
        Stacks.SheafOfModules.Invertible.tensorPower
          ((BigFppfOver.toScheme B S hS).obj T).presheaf
          ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
          (sectionPointQuotient X E hE Q T x).L (-1) ≅
      Stacks.Conormal.conormalSheaf (sectionPointBundleSection X E hE hb σ hσ T x).1 :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T x
  Stacks.RelativeProj.projectiveBundleConormalIso (pointZariskiModule X E T x)
    (sectionPointQuotient X E hE Q T x) (sectionPointBundleSection X E hE hb σ hσ T x).2
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T x).choose
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T x).choose_spec

/-- The identification of the fibre `𝐏(ℰ)_T` of Stacks 084B with `𝐏((x^*ℰ)_Zar)`. -/
def pointFibreProjectiveBundleIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    (BigFppfOver.toScheme B S hS).obj
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T x) ≅
      Stacks.RelativeProj.projectiveBundle _ (pointZariskiModule X E T x) :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T x
  (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreIso T x ≪≫
    pointProjIso X E hE hb T x ≪≫ situationProjectiveBundleIso (pointZariskiModule X E T x)

/-- The section `s_x` is the section `k_x` of the fibre of Stacks 084B followed by the
identification of the fibre with `𝐏((x^*ℰ)_Zar)`. -/
theorem sectionPointSection_eq (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    (sectionPointSection X E hE hb σ hσ T x).1 =
      (BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T x) ≫
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreIso T x).hom ≫
          (pointProjIso X E hE hb T x).hom :=
  Category.assoc _ _ _

/-- The section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T` is the section `k_x` of the fibre followed by
`pointFibreProjectiveBundleIso`. -/
theorem sectionPointBundleSection_eq (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    (sectionPointBundleSection X E hE hb σ hσ T x).1 =
      (BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T x) ≫
        (pointFibreProjectiveBundleIso X E hE hb T x).hom := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  refine (situationSectionsEquiv_apply_coe (pointZariskiModule X E T x) _).trans ?_
  rw [sectionPointSection_eq]
  simp only [pointFibreProjectiveBundleIso, Iso.trans_hom, Category.assoc]

include hσ in
/-- The section `k_x` of the fibre of Stacks 084B is a closed immersion. -/
theorem isClosedImmersion_sectionFibreLift (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T x)) :=
  have := isQuasicoherent_pointZariskiModule X E hE T x
  (MorphismProperty.cancel_right_of_respectsIso @AlgebraicGeometry.IsClosedImmersion _
    (pointFibreProjectiveBundleIso X E hE hb T x).hom).1
    ((sectionPointBundleSection_eq X E hE hb σ hσ T x) ▸
      Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
        (sectionPointBundleSection X E hE hb σ hσ T x).1
        (sectionPointBundleSection X E hE hb σ hσ T x).2)

/-- **The conormal sheaf of `s_x` is that of the section `k_x` of the fibre**, through the
identification of the fibre with `𝐏((x^*ℰ)_Zar)` (the base-change map of a square whose other
edges are isomorphisms). -/
def sectionPointConormalFibreIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T x).1
      (sectionPointBundleSection X E hE hb σ hσ T x).2
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
    Stacks.Conormal.conormalSheaf (sectionPointBundleSection X E hE hb σ hσ T x).1 ≅
      Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map
        (sectionFibreLift X E hE hb σ hσ T x)) :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T x
  haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T x).1
    (sectionPointBundleSection X E hE hb σ hσ T x).2
  haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  Stacks.Conormal.conormalUnitSquareIso (a := (pointFibreProjectiveBundleIso X E hE hb T x).hom)
    ((sectionPointBundleSection_eq X E hE hb σ hσ T x).symm.trans (Category.id_comp _).symm)

end AlgebraicGeometry.Space

end
