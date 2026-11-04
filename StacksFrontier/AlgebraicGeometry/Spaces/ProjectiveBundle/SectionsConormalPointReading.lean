module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalPointReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPieceSquareMapPaste

/-!
# The conormal isomorphism of Stacks 0B4I read at scheme points through a chart

Let `σ` be a section of `π : 𝐏(ℰ) ⟶ X` corresponding to the invertible quotient `q : ℰ ⟶ ℒ`
(Stacks 0B4I), and let `φ : Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ` be the conormal isomorphism glued from the
charts in `AlgebraicGeometry.Space.existsUnique_sectionConormalIso`.  Its chart restrictions are
characterised only at the étale charts `u : U ⟶ X`.  This file reads `φ` at every scheme point of
the form `x' = u ∘ h` with `u` an étale chart and `h : T' ⟶ U` an arbitrary morphism of test
objects (so `x'` need not be étale): the Zariski reading of `x'^*φ`, followed by the map
`x'^*𝒞_σ ⟶ 𝒞_{k_{x'}}` of conormal algebras of the fibre square and the reading of the conormal
module of the section `k_{x'}` of the fibre, is the source reading at `x'` followed by
Stacks 0B3V at the section `s_{x'}` of `𝐏((x'^*ℰ)_Zar)` and the identification of `s_{x'}` with
`k_{x'}`.

## Main results

* `AlgebraicGeometry.Space.sectionConormalTargetPointHom_paste`: the paste of the target maps.
* `AlgebraicGeometry.Space.zariskiReading_pointPullback_sectionConormal_of`: the reading at `u ∘ h`
  of a morphism whose reading at `u` is the chart isomorphism, for a family of source readings.
* `AlgebraicGeometry.Space.zariskiReading_pointPullback_sectionConormalIso_of`,
  `AlgebraicGeometry.Space.zariskiReading_pointPullback_sectionConormalIso`: the same for an
  isomorphism with the chart restrictions of the glued isomorphism (for a family of source
  readings, resp. the explicit ones given `hc`).

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- **The reading of a glued isomorphism at a point through a chart** (generic): if `R` reads
`φu` as the five-fold composite through `s`, `θ`, `F`, `Z` and `Ch`, and the base change along
`P` carries every factor to the corresponding factor at the point (`hsq`, `hθ`, `hF`, `hz`, the
paste `hpaste` of the target maps), then `R'` reads `φx` followed by the target map `tx` and `Zx`
as `sx ≫ θx ≫ Fx`. -/
theorem _root_.CategoryTheory.Functor.conormalGlue_point {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟)
    (Φ : ℬ ⥤ 𝒜) {Ku Cu Nk : ℬ} {Kx Cx Nk' : 𝒜} {a₁ a₂ a₃ : 𝒞} {b₁ b₂ b₃ : 𝒟}
    (φu : Ku ⟶ Cu) (φx : Kx ⟶ Cx) (Ch : Cu ≅ Nk) (tx : Cx ⟶ Nk')
    (Z : R.obj Nk ≅ a₃) (Zx : R'.obj Nk' ⟶ b₃)
    (s : R.obj Ku ⟶ a₁) (hs : IsIso s) (θ : a₁ ≅ a₂) (F : a₂ ≅ a₃)
    (sx : R'.obj Kx ⟶ b₁) (θx : b₁ ⟶ b₂) (Fx : b₂ ⟶ b₃)
    (cK : R'.obj Kx ⟶ P.obj (R.obj Ku)) (pK : P.obj (R.obj Ku) ⟶ R'.obj (Φ.obj Ku))
    (mK : Φ.obj Ku ⟶ Kx) (pC : P.obj (R.obj Cu) ⟶ R'.obj (Φ.obj Cu))
    (pN : P.obj (R.obj Nk) ⟶ R'.obj (Φ.obj Nk)) (mC : Φ.obj Cu ⟶ Cx) (sq : Φ.obj Nk ⟶ Nk')
    (csbc : P.obj a₁ ⟶ b₁) (cbs : P.obj a₂ ⟶ b₂) (cbk : P.obj a₃ ⟶ b₃)
    (hφu : R.map φu = (@asIso _ _ _ _ s hs ≪≫ θ ≪≫ F ≪≫ Z.symm ≪≫ (R.mapIso Ch).symm).hom)
    (hcK : cK ≫ pK ≫ R'.map mK = 𝟙 _) (hsq : cK ≫ P.map s ≫ csbc = sx)
    (hθ : csbc ≫ θx = P.map θ.hom ≫ cbs) (hF : cbs ≫ Fx = P.map F.hom ≫ cbk)
    (nK : P.map (R.map φu) ≫ pC = pK ≫ R'.map (Φ.map φu))
    (nC : P.map (R.map Ch.hom) ≫ pN = pC ≫ R'.map (Φ.map Ch.hom))
    (hnat : Φ.map φu ≫ mC = mK ≫ φx) (hpaste : mC ≫ tx = Φ.map Ch.hom ≫ sq)
    (hz : pN ≫ R'.map sq ≫ Zx = P.map Z.hom ≫ cbk) :
    R'.map φx ≫ R'.map tx ≫ Zx = sx ≫ θx ≫ Fx := by
  have h1 : R.map φu ≫ R.map Ch.hom ≫ Z.hom = s ≫ θ.hom ≫ F.hom := by
    rw [hφu]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_inv, Category.assoc]
    rw [← R.map_comp_assoc, Iso.inv_hom_id, R.map_id, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id]
  have h2 : P.map (R.map φu) ≫ P.map (R.map Ch.hom) ≫ P.map Z.hom ≫ cbk =
      P.map s ≫ P.map θ.hom ≫ P.map F.hom ≫ cbk := by
    simp only [← P.map_comp_assoc, h1]
  have h3 : R'.map (Φ.map φu) ≫ R'.map (Φ.map Ch.hom) ≫ R'.map sq =
      R'.map mK ≫ R'.map φx ≫ R'.map tx := by
    simp only [← R'.map_comp, ← hpaste, reassoc_of% hnat]
  rw [← hsq]
  simp only [Category.assoc]
  rw [reassoc_of% hθ, hF, ← h2, ← hz, reassoc_of% nC, reassoc_of% nK, reassoc_of% h3,
    reassoc_of% hcK]

section Point

variable (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

/-- **The paste of the target maps at `x` and `x ∘ h`**: the composition comparison of Stacks
03LU followed by the target map at `x ∘ h` is the inverse image along `h` of the chart
isomorphism at the étale point `x` followed by the map of conormal algebras of the square of
sections over `h`. -/
theorem sectionConormalTargetPointHom_paste {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) (hx : IsEtale B S hS x) :
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x)))) ≫
      sectionConormalTargetPointHom X E hE hb σ hσ T' (yoneda.map h ≫ x) =
    (modulePullback B S hS (yonedaSpaceMap h)).map
        (sectionConormalChartIso X E hE hb σ hσ T x hx).hom ≫
      (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h)
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
          (yonedaSpaceMap ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison
          T x h))
      (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x).w.symm 1) := by
  have hp := conormalAlgebraPieceSquareMapOfIso_comp_of_eq B S hS σ (pointHom x)
    (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
        (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x))
        (yonedaSpaceMap h)
    (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
        (yonedaSpaceMap ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T
        x h))
    (isPullback_sectionFibreLift X E hE hb σ hσ T x).w.symm
    (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x).w.symm
    (pointHom (yoneda.map h ≫ x)) rfl (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T'
        (yoneda.map h ≫ x)))
    (yonedaSpaceMap_fibreComparison_comp_pointHom X E hE hb h x)
    (isPullback_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)).w.symm 1
        (sectionConormalTargetPieceIso X E hE hb σ hσ)
  have hd' : sectionConormalTargetPointHom X E hE hb σ hσ T' (yoneda.map h ≫ x) =
      conormalAlgebraPieceSquareMapOfIso B S hS (pointHom (yoneda.map h ≫ x))
        (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))) σ
            (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
            ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T'
            (yoneda.map h ≫ x)))
        (isPullback_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)).w.symm 1
            (sectionConormalTargetPieceIso X E hE hb σ hσ) := rfl
  have hd : sectionConormalTargetPointHom X E hE hb σ hσ T x =
      conormalAlgebraPieceSquareMapOfIso B S hS (pointHom x)
        (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x)) σ
            (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
            ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x))
        (isPullback_sectionFibreLift X E hE hb σ hσ T x).w.symm 1
            (sectionConormalTargetPieceIso X E hE hb σ hσ) := rfl
  refine (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ _ ≫ t) hd').trans (hp.trans ?_))
  exact congrArg (fun t => (modulePullback B S hS (yonedaSpaceMap h)).map t ≫ _)
    (hd.symm.trans (sectionConormalTargetPointHom_eq_chartIso X E hE hb σ hσ T x hx))

/-- Transport of the naturality of the composition comparison of Stacks 03LU along an equality
of the composite. -/
theorem modulePullbackCompIso_hom_app_eqToHom_naturality {Y'' Y' Y : AlgebraicSpaces B S hS}
    (a : Y'' ⟶ Y') (b : Y' ⟶ Y) (c : Y'' ⟶ Y) (e : a ≫ b = c) {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (f : M ⟶ N) :
    (modulePullback B S hS a).map ((modulePullback B S hS b).map f) ≫
        (modulePullbackCompIso B S hS a b).hom.app N ≫
        eqToHom (congrArg (fun k : Y'' ⟶ Y => (modulePullback B S hS k).obj N) e) =
      ((modulePullbackCompIso B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun k : Y'' ⟶ Y => (modulePullback B S hS k).obj M) e)) ≫
        (modulePullback B S hS c).map f := by
  subst e
  simp only [eqToHom_refl, Category.comp_id]
  exact (modulePullbackCompIso B S hS a b).hom.naturality f

/-- **The reading at `x ∘ h` of a morphism read at an étale point `x` as the chart
isomorphism**: if the Zariski reading of `x^*φ` is the chart isomorphism through the source
readings `s`, and `s` is compatible with base change along an arbitrary `h : T' ⟶ T`, then the
reading of `(x ∘ h)^*φ`, followed by the target map `x'^*𝒞_σ ⟶ 𝒞_{k_{x'}}` and the reading of
the conormal module of `k_{x'}`, is the source reading at `x' = x ∘ h` followed by Stacks 0B3V at
`s_{x'}` and the identification of `s_{x'}` with `k_{x'}`.  The point `x'` need not be étale. -/
theorem zariskiReading_pointPullback_sectionConormal_of
    (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
             Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
             (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
             (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
             (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
              (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
              ((BigFppfOver.toScheme B S hS).obj T).presheaf
              ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) (hx : IsEtale B S hS x)
    (hs : IsIso (s T x))
    (φ : (haveI : IsInvertible (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L := Q.invertible.toAlgebraicGeometry;
                (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
                (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)))) ⟶
                (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2
                σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    (hφ : (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom x)).map φ) =
      (sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
        Q.invertible.toAlgebraicGeometry
    (pointZariskiModuleBaseChangeIso X (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map (s T x) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).hom =
      s T' (yoneda.map h ≫ x) →
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).map φ) ≫
      (zariskiReadingFunctor T').map (sectionConormalTargetPointHom X E hE hb σ hσ T'
          (yoneda.map h ≫ x)) ≫
      (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))).hom =
    s T' (yoneda.map h ≫ x) ≫ (sectionPointConormalIso X E hE hb σ hσ Q hQ T'
        (yoneda.map h ≫ x)).hom ≫
      (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ x)).hom := by
  intro hsq
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T x).1
    (sectionPointBundleSection X E hE hb σ hσ T x).2
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
  have hφu := hφ.trans (congrArg Iso.hom
    (sectionConormalReadingIsoOf_eq X E hE Q hb σ hσ s hQ T x hx hs))
  have h1 := pointZariskiModuleBaseChangeIso_hom_comp_inv X x h
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
         Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
         (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
         (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
         (structureRingSheaf B S hS X).property Q.L (-1))))
    (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
  have hmK := congrArg (zariskiReadingFunctor T').map
      (modulePullbackCompIso_hom_app_representedSpaceMap_pointHom X h x
    (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)))))
  have h3 := sectionPointConormalIso_baseChange X E hE hb σ hσ Q hQ x h
  have h4 := sectionPointConormalFibreIso_baseChange X E hE hb x h σ hσ
  have nK := zariskiReadingPullbackHom_naturality_yonedaSpaceMap h
    ((modulePullback B S hS (pointHom x)).map φ)
  have nC := zariskiReadingPullbackHom_naturality_yonedaSpaceMap h
      (sectionConormalChartIso X E hE hb σ hσ T x hx).hom
  have hnat := modulePullbackCompIso_hom_app_eqToHom_naturality (yonedaSpaceMap h) (pointHom x)
      (pointHom (yoneda.map h ≫ x))
    (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x)) φ
  have hpaste := sectionConormalTargetPointHom_paste X E hE hb σ hσ x h hx
  have hz := zariskiReadingConormalIso_naturality_of_comm (sectionFibreLift X E hE hb σ hσ T x)
      (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)) h
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h)
    (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x).w.symm
    (toScheme_map_sectionFibreLift_comp_fibreComparison X E hE hb x h σ hσ)
  exact CategoryTheory.Functor.conormalGlue_point (Scheme.Modules.pullback
      ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T) (zariskiReadingFunctor T')
      (modulePullback B S hS (yonedaSpaceMap h))
    ((modulePullback B S hS (pointHom x)).map φ) ((modulePullback B S hS
        (pointHom (yoneda.map h ≫ x))).map φ) (sectionConormalChartIso X E hE hb σ hσ T x hx)
    (sectionConormalTargetPointHom X E hE hb σ hσ T' (yoneda.map h ≫ x))
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x))
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))).hom
    (s T x) hs (sectionPointConormalIso X E hE hb σ hσ Q hQ T x)
    (sectionPointConormalFibreIso X E hE hb σ hσ T x)
    (s T' (yoneda.map h ≫ x)) (sectionPointConormalIso X E hE hb σ hσ Q hQ T'
        (yoneda.map h ≫ x)).hom
    (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ x)).hom
    (pointZariskiModuleBaseChangeIso X
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
           (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
           (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
           (structureRingSheaf B S hS X).property Q.L (-1))))
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom
    ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
           (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
           (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
           (structureRingSheaf B S hS X).property Q.L (-1))))))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
           (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
           (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
           (structureRingSheaf B S hS X).property Q.L (-1)))) ≫ eqToHom
           (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))))
          (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x))))
    ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    ((zariskiReadingPullbackHom h).app ((conormalAlgebra B S hS
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))).piece 1))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫ eqToHom
              (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x))))
              (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h)
              (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
          (yonedaSpaceMap ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison
          T x h))
      (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x).w.symm 1)
    (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
      (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
      (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
      (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
      (sectionPointQuotientBaseChangeL X E hE Q x h)
      (sectionPointQuotient_baseChange_q X E hE Q x h)).hom
    (Stacks.Conormal.conormalBaseChangeMap
      (sectionPointBundleSection_baseChange X E hE hb σ hσ x h))
    (Stacks.Conormal.conormalBaseChangeMap
      (toScheme_map_sectionFibreLift_comp_fibreComparison X E hE hb x h σ hσ))
    hφu ((congrArg (fun t => _ ≫ _ ≫ t) hmK).symm.trans h1) hsq h3 h4 nK nC hnat hpaste hz

/-- The restriction of a morphism to a chart is its inverse image along the point of the chart. -/
theorem chartModuleRestriction_map_eq_modulePullback_map (U : SmallEtale B S hS X.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) :
    (modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X.1).obj U) (X := X)
      U.1.hom)).map f = (chartModuleRestriction B S hS X U).map f := by
  refine eq_of_heq (modulePullback_map_heq_of_heq ?_ ?_ _ _ ?_ ?_ ?_ _ _ ?_)
  · exact rfl
  · exact rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl

/-- **The reading of the glued conormal isomorphism at any point factoring through a chart**:
for an isomorphism `φ` restricting on every étale chart to the chart isomorphism through the
source readings `s`, a chart `U` and an arbitrary `h : T' ⟶ U`, the reading of `(u ∘ h)^*φ`
followed by the target map and the reading of the conormal module of `k_{u ∘ h}` is the source
reading at `u ∘ h` followed by Stacks 0B3V and the identification of the sections. -/
theorem zariskiReading_pointPullback_sectionConormalIso_of
    (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
             Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
             (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
             (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
             (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
              (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
              ((BigFppfOver.toScheme B S hS).obj T).presheaf
              ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
                (hs : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso
                (s T x))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hsq : ∀ {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T),
      haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry
      (pointZariskiModuleBaseChangeIso X (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map (s T x) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).hom =
      s T' (yoneda.map h ≫ x))
    (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
    (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ U).hom)
    (U : SmallEtale B S hS X.1) {T' : BigFppfOver B S hS}
    (h : T' ⟶ ((SmallEtale.toOver B S hS X.1).obj U)) :
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ U.1.hom)
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom (yoneda.map h ≫ U.1.hom))).map
        φ.hom) ≫
      (zariskiReadingFunctor T').map (sectionConormalTargetPointHom X E hE hb σ hσ T'
          (yoneda.map h ≫ U.1.hom)) ≫
      (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T'
          (yoneda.map h ≫ U.1.hom))).hom =
    s T' (yoneda.map h ≫ U.1.hom) ≫ (sectionPointConormalIso X E hE hb σ hσ Q hQ T'
        (yoneda.map h ≫ U.1.hom)).hom ≫
      (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ U.1.hom)).hom := by
  have e1 := chartModuleRestriction_map_eq_modulePullback_map X U φ.hom
  have e2 := hφ U
  have e4 := zariskiReading_map_sectionConormalChartFamilyOf_hom X E hE Q hb σ hσ s hs hQ U
  have e5 := (congrArg (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).map
    (e1.trans e2)).trans e4
  exact zariskiReading_pointPullback_sectionConormal_of X E hE Q hb σ hσ s hQ
      (T := ((SmallEtale.toOver B S hS X.1).obj U)) (T' := T')
    U.1.hom h (isEtale_of_presheaf_etale B S hS U.2)
    (hs ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom (isEtale_of_presheaf_etale B S hS U.2)) φ.hom
        e5
    (hsq (T := ((SmallEtale.toOver B S hS X.1).obj U)) (T' := T') U.1.hom h)

/-- **The reading of the conormal isomorphism of Stacks 0B4I at any point factoring through a
chart**, for the explicit source readings, given the monoidality `hc` of the base change of the
Zariski reading: for an isomorphism `φ : Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ` with the chart restrictions of
`existsUnique_sectionConormalIso`, a chart `u : U ⟶ X` and an arbitrary `h : T' ⟶ U`, the reading
of `(u ∘ h)^*φ` followed by the target map and the reading of the conormal module of `k_{u ∘ h}`
is the explicit source reading at `u ∘ h`, Stacks 0B3V at `s_{u ∘ h}` and the identification of
`s_{u ∘ h}` with `k_{u ∘ h}`. -/
theorem zariskiReading_pointPullback_sectionConormalIso
    (hc : ∀ {T T' : BigFppfOver B S hS} (h : T' ⟶ T),
      ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
              ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
          (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)) ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
          (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
          ((Stacks.RingedSpace.comparisonBifunctorIso ((BigFppfOver.toScheme B S hS).map
          h).toLRSHom.toShHom).hom.app ((zariskiReadingFunctor T).obj (N),
          (zariskiReadingFunctor T).obj (M))) ((zariskiReadingPullbackHom h).app (N))
          ((zariskiReadingPullbackHom h).app (M)) ((zariskiReadingPullbackHom h).app
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N))) ((zariskiReadingFunctor T').obj
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))).hom))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
    (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ
          (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
      haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj (kernel Q.q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom))
          (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).hom)
    (U : SmallEtale B S hS X.1) {T' : BigFppfOver B S hS}
    (h : T' ⟶ ((SmallEtale.toOver B S hS X.1).obj U)) :
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ U.1.hom)
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom (yoneda.map h ≫ U.1.hom))).map
        φ.hom) ≫
      (zariskiReadingFunctor T').map (sectionConormalTargetPointHom X E hE hb σ hσ T'
          (yoneda.map h ≫ U.1.hom)) ≫
      (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T'
          (yoneda.map h ≫ U.1.hom))).hom =
    (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
      haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj (kernel Q.q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom)) T'
          (yoneda.map h ≫ U.1.hom) ≫ (sectionPointConormalIso X E hE hb σ hσ Q hQ T'
          (yoneda.map h ≫ U.1.hom)).hom ≫
      (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ U.1.hom)).hom :=
  zariskiReading_pointPullback_sectionConormalIso_of X E hE Q hb σ hσ _
      (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ
    (fun x h => conormalSourcePointReading_baseChange X E hE Q x h (hc h)) φ hφ U h

end Point

end AlgebraicGeometry.Space

end
