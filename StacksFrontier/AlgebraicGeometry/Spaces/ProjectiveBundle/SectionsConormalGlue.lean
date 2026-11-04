module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingTensorSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalChartIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalSchemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalFibreBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionConormalNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleIsoGlueing

/-!
# The conormal clause of Stacks 0B4I: glueing the chart isomorphisms

Let `σ` be a section of `π : 𝐏(ℰ) ⟶ X` corresponding to the invertible quotient `q : ℰ ⟶ ℒ`
(Stacks 0B4I).  At every étale scheme point `x : T ⟶ X` the Zariski reading of
`x^*(Ker(q) ⊗ ℒ^{⊗ -1})` is identified with `Ker(q_x) ⊗ ℒ_x^{⊗ -1}` by a source reading `s_x`, and
Stacks 0B3V on `T`, the identification of the section `s_x` of `𝐏((x^*ℰ)_Zar)` with the section
`k_x` of the fibre of Stacks 084B, and the reading of the conormal module of `k_x` identify it
further with the reading of `x^*𝒞_σ`.  Lifting along the Zariski reading gives chart
isomorphisms `x^*(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ x^*𝒞_σ`.

This file proves that the chart isomorphisms are compatible with the transitions of the chart
restrictions of Stacks 03LY whenever the source readings are compatible with base change, and
glues them to an isomorphism `Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ`, unique with these chart restrictions.
For the explicit source readings (the monoidality comparison of the Zariski reading followed by
the kernel factor and the inverse-line factor) the compatibility with base change is
`AlgebraicGeometry.Space.conormalSourcePointReading_baseChange`, whose only hypothesis is the
monoidality `hc` of the base change of the Zariski reading.

## Main results

* `AlgebraicGeometry.Space.sectionConormalPointIsoOf_baseChange`: the compatibility of the chart
  isomorphisms at `x` and `x ∘ h`, for étale `x`, `h`.
* `AlgebraicGeometry.Space.existsUnique_sectionConormalIso_of`: the glued isomorphism, for any
  family of source readings compatible with base change.
* `AlgebraicGeometry.Space.existsUnique_sectionConormalIso`: the glued isomorphism for the
  explicit source readings, given `hc`.
* `AlgebraicGeometry.Space.zariskiReading_map_sectionConormalChartFamily_hom`: the reading of its
  chart restrictions.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
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

/-! ### Generic pastes -/

/-- **The base change of a five-fold reading isomorphism** (generic): if the first factor `s` is
carried to `s'` through the identification `cK`, the next two by squares to the base-change maps
`cbs`, `cbk`, and the last two together (`hT`), then the whole composite is carried to the
primed one. -/
theorem _root_.CategoryTheory.Functor.conormalGlue_key {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (P : 𝒞 ⥤ 𝒟) {a₀ a₁ a₂ a₃ a₄ a₅ : 𝒞} {w₀ w₀' b₁ b₂ b₃ b₄ w₅ w₅' : 𝒟}
    (s : a₀ ⟶ a₁) (hs : IsIso s) (θ : a₁ ≅ a₂) (φF : a₂ ≅ a₃) (Z : a₄ ≅ a₃) (RC : a₅ ≅ a₄)
    (s' : w₀' ⟶ b₁) (hs' : IsIso s') (θ' : b₁ ≅ b₂) (F' : b₂ ≅ b₃) (Z' : b₄ ≅ b₃) (RC' : w₅' ≅ b₄)
    (pK : P.obj a₀ ⟶ w₀) (mK : w₀ ⟶ w₀') (cK : w₀' ⟶ P.obj a₀)
    (csbc : P.obj a₁ ⟶ b₁) (cbs : P.obj a₂ ⟶ b₂) (cbk : P.obj a₃ ⟶ b₃)
    (pC : P.obj a₅ ⟶ w₅) (mC : w₅ ⟶ w₅')
    (hc : (pK ≫ mK) ≫ cK = 𝟙 _) (hsq : cK ≫ P.map s ≫ csbc = s')
    (hθ : csbc ≫ θ'.hom = P.map θ.hom ≫ cbs) (hF : cbs ≫ F'.hom = P.map φF.hom ≫ cbk)
    (hT : P.map (Z.symm ≪≫ RC.symm).hom ≫ pC ≫ mC = cbk ≫ (Z'.symm ≪≫ RC'.symm).hom)
    (β : a₀ ≅ a₅) (β' : w₀' ≅ w₅')
    (hβ : β = @asIso _ _ _ _ s hs ≪≫ θ ≪≫ φF ≪≫ Z.symm ≪≫ RC.symm)
    (hβ' : β' = @asIso _ _ _ _ s' hs' ≪≫ θ' ≪≫ F' ≪≫ Z'.symm ≪≫ RC'.symm) :
    P.map β.hom ≫ pC ≫ mC = pK ≫ mK ≫ β'.hom := by
  subst hβ hβ'
  simp only [Iso.trans_hom, asIso_hom] at hT ⊢
  rw [← hsq]
  simp only [Category.assoc] at hc ⊢
  rw [reassoc_of% hθ, reassoc_of% hF, ← hT, reassoc_of% hc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The target half of the base change of a five-fold reading** (generic): the inverse of the
reading `Z` of the conormal sheaf and of the reading of the chart identification `Ch`, followed by
the base change `pC` of the reading and the reading `mC` of the comparison `cmp ≫ e`, from the
naturality `n` of the base change of the reading, the naturality `c` of `Ch` and the naturality
`z` of `Z`. -/
theorem _root_.CategoryTheory.Functor.conormalGlue_target {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟) (Φ : ℬ ⥤ 𝒜)
    {N₀ N₁ : ℬ} {N₀' N₀'' N₁' : 𝒜} {a₃ : 𝒞} {b₃ : 𝒟} (Ch : N₀ ≅ N₁) (Ch' : N₀'' ≅ N₁')
    (Z : R.obj N₁ ≅ a₃) (Z' : R'.obj N₁' ≅ b₃) (cbk : P.obj a₃ ⟶ b₃)
    (pP : P.obj (R.obj N₁) ⟶ R'.obj (Φ.obj N₁)) (pC : P.obj (R.obj N₀) ⟶ R'.obj (Φ.obj N₀))
    (cmp : Φ.obj N₀ ⟶ N₀') (e : N₀' ⟶ N₀'') (R9 : Φ.obj N₁ ⟶ N₁')
    (mC : R'.obj (Φ.obj N₀) ⟶ R'.obj N₀'') (hm : mC = R'.map (cmp ≫ e))
    (n : P.map (R.map Ch.hom) ≫ pP = pC ≫ R'.map (Φ.map Ch.hom))
    (c : cmp ≫ e ≫ Ch'.hom = Φ.map Ch.hom ≫ R9)
    (z : pP ≫ R'.map R9 ≫ Z'.hom = P.map Z.hom ≫ cbk) :
    P.map (Z.symm ≪≫ (R.mapIso Ch).symm).hom ≫ pC ≫ mC =
      cbk ≫ (Z'.symm ≪≫ (R'.mapIso Ch').symm).hom := by
  have c' : cmp ≫ e = Φ.map Ch.hom ≫ R9 ≫ Ch'.inv := by
    rw [← reassoc_of% c, Iso.hom_inv_id, Category.comp_id]
  have n' : P.map (R.map Ch.inv) ≫ pC ≫ R'.map (Φ.map Ch.hom) = pP := by
    rw [← n, ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have z' : pP ≫ R'.map R9 = P.map Z.hom ≫ cbk ≫ Z'.inv := by
    rw [← reassoc_of% z, Iso.hom_inv_id, Category.comp_id]
  rw [hm, c']
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% n', reassoc_of% z', ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Reduction of a compatibility of lifted isomorphisms to their readings** (generic): if `R'`
is faithful on the relevant morphisms, `pK` is an epimorphism, `R` reads `α` as `β` and `R'` reads
`α'` as `β'`, and the base change `p` of the reading is natural at `α`, then
`Φ(α) ≫ cmpC = cmpK ≫ α'` follows from the read square. -/
theorem _root_.CategoryTheory.Functor.conormalGlue_reduce {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟) (Φ : ℬ ⥤ 𝒜)
    {M N : ℬ} {M' N' : 𝒜} (α : M ⟶ N) (α' : M' ⟶ N') (β : R.obj M ⟶ R.obj N)
    (β' : R'.obj M' ⟶ R'.obj N') (hβ : R.map α = β) (hβ' : R'.map α' = β')
    (pK : P.obj (R.obj M) ⟶ R'.obj (Φ.obj M)) (pC : P.obj (R.obj N) ⟶ R'.obj (Φ.obj N))
    (hp : P.map (R.map α) ≫ pC = pK ≫ R'.map (Φ.map α)) (hpK : Epi pK)
    (cmpC : Φ.obj N ⟶ N') (cmpK : Φ.obj M ⟶ M')
    (hinj : ∀ a b : Φ.obj M ⟶ N', R'.map a = R'.map b → a = b)
    (key : P.map β ≫ pC ≫ R'.map cmpC = pK ≫ R'.map cmpK ≫ β') :
    Φ.map α ≫ cmpC = cmpK ≫ α' := by
  refine hinj _ _ ((cancel_epi pK).1 ?_)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← reassoc_of% hp, hβ,
    hβ', key]

/-! ### The chart isomorphisms through a family of source readings -/

section Chart

variable (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

/-- **The conormal isomorphism of Stacks 0B4I read at an étale scheme point**, through a given
reading `s` of the source: `s_x`, Stacks 0B3V at `s_x`, the identification of `s_x` with the
section `k_x` of the fibre, and the reading of the conormal module of `k_x`. -/
def sectionConormalReadingIsoOf (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x)
    (hs : IsIso (s T x)) :
    (zariskiReadingFunctor T).obj
        ((modulePullback B S hS (pointHom x)).obj
            (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
               X).property Q.L := Q.invertible.toAlgebraicGeometry;
            (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))))) ≅
      (zariskiReadingFunctor T).obj
        ((modulePullback B S hS (pointHom x)).obj (conormalModuleOfImmersion B S hS
            (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) :=
  haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  @asIso _ _ _ _ (s T x) hs ≪≫
    sectionPointConormalIso X E hE hb σ hσ Q hQ T x ≪≫
    sectionPointConormalFibreIso X E hE hb σ hσ T x ≪≫
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x)).symm ≪≫
    ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T x hx)).symm

/-- **The chart isomorphism of the conormal clause of Stacks 0B4I** at an étale scheme point,
through a given reading `s` of the source: the lift of `sectionConormalReadingIsoOf` along the
Zariski reading. -/
def sectionConormalPointIsoOf (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x)
    (hs : IsIso (s T x)) :
    (modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)))) ≅
      (modulePullback B S hS (pointHom x)).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) :=
  isoOfZariskiReadingIso T
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q))
    (isQuasicoherentOnSite_pointPullback_sectionConormalTarget X E hE hb σ hσ T x hx)
    (sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ T x hx hs)

/-- The reading of the chart isomorphism is the reading isomorphism. -/
theorem zariskiReading_map_sectionConormalPointIsoOf_hom (s : ∀ (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x)
    (hs : IsIso (s T x)) :
    (zariskiReadingFunctor T).map (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom =
      (sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom :=
  zariskiReading_map_isoOfZariskiReadingIso_hom T _ _ _

/-- The reading isomorphism through `s`, unfolded. -/
theorem sectionConormalReadingIsoOf_eq (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x)
    (hs : IsIso (s T x)) :
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
    sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ T x hx hs =
      (@asIso _ _ _ _ (s T x) hs ≪≫
        sectionPointConormalIso X E hE hb σ hσ Q hQ T x ≪≫
        sectionPointConormalFibreIso X E hE hb σ hσ T x ≪≫
        (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x)).symm ≪≫
        ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T x hx)).symm) :=
  rfl

/-- The composition comparison of Stacks 03LU for two heterogeneously equal pairs of morphisms
between equal spaces. -/
theorem modulePullbackCompIso_hom_app_heq {Y Y₀ Y' Y'₀ Y'' : AlgebraicSpaces B S hS}
    (hY : Y = Y₀) (hY' : Y' = Y'₀) (a : Y ⟶ Y') (a' : Y₀ ⟶ Y'₀) (e : HEq a a') (b : Y' ⟶ Y'')
    (b' : Y'₀ ⟶ Y'') (hb : HEq b b') {M M' : Modules.{u, u} B S hS Y''.1 Y''.2} (hM : M = M') :
    HEq ((modulePullbackCompIso B S hS a b).hom.app M)
      ((modulePullbackCompIso B S hS a' b').hom.app M') := by
  subst hY hY' hM
  obtain rfl := eq_of_heq e
  obtain rfl := eq_of_heq hb
  rfl

/-- The composition comparison of Stacks 03LU at a morphism of represented algebraic spaces and a
scheme point, in the two spellings of the morphism of represented spaces. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap_pointHom_heq
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    HEq ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app M)
      ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app M) := by
  refine modulePullbackCompIso_hom_app_heq ?_ ?_ _ _ ?_ _ _ ?_ ?_
  · exact rfl
  · exact rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact rfl

/-- The composition comparison of Stacks 03LU at a morphism of represented algebraic spaces and a
scheme point, in the two spellings of the morphism of represented spaces. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap_pointHom {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app M =
      (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app M ≫
        eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj M)
          (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x))) :=
  (eq_of_heq (modulePullbackCompIso_hom_app_representedSpaceMap_pointHom_heq X h x M)).trans
    (Category.comp_id _).symm

/-- **The chart isomorphisms at `x` and `x ∘ h` are compatible** with the composition comparison
of Stacks 03LU, for étale `x`, `h` and a family `s` of source readings compatible with base change
along `h`: checked on Zariski readings, where it is the paste of the source square `hsq`,
Stacks 0B3V (`sectionPointConormalIso_baseChange`), the fibre square
(`sectionPointConormalFibreIso_baseChange`), the naturality of the reading of the conormal module
(`zariskiReadingConormalIso_naturality`) and of the chart identification
(`sectionConormalChartIso_naturality`). -/
theorem sectionConormalPointIsoOf_baseChange (s : ∀ (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) (hx : IsEtale B S hS x)
    (hh : IsEtale B S hS (yoneda.map h)) (hx' : IsEtale B S hS (yoneda.map h ≫ x))
    (hs : IsIso (s T x)) (hs' : IsIso (s T' (yoneda.map h ≫ x))) :
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
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom ≫
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) =
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
            (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))) ≫
      (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T' (yoneda.map h ≫ x) hx' hs').hom := by
  intro hsq
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)
  have hpK : IsIso ((zariskiReadingPullbackHom h).app
      ((modulePullback B S hS (pointHom x)).obj
          (have : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
             Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))))) :=
    isIso_zariskiReadingPullbackHom_app h _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q))
  have hc := sectionConormalChartIso_naturality X E hE hb σ hσ h x hx hh hx'
  have hT := CategoryTheory.Functor.conormalGlue_target
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
    (zariskiReadingFunctor T') (modulePullback B S hS (yonedaSpaceMap h))
    (sectionConormalChartIso X E hE hb σ hσ T x hx)
    (sectionConormalChartIso X E hE hb σ hσ T' (yoneda.map h ≫ x) hx')
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x))
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
    (Stacks.Conormal.conormalBaseChangeMap
      (toScheme_map_sectionFibreLift_comp_fibreComparison X E hE hb x h σ hσ))
    ((zariskiReadingPullbackHom h).app ((conormalAlgebra B S hS
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))).piece 1))
    ((zariskiReadingPullbackHom h).app
      ((modulePullback B S hS (pointHom x)).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    (eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
      (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x))))
    (conormalAlgebraEtaleRestrictionPieceIso B S hS (yonedaSpaceMap h)
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
      (yonedaSpaceMap
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h))
      (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x)
      (isEtale_fibreComparison X E hE hb h x hh) 1).hom
    ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (pointHom x)).hom.app (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE
          hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    (congrArg (zariskiReadingFunctor T').map
      (modulePullbackCompIso_hom_app_representedSpaceMap_pointHom X h x _))
    (zariskiReadingPullbackHom_naturality_yonedaSpaceMap h
      (sectionConormalChartIso X E hE hb σ hσ T x hx).hom)
    hc
    (zariskiReadingConormalIso_naturality (sectionFibreLift X E hE hb σ hσ T x)
      (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)) h
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h)
      (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x)
      (isEtale_fibreComparison X E hE hb h x hh)
      (toScheme_map_sectionFibreLift_comp_fibreComparison X E hE hb x h σ hσ))
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T x).1
    (sectionPointBundleSection X E hE hb σ hσ T x).2
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
  have h1 := pointZariskiModuleBaseChangeIso_inv_comp_hom X x h
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
         Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
      (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property Q.L (-1))))
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
  have h3 := sectionPointConormalIso_baseChange X E hE hb σ hσ Q hQ x h
  have h4 := sectionPointConormalFibreIso_baseChange X E hE hb x h σ hσ
  refine (fun hK => ?_) (CategoryTheory.Functor.conormalGlue_key
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
    (s T x) hs (sectionPointConormalIso X E hE hb σ hσ Q hQ T x)
    (sectionPointConormalFibreIso X E hE hb σ hσ T x)
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T x))
    ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T x hx))
    (s T' (yoneda.map h ≫ x)) hs' (sectionPointConormalIso X E hE hb σ hσ Q hQ T'
        (yoneda.map h ≫ x))
    (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ x))
    (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
    ((zariskiReadingFunctor T').mapIso
      (sectionConormalChartIso X E hE hb σ hσ T' (yoneda.map h ≫ x) hx'))
    ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))))))
    ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (pointHom x)).hom.app
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
             Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))))
    (pointZariskiModuleBaseChangeIso X
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))))
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom
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
    ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (pointHom x)).hom.app (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE
          hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))))
    h1 hsq h3 h4 hT _ _ (sectionConormalReadingIsoOf_eq X E hE Q hb σ hσ s hQ T x hx hs)
    (sectionConormalReadingIsoOf_eq X E hE Q hb σ hσ s hQ T' (yoneda.map h ≫ x) hx' hs'))
  · exact CategoryTheory.Functor.conormalGlue_reduce
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T') (modulePullback B S hS (representedSpaceMap B S hS h))
      (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom
      (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T' (yoneda.map h ≫ x) hx' hs').hom _ _
      (zariskiReading_map_sectionConormalPointIsoOf_hom X E hE Q hb σ hσ s hQ T x hx hs)
      (zariskiReading_map_sectionConormalPointIsoOf_hom X E hE Q hb σ hσ s hQ T'
        (yoneda.map h ≫ x) hx' hs')
      _ _ ((zariskiReadingPullbackHom h).naturality _) (@IsIso.epi_of_iso _ _ _ _ _ hpK) _ _
      (fun a b hab => zariskiReading_map_injective T'
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) _
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
            (isQuasicoherentOnSite_sectionConormalSource X E hE Q))) hab) hK

/-- **The chart isomorphisms at `x` and `x'` are compatible** for `x' = x ∘ h`, through the
composition comparison of Stacks 03LU followed by the transport along `h ≫ x = x'`: the form of
`sectionConormalPointIsoOf_baseChange` in which the transitions of the chart restrictions are
written. -/
theorem sectionConormalPointIsoOf_baseChange_of_eq (s : ∀ (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) (x' : yoneda.obj T' ⟶ X.1)
    (e : yoneda.map h ≫ x = x') (hk : representedSpaceMap B S hS h ≫ pointHom x = pointHom x')
    (hx : IsEtale B S hS x) (hh : IsEtale B S hS (yoneda.map h)) (hx' : IsEtale B S hS x')
    (hs : IsIso (s T x)) (hs' : IsIso (s T' x')) :
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
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T x hx hs).hom ≫
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x) ≪≫
        eqToIso (congrArg (fun k => modulePullback B S hS k) hk)).app
            (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))).hom =
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x) ≪≫
        eqToIso (congrArg (fun k => modulePullback B S hS k) hk)).app
            (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
               X).property Q.L := Q.invertible.toAlgebraicGeometry;
            (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))))).hom ≫
      (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ T' x' hx' hs').hom := by
  intro hsq
  subst e
  have e : ∀ M : Modules.{u, u} B S hS X.1 X.2,
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x) ≪≫
        eqToIso (congrArg (fun k => modulePullback B S hS k) hk)).app M).hom =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app M :=
    fun M => (congrArg (_ ≫ ·)
      ((eqToHom_app (congrArg (fun k => modulePullback B S hS k) hk) M).trans
        (eqToHom_refl _ _))).trans (Category.comp_id _)
  exact (congrArg (_ ≫ ·) (e _)).trans
    ((sectionConormalPointIsoOf_baseChange X E hE Q hb σ hσ s hQ x h hx hh hx' hs hs' hsq).trans
      (congrArg (· ≫ _) (e _).symm))

/-- The transitions of the chart restrictions, in the spelling of scheme points: the composition
comparison of Stacks 03LU at the represented morphism of charts and the point of the larger chart,
followed by the transport along the triangle of the charts. -/
theorem chartModuleRestrictionTransitions_hom_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleRestrictionTransitions B S hS X M f).hom =
      ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map f))
          (pointHom (X := X) U.1.hom) ≪≫
        eqToIso (congrArg (fun k => modulePullback B S hS k)
          (chartMap_comp_chartToSpace B S hS X f))).app M).hom :=
  rfl

/-- A relation `f' ≫ g' = k' ≫ m'` gives the same relation between heterogeneously equal
morphisms `f, g, k, m` with equal endpoints. -/
theorem _root_.CategoryTheory.comp_eq_comp_of_heq_of_obj_eq {𝒟 : Type*} [Category 𝒟]
    {A B C D A' B' C' D' : 𝒟} {f : A ⟶ B} {g : B ⟶ D} {k : A ⟶ C} {m : C ⟶ D} {f' : A' ⟶ B'}
    {g' : B' ⟶ D'} {k' : A' ⟶ C'} {m' : C' ⟶ D'} (hf : HEq f f') (hg : HEq g g')
    (hk : HEq k k') (hm : HEq m m') (H : f' ≫ g' = k' ≫ m') (hA : A = A') (hB : B = B')
    (hC : C = C') (hD : D = D') : f ≫ g = k ≫ m := by
  subst hA hB hC hD
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq hm
  exact H

/-! ### Glueing the chart isomorphisms -/

/-- **The chart isomorphisms of the conormal clause of Stacks 0B4I**, indexed by the étale scheme
charts of `X`, through a family `s` of source readings invertible at étale points. -/
def sectionConormalChartFamilyOf (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1))))) (hs : ∀ (T : BigFppfOver B S hS)
                (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (U : SmallEtale B S hS X.1) :
    (chartModuleRestriction B S hS X U).obj (sectionConormalSource X E Q) ≅
      (chartModuleRestriction B S hS X U).obj (sectionConormalTarget X E hE hb σ hσ) :=
  sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
    (isEtale_of_presheaf_etale B S hS U.2)
    (hs ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom (isEtale_of_presheaf_etale B S hS U.2))

/-- **The chart isomorphisms are compatible with the transitions of the chart restrictions**, the
glueing condition of Stacks 03LY, given the compatibility `hsq` of the source readings with base
change. -/
theorem sectionConormalChartFamilyOf_compat (s : ∀ (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1))))) (hs : ∀ (T : BigFppfOver B S hS)
                (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
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
      s T' (yoneda.map h ≫ x)) {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).map
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ U).hom ≫
      (chartModuleRestrictionTransitions B S hS X (sectionConormalTarget X E hE hb σ hσ) f).hom =
    (chartModuleRestrictionTransitions B S hS X (sectionConormalSource X E Q) f).hom ≫
      (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ V).hom := by
  refine CategoryTheory.comp_eq_comp_of_heq_of_obj_eq ?_ ?_ ?_ ?_
    (sectionConormalPointIsoOf_baseChange_of_eq X E hE Q hb σ hσ s hQ U.1.hom
      ((SmallEtale.toOver B S hS X.1).map f) V.1.hom (CostructuredArrow.w f.hom)
      (chartMap_comp_chartToSpace B S hS X f) (isEtale_of_presheaf_etale B S hS U.2)
      (isEtale_chartMap B S hS X f) (isEtale_of_presheaf_etale B S hS V.2)
      (hs _ _ (isEtale_of_presheaf_etale B S hS U.2))
      (hs _ _ (isEtale_of_presheaf_etale B S hS V.2))
      (hsq U.1.hom ((SmallEtale.toOver B S hS X.1).map f))) ?_ ?_ ?_ ?_
  · refine modulePullback_map_heq_of_heq ?_ ?_ _ _ ?_ ?_ ?_ _ _ ?_
    · exact rfl
    · exact rfl
    · exact HEq.rfl
    · exact HEq.rfl
    · exact HEq.rfl
    · exact HEq.rfl
  · exact heq_of_eq (chartModuleRestrictionTransitions_hom_eq X f _)
  · exact heq_of_eq (chartModuleRestrictionTransitions_hom_eq X f _)
  · exact HEq.rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl

/-- **The conormal isomorphism of Stacks 0B4I glued from the charts** (Stacks 03LY): through a
family `s` of source readings invertible at étale points and compatible with base change, there
is a unique isomorphism `Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ` restricting on every étale chart to the chart
isomorphism. -/
theorem existsUnique_sectionConormalIso_of (s : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1))))) (hs : ∀ (T : BigFppfOver B S hS)
                (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
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
      s T' (yoneda.map h ≫ x)) :
    ∃! φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ,
      ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ U).hom := by
  refine ⟨chartGlueIso (M := sectionConormalSource X E Q)
      (N := sectionConormalTarget X E hE hb σ hσ)
      (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ)
      (sectionConormalChartFamilyOf_compat X E hE Q hb σ hσ s hs hQ hsq),
    chartModuleRestriction_map_chartGlueIso_hom (M := sectionConormalSource X E Q)
      (N := sectionConormalTarget X E hE hb σ hσ)
      (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ)
      (sectionConormalChartFamilyOf_compat X E hE Q hb σ hσ s hs hQ hsq), ?_⟩
  intro φ hφ
  exact Iso.ext (hom_ext_of_chartModuleRestriction fun U => (hφ U).trans
    (chartModuleRestriction_map_chartGlueIso_hom (M := sectionConormalSource X E Q)
      (N := sectionConormalTarget X E hE hb σ hσ)
      (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ)
      (sectionConormalChartFamilyOf_compat X E hE Q hb σ hσ s hs hQ hsq) U).symm)

/-- **The reading of the chart isomorphisms**: on an étale chart `U`, the chart isomorphism read
on the scheme `U` is the source reading `s_U`, Stacks 0B3V at `s_U`, the identification of `s_U`
with the section of the fibre, and the inverse of the reading of the conormal module of that
section. -/
theorem zariskiReading_map_sectionConormalChartFamilyOf_hom (s : ∀ (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1),
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
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
              T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1))))) (hs : ∀ (T : BigFppfOver B S hS)
                (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (U : SmallEtale B S hS X.1) :
    (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).map
        (sectionConormalPointIsoOf X E hE Q hb σ hσ s hQ ((SmallEtale.toOver B S hS X.1).obj U)
          U.1.hom (isEtale_of_presheaf_etale B S hS U.2)
          (hs ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            (isEtale_of_presheaf_etale B S hS U.2))).hom =
      (sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ ((SmallEtale.toOver B S hS X.1).obj U)
        U.1.hom (isEtale_of_presheaf_etale B S hS U.2)
        (hs ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
          (isEtale_of_presheaf_etale B S hS U.2))).hom :=
  zariskiReading_map_sectionConormalPointIsoOf_hom X E hE Q hb σ hσ s hQ _ _ _ _

end Chart


/-! ### The conormal clause through the explicit source readings -/

section Explicit

/-- At an étale scheme point the kernel factor of the conormal source reading is invertible: the
inverse image along a flat morphism preserves kernels. -/
theorem isIso_kernelPointReadingHom_of_isEtale (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (hx : IsEtale B S hS x) : IsIso (kernelPointReadingHom X E hE Q T x) := by
  have := preservesZeroMorphisms_modulePullback B S hS (pointHom x)
  have hf := isFlat_smallEtaleRingedToposHom_of_isEtale B S hS (pointHom x) hx
  have h₁ : IsIso (kernelComparison Q.q (modulePullback B S hS (pointHom x))) := by
    rw [← modulePullbackKernelIso_hom (pointHom x) hf Q.q]; infer_instance
  have h₂ : IsIso (kernelComparison Q.q (modulePullback B S hS (pointHom x)) ≫
      (kernelPointBaseChangeIso X E Q T x).hom) := IsIso.comp_isIso
  have h₃ : IsIso ((zariskiReadingFunctor T).map (kernelComparison Q.q
      (modulePullback B S hS (pointHom x)) ≫ (kernelPointBaseChangeIso X E Q T x).hom)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h₂
  exact IsIso.comp_isIso' h₃ (Iso.isIso_hom _)

/-- At an étale scheme point the explicit reading of the conormal source is invertible. -/
theorem isIso_conormalSourcePointReading_of_isEtale (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
        Q.invertible.toAlgebraicGeometry
    IsIso (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj
        T).Modules) (iC := Scheme.Modules.instCategory)
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
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom) := by
  have hk := isIso_kernelPointReadingHom_of_isEtale X E hE Q T x hx
  refine IsIso.comp_isIso' ?_ ?_
  · exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _))
      (IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_hom _))
  · refine IsIso.comp_isIso' ?_ ?_
    · exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ hk) _
    · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)

variable (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

/-- **The conormal clause of Stacks 0B4I, given the monoidality `hc` of the base change of the
Zariski reading**: for the section `σ` corresponding to the invertible quotient `q : ℰ ⟶ ℒ`, there
is a unique isomorphism `Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}` whose restriction to every étale
scheme chart `U` of `X` is the chart isomorphism, the lift along the Zariski reading of: the
reading of the source `Ker(q_U) ⊗ ℒ_U^{⊗ -1}`, Stacks 0B3V on `U` at the section `s_U`, the
identification of `s_U` with the section of the fibre of Stacks 084B, and the reading of the
conormal module of that section (`zariskiReading_map_sectionConormalChartFamily_hom`). -/
theorem existsUnique_sectionConormalIso
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
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj
          T).presheaf,
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
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫ (monoidalTensorSheafTensorIso
          ((BigFppfOver.toScheme B S hS).obj T) ((zariskiReadingFunctor T).obj (N))
          ((zariskiReadingFunctor T).obj (M))).hom) ((Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
          ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
          ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫ (monoidalTensorSheafTensorIso
          ((BigFppfOver.toScheme B S hS).obj T') ((zariskiReadingFunctor T').obj
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))).hom))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q) :
    ∃! φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ,
      ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
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
          (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).hom :=
  existsUnique_sectionConormalIso_of X E hE Q hb σ hσ _ (fun T x hx =>
      isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ
    (fun x h => conormalSourcePointReading_baseChange X E hE Q x h (hc h))

/-- **The chart isomorphisms of the conormal clause read on the charts**: on an étale chart `U`
the chart isomorphism reads as the explicit source reading followed by Stacks 0B3V at `s_U`, the
identification of `s_U` with the section of the fibre, and the inverse of the reading of the
conormal module of that section. -/
theorem zariskiReading_map_sectionConormalChartFamily_hom
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (U : SmallEtale B S hS X.1) :
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ
        ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
    (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).map
        (sectionConormalPointIsoOf X E hE Q hb σ hσ
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
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom)) hQ
          ((SmallEtale.toOver B S hS X.1).obj U)
          U.1.hom (isEtale_of_presheaf_etale B S hS U.2)
          ((fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx)
              ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            (isEtale_of_presheaf_etale B S hS U.2))).hom =
      (@asIso _ _ _ _ ((fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
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
          ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom)
          ((fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx)
              ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            (isEtale_of_presheaf_etale B S hS U.2)) ≪≫
        sectionPointConormalIso X E hE hb σ hσ Q hQ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            ≪≫
        sectionPointConormalFibreIso X E hE hb σ hσ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            ≪≫
        (zariskiReadingConormalIso
          (sectionFibreLift X E hE hb σ hσ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom)).symm ≪≫
        ((zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).mapIso
          (sectionConormalChartIso X E hE hb σ hσ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
            (isEtale_of_presheaf_etale B S hS U.2))).symm).hom :=
  (zariskiReading_map_sectionConormalChartFamilyOf_hom X E hE Q hb σ hσ _
      (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).trans
    (congrArg Iso.hom (sectionConormalReadingIsoOf_eq X E hE Q hb σ hσ _ hQ _ _ _ _))

end Explicit

end AlgebraicGeometry.Space

end
