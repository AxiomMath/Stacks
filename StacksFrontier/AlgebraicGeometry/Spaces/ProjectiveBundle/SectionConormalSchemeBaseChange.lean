module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalScheme

/-!
# Base change of the conormal isomorphism of Stacks 0B3V at the scheme points of a section

Let `σ` be a section of the projective bundle `π : 𝐏(ℰ) ⟶ X` of a quasi-coherent module on an
algebraic space, corresponding to an invertible quotient `q : ℰ ⟶ ℒ`, let `x : T ⟶ X` be a scheme
point and `h : T' ⟶ T` a morphism of test objects, with `x' = x ∘ h` and `τ` the morphism of
schemes underlying `h`.  The section `s_{x'}` of `𝐏((x'^*ℰ)_Zar) ⟶ T'` lies over `s_x` along the
base-change morphism of projective bundles, the quotient `q_{x'}` is the pullback of `q_x` along
`τ`, and the conormal isomorphisms `Ker(q_x) ⊗ ℒ_x^{⊗ -1} ≅ 𝒞_{s_x}` of Stacks 0B3V are compatible
with this base change.

## Main definitions

* `AlgebraicGeometry.Space.sectionPointQuotientBaseChangeL`: `ℒ_{x'} ≅ τ^*ℒ_x`.

## Main results

* `AlgebraicGeometry.Space.sectionPointBundleSection_baseChange`: `s_{x'}` lies over `s_x`.
* `AlgebraicGeometry.Space.sectionPointQuotient_baseChange_q`: `q_{x'}` is `τ^*q_x`.
* `AlgebraicGeometry.Space.sectionPointConormalIso_baseChange`: the conormal isomorphisms commute
  with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

section SchemeSide

variable {Y Y' : Scheme.{u}} (r : Y' ⟶ Y) (F : Y.Modules) [F.IsQuasicoherent] (F' : Y'.Modules)
  [F'.IsQuasicoherent] (e : F' ≅ (Scheme.Modules.pullback r).obj F)

/-- The identification `situationProjectiveBundleIso` carries the base change of relative Proj
along `r^*Sym(ℱ) ≅ Sym(ℱ')` to the base-change morphism of projective bundles. -/
theorem situationProjectiveBundleIso_hom_comp_projectiveBundleBaseChange :
    (situationProjectiveBundleIso F').hom ≫
        Stacks.RelativeProj.projectiveBundleBaseChange r F F' e =
      Stacks.RelativeProj.Situation.relativeProjBaseChange
          (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (Stacks.SymGraded.schemeSheafGradedAlgebra F
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)))
          (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (Stacks.SymGraded.schemeSheafGradedAlgebra F'
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F')))
          r (symmetricPullbackSituationHom r F F' e)
          (fun m => isIso_symmetricPullbackSituationHom_app r F F' e m) ≫
        (situationProjectiveBundleIso F).hom :=
  (Category.id_comp _).trans (Category.comp_id _).symm

end SchemeSide

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)

/-- **The sections of Stacks 084B at two scheme points `g` and `g ∘ h` lie over each other** along
the base change of relative Proj. -/
theorem pointsEquivSections_baseChange {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T)
    (u : {u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      u ≫ (projectiveBundleπ X E hE hb).hom = g}) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T g
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
    (pointsEquivSections X E hE hb T' (yoneda.map h ≫ g)
        ⟨yoneda.map h ≫ u.1, (Category.assoc _ _ _).trans (congrArg (yoneda.map h ≫ ·) u.2)⟩).1 ≫
        Stacks.RelativeProj.Situation.relativeProjBaseChange
          (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T g))
          (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T' (yoneda.map h ≫ g)))
          ((BigFppfOver.toScheme B S hS).map h)
          (symmetricPullbackSituationHom ((BigFppfOver.toScheme B S hS).map h)
            (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
            (pointZariskiModuleBaseChangeIso X E hE g h))
          (fun m => isIso_symmetricPullbackSituationHom_app ((BigFppfOver.toScheme B S hS).map h)
            (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
            (pointZariskiModuleBaseChangeIso X E hE g h) m) =
      (BigFppfOver.toScheme B S hS).map h ≫ (pointsEquivSections X E hE hb T g u).1 := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
  have hA := toScheme_map_comp_sectionOfPoint X E hE hb g h u.1
    ((congrArg (u.1 ≫ ·) rfl).trans (u.2.trans (yoneda_map_id_comp_eq g).symm))
    (((Category.assoc _ _ _).trans (congrArg (yoneda.map h ≫ ·) u.2)).trans
      (yoneda_map_id_comp_eq _).symm)
  have hB := toScheme_map_projComparison_comp_pointProjIso X E hE hb g h
  exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    hB.symm)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hA.symm)))).trans
      (Category.assoc _ _ _)

variable (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb)
  (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X) (Q : InvertibleQuotient X E)

/-- The section `s_{x ∘ h}` is the section of Stacks 084B at the restriction of the point
`x ≫ σ` along `h`. -/
theorem sectionPointSection_comp {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    sectionPointSection X E hE hb σ hσ T' (yoneda.map h ≫ x) =
      pointsEquivSections X E hE hb T' (yoneda.map h ≫ x)
        ⟨yoneda.map h ≫ (x ≫ σ.hom), (Category.assoc _ _ _).trans (congrArg (yoneda.map h ≫ ·)
          (comp_section_comp (projectiveBundleπ X E hE hb).hom x
            (congrArg InducedCategory.Hom.hom hσ)))⟩ :=
  congrArg (pointsEquivSections X E hE hb T' (yoneda.map h ≫ x))
    (Subtype.ext (Category.assoc _ _ _))

/-- **The section `s_{x ∘ h}` lies over `s_x`** along the base-change morphism of projective
bundles `𝐏((x'^*ℰ)_Zar) ⟶ 𝐏((x^*ℰ)_Zar)`. -/
theorem sectionPointBundleSection_baseChange {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1 ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
          (pointZariskiModuleBaseChangeIso X E hE x h) =
      (BigFppfOver.toScheme B S hS).map h ≫ (sectionPointBundleSection X E hE hb σ hσ T x).1 := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  have h1 := pointsEquivSections_baseChange X E hE hb x h
    ⟨x ≫ σ.hom, comp_section_comp (projectiveBundleπ X E hE hb).hom x
      (congrArg InducedCategory.Hom.hom hσ)⟩
  have h2 := situationProjectiveBundleIso_hom_comp_projectiveBundleBaseChange
    ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T x)
    (pointZariskiModule X E T' (yoneda.map h ≫ x)) (pointZariskiModuleBaseChangeIso X E hE x h)
  refine (congrArg (· ≫ _) ((situationSectionsEquiv_apply_coe _ _).trans
    (congrArg (fun s => s.1 ≫ (situationProjectiveBundleIso _).hom)
      (sectionPointSection_comp X E hE hb σ hσ x h)))).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ?_)
  exact Category.assoc _ _ _


/-- The pullback `x^*ℒ` of the invertible module of `q` to a scheme point is quasi-coherent. -/
theorem isQuasicoherentOnSite_pointPullback_L (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    ((modulePullback B S hS (pointHom x)).obj Q.L).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertibleModule (yonedaSpace B S hS T) _
    (Q.baseChange (pointHom x) (Iso.refl _)).invertible

/-- **The identification `ℒ_{x ∘ h} ≅ τ^*ℒ_x`** of the invertible modules of `q_{x ∘ h}` and of
the pullback of `q_x`: the composition comparison of Stacks 03LU and the base change of the
Zariski reading. -/
def sectionPointQuotientBaseChangeL {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x)).L ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        (sectionPointQuotient X E hE Q T x).L :=
  (zariskiReadingFunctor T').mapIso ((modulePullbackCompIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
      (pointHom x)).app Q.L).symm ≪≫
    (zariskiReadingPullbackIso h _ (isQuasicoherentOnSite_pointPullback_L X E Q T x)).symm

/-- A functor `P'` equal to a composite `P₁ ⋙ P₂` up to the identification `c`, and a
comparison `z : R ⋙ τ ⟶ P₂ ⋙ R'` invertible at the relevant objects: the square of `q` under
`R' ∘ P'` and `τ ∘ R ∘ P₁`. -/
theorem map_comp_map_inv_app_comp_inv_eq {𝒞 𝒴 𝒟 𝒮 𝒮' : Type*} {_ : Category 𝒞}
    {_ : Category 𝒴} {_ : Category 𝒟} {_ : Category 𝒮} {_ : Category 𝒮'} (P₁' : 𝒞 ⥤ 𝒴)
    {P₁ : 𝒞 ⥤ 𝒴} (hP₁ : P₁' = P₁) {P₂ : 𝒴 ⥤ 𝒟} (P' : 𝒞 ⥤ 𝒟) {P'' : 𝒞 ⥤ 𝒟} (hP : P' = P'')
    (c : P₁ ⋙ P₂ ≅ P'')
    {R : 𝒴 ⥤ 𝒮} {R' : 𝒟 ⥤ 𝒮'} {τ : 𝒮 ⥤ 𝒮'} (z : R ⋙ τ ⟶ P₂ ⋙ R') {E L : 𝒞} (q : E ⟶ L)
    (hE : IsIso (z.app (P₁.obj E))) (hL : IsIso (z.app (P₁.obj L))) :
    R'.map (P'.map q) ≫ R'.map (eqToHom (congrArg (fun F : 𝒞 ⥤ 𝒟 => F.obj L) hP) ≫ c.inv.app L) ≫
        inv (z.app (P₁.obj L)) =
      (R'.map (eqToHom (congrArg (fun F : 𝒞 ⥤ 𝒟 => F.obj E) hP) ≫ c.inv.app E) ≫
        inv (z.app (P₁.obj E))) ≫
        eqToHom (congrArg (fun F : 𝒞 ⥤ 𝒴 => τ.obj (R.obj (F.obj E))) hP₁.symm) ≫
          τ.map (R.map (P₁'.map q)) ≫
            eqToHom (congrArg (fun F : 𝒞 ⥤ 𝒴 => τ.obj (R.obj (F.obj L))) hP₁) := by
  subst hP hP₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← R'.map_comp_assoc, c.inv.naturality q, Functor.comp_map, Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (z.naturality (P₁'.map q)).symm

/-- **The quotient `q_{x ∘ h}` is the pullback of `q_x` along `τ`**, through
`ℰ_{x ∘ h} ≅ τ^*ℰ_x` and `ℒ_{x ∘ h} ≅ τ^*ℒ_x`. -/
theorem sectionPointQuotient_baseChange_q {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x)).q ≫
        (sectionPointQuotientBaseChangeL X E hE Q x h).hom =
      (pointZariskiModuleBaseChangeIso X E hE x h).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointQuotient X E hE Q T x).q := by
  have hIL := isIso_zariskiReadingPullbackHom_app h ((modulePullback B S hS (pointHom x)).obj Q.L)
    (isQuasicoherentOnSite_pointPullback_L X E Q T x)
  have hIE := isIso_zariskiReadingPullbackHom_app h _
    (isQuasicoherentOnSite_pointPullback X E hE T x)
  have e : ∀ {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ X.1),
      (sectionPointQuotient X E hE Q T y).q =
        (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom y)).map Q.q) :=
    fun _ => (zariskiReadingFunctor _).congr_map (Category.id_comp _)
  have k := map_comp_map_inv_app_comp_inv_eq (modulePullback B S hS (pointHom x)) rfl
    (modulePullback B S hS (pointHom (yoneda.map h ≫ x))) rfl
    (modulePullbackCompIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T) (pointHom x))
    (zariskiReadingPullbackHom h) Q.q hIE hIL
  rw [eqToHom_refl, eqToHom_refl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.id_comp, Category.id_comp, Category.comp_id] at k
  rw [e, e]
  exact k

attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

/-- **The conormal isomorphisms of Stacks 0B3V at `s_x` and `s_{x ∘ h}` are compatible with base
change along `τ`**: the instance at the scheme points of `σ` of
`Stacks.RelativeProj.projectiveBundleConormalIso_baseChange`. -/
theorem sectionPointConormalIso_baseChange
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T x).1
      (sectionPointBundleSection X E hE hb σ hσ T x).2
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1
      (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
    (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).hom ≫
        (sectionPointConormalIso X E hE hb σ hσ Q hQ T' (yoneda.map h ≫ x)).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointConormalIso X E hE hb σ hσ Q hQ T x).hom ≫
        Stacks.Conormal.conormalBaseChangeMap
          (sectionPointBundleSection_baseChange X E hE hb σ hσ x h) :=
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  Stacks.RelativeProj.projectiveBundleConormalIso_baseChange ((BigFppfOver.toScheme B S hS).map h)
    (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
    (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
    (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
    (sectionPointQuotientBaseChangeL X E hE Q x h)
    (sectionPointQuotient_baseChange_q X E hE Q x h)
    (sectionPointBundleSection X E hE hb σ hσ T x).2
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T x).choose
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T x).choose_spec
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T' (yoneda.map h ≫ x)).choose
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T' (yoneda.map h ≫ x)).choose_spec
    (sectionPointBundleSection_baseChange X E hE hb σ hσ x h)

end AlgebraicGeometry.Space

end
