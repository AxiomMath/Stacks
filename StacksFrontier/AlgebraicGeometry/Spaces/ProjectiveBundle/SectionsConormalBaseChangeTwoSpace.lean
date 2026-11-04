module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeGlue

/-!
# The two-space squares of the conormal isomorphism of Stacks 0B4I at the scheme points

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`, and let `τ` be the morphism of schemes underlying `h`.
The Zariski reading `(v^*g^*ℰ)_Zar` of the base change is `τ^*(u^*ℰ)_Zar`, and likewise for the
invertible quotient `q` of `ℰ`.  This file proves that the conormal isomorphisms of Stacks 0B3V
at the sections `s_u` and `s'_v` and the identifications of their conormal sheaves with those of
the sections `k_u`, `k'_v` of the fibres of Stacks 084B are compatible with these
identifications, given the compatibility of the fibre identifications with the comparison of
fibres, and reduces `AlgebraicGeometry.Space.ConormalChartSourceCompat` to the compatibility
of the source readings with the base change of the conormal source.

## Main definitions

* `AlgebraicGeometry.Space.pointPullbackCompIso`: `v^*g^* ≅ (u ∘ h)^*`.
* `AlgebraicGeometry.Space.pointZariskiModuleTwoSpaceIso`: `(v^*g^*ℰ)_Zar ≅ τ^*(u^*ℰ)_Zar`.
* `AlgebraicGeometry.Space.sectionPointQuotientTwoSpaceL`: the same for the invertible modules.

## Main results

* `AlgebraicGeometry.Space.sectionPointQuotient_twoSpace_q`: the quotient maps correspond.
* `AlgebraicGeometry.Space.sectionPointConormalIso_twoSpace`: the square of the conormal
  isomorphisms of Stacks 0B3V.
* `AlgebraicGeometry.Space.sectionPointConormalFibreIso_twoSpace`: the square of the fibre
  identifications.
* `AlgebraicGeometry.Space.conormalChartSourceCompat_of_twoSpace`: the reduction of
  `ConormalChartSourceCompat` to the source square.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- The paste of a source square, a square of conormal isomorphisms and a square of fibre
identifications. -/
theorem CategoryTheory.comp_conormalTwoSpace_paste {𝒞 : Type*} [Category 𝒞]
    {A Pa P₁ P₂ P₃ Z W b₁ b₂ : 𝒞} (x : A ⟶ Pa) (sP : Pa ⟶ P₁) (θP : P₁ ⟶ P₂) (FP : P₂ ⟶ P₃)
    (c : P₃ ⟶ Z) (cs : P₁ ⟶ b₁) (cb : P₂ ⟶ b₂) (y : A ⟶ W) (s' : W ⟶ b₁) (θ' : b₁ ⟶ b₂)
    (F' : b₂ ⟶ Z) (hΘ : cs ≫ θ' = θP ≫ cb) (hF : cb ≫ F' = FP ≫ c)
    (hS : x ≫ sP ≫ cs = y ≫ s') :
    x ≫ sP ≫ θP ≫ FP ≫ c = y ≫ s' ≫ θ' ≫ F' := by
  rw [← hF, ← reassoc_of% hΘ, ← reassoc_of% hS]

/-- Two squares pasted along a common edge `m`. -/
theorem CategoryTheory.comp_comp_eq_of_comp_eq {𝒞 : Type*} [Category 𝒞] {A B₁ B₂ C₁ D : 𝒞}
    (a : A ⟶ B₁) (b : B₁ ⟶ C₁) (c : C₁ ⟶ D) (d : A ⟶ B₂) (m : B₂ ⟶ C₁) {B₃ : 𝒞} (e : B₂ ⟶ B₃)
    (f : B₃ ⟶ D) (n : a ≫ b = d ≫ m) (k : m ≫ c = e ≫ f) : a ≫ b ≫ c = (d ≫ e) ≫ f := by
  rw [← Category.assoc, n, Category.assoc, k, Category.assoc]

/-- Two squares `a' ≫ kb = kp ≫ a` and `k' ≫ kp = r ≫ k`, pasted. -/
theorem CategoryTheory.comp_comp_square_paste {𝒞 : Type*} [Category 𝒞] {A A' P P' Q Q' : 𝒞}
    (k' : A' ⟶ P') (a' : P' ⟶ Q') (kb : Q' ⟶ Q) (kp : P' ⟶ P) (a : P ⟶ Q) (r : A' ⟶ A)
    (k : A ⟶ P) (hk : a' ≫ kb = kp ≫ a) (hc : k' ≫ kp = r ≫ k) :
    (k' ≫ a') ≫ kb = r ≫ k ≫ a := by
  rw [Category.assoc, hk, ← Category.assoc, hc, Category.assoc]

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)

/-- **The comparison `v^*g^* ≅ (u ∘ h)^*`** of the inverse images along the two factorizations
of the point `v ≫ g = u ∘ h` (Stacks 03LU). -/
def pointPullbackCompIso :
    modulePullback B S hS g ⋙ modulePullback B S hS (pointHom v) ≅
      modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u)) :=
  modulePullbackCompIso B S hS (pointHom v) g ≪≫
    eqToIso (congrArg (modulePullback B S hS)
      (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = pointHom (X := X) (yoneda.map h ≫ u)))

/-- **The Zariski reading of the base change at `v` is the inverse image of the Zariski reading
at `u`**: `(v^*g^*ℰ)_Zar ≅ τ^*(u^*ℰ)_Zar`, for `v ≫ g = u ∘ h`. -/
def pointZariskiModuleTwoSpaceIso :
    pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        (pointZariskiModule X E T u) :=
  (zariskiReadingFunctor T').mapIso ((pointPullbackCompIso X g u v h hvh).app E) ≪≫
    pointZariskiModuleBaseChangeIso X E hE u h

variable (Q : InvertibleQuotient X E)

/-- **The invertible module of `q'_v` is the inverse image of that of `q_u`**, for the base
change `q' = g^*q` and `v ≫ g = u ∘ h`. -/
def sectionPointQuotientTwoSpaceL :
    (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T' v).L ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        (sectionPointQuotient X E hE Q T u).L :=
  (zariskiReadingFunctor T').mapIso ((pointPullbackCompIso X g u v h hvh).app Q.L) ≪≫
    sectionPointQuotientBaseChangeL X E hE Q u h

/-- **The quotient `q'_v` is the inverse image of `q_u`**, through
`pointZariskiModuleTwoSpaceIso` and `sectionPointQuotientTwoSpaceL`. -/
theorem sectionPointQuotient_twoSpace_q :
    (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T' v).q ≫
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q).hom =
      (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointQuotient X E hE Q T u).q := by
  have e1 : (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      (Q.baseChange g (Iso.refl _)) T' v).q =
      (zariskiReadingFunctor T').map ((modulePullback B S hS g ⋙
        modulePullback B S hS (pointHom v)).map Q.q) :=
    (zariskiReadingFunctor T').congr_map ((Category.id_comp _).trans
      ((modulePullback B S hS (pointHom v)).congr_map (Category.id_comp _)))
  have e2 : (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u)).q =
      (zariskiReadingFunctor T').map
        ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).map Q.q) :=
    (zariskiReadingFunctor T').congr_map (Category.id_comp _)
  have n : (zariskiReadingFunctor T').map ((modulePullback B S hS g ⋙
        modulePullback B S hS (pointHom v)).map Q.q) ≫
        (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app Q.L) =
      (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app E) ≫
        (zariskiReadingFunctor T').map
          ((modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).map Q.q) :=
    ((zariskiReadingFunctor T').map_comp _ _).symm.trans
      ((congrArg (zariskiReadingFunctor T').map
        ((pointPullbackCompIso X g u v h hvh).hom.naturality Q.q)).trans
        ((zariskiReadingFunctor T').map_comp _ _))
  have k := sectionPointQuotient_baseChange_q X E hE Q u h
  rw [e2] at k
  rw [e1]
  change _ ≫ ((zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app Q.L) ≫
    (sectionPointQuotientBaseChangeL X E hE Q u h).hom) =
    ((zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app E) ≫
      (pointZariskiModuleBaseChangeIso X E hE u h).hom) ≫ _
  exact CategoryTheory.comp_comp_eq_of_comp_eq _ _ _ _ _ _ _ n k

variable (hb : SymmetricAlgebraBounded X E)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')

/-- **The conormal isomorphisms of Stacks 0B3V at `s_u` and `s'_v` are compatible with the
two-space base change**, for sections lying over each other along the base-change morphism of
projective bundles of `pointZariskiModuleTwoSpaceIso`. -/
theorem sectionPointConormalIso_twoSpace
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ = Quotient.mk
        _ (Q.baseChange g (Iso.refl _)))
    (hsec : haveI := isQuasicoherent_pointZariskiModule X E hE T u
      haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1 ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map h ≫ (sectionPointBundleSection X E hE hb σ hσ T u).1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T u).1
      (sectionPointBundleSection X E hE hb σ hσ T u).2
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).2
    (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom ≫
        (sectionPointConormalIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
            (Q.baseChange g (Iso.refl _)) hQ' T' v).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointConormalIso X E hE hb σ hσ Q hQ T u).hom ≫
        Stacks.Conormal.conormalBaseChangeMap hsec :=
  have := isQuasicoherent_pointZariskiModule X E hE T u
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  Stacks.RelativeProj.projectiveBundleConormalIso_baseChange ((BigFppfOver.toScheme B S hS).map h)
    (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
    (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
    (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T' v)
    (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
    (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)
    (sectionPointBundleSection X E hE hb σ hσ T u).2
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T u).choose
    (exists_sectionPointQuotient_iso X E hE hb σ hσ Q hQ T u).choose_spec
    (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).2
    (exists_sectionPointQuotient_iso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
        (Q.baseChange g (Iso.refl _)) hQ' T' v).choose
    (exists_sectionPointQuotient_iso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
        (Q.baseChange g (Iso.refl _)) hQ' T' v).choose_spec
    hsec

variable (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)

include comm in
/-- **The section `s'_v` lies over `s_u`** along the base-change morphism of projective bundles
of `pointZariskiModuleTwoSpaceIso`, given that the identifications of the fibres with the
projective bundles are compatible with the comparison of fibres. -/
theorem sectionPointBundleSection_twoSpace
    (hk : haveI := isQuasicoherent_pointZariskiModule X E hE T u
      haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
      (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map
          (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
        (pointFibreProjectiveBundleIso X E hE hb T u).hom) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1 ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map h ≫ (sectionPointBundleSection X E hE hb σ hσ T u).1 :=
  have := isQuasicoherent_pointZariskiModule X E hE T u
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  (congrArg (· ≫ Stacks.RelativeProj.projectiveBundleBaseChange
      ((BigFppfOver.toScheme B S hS).map h)
      (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
      (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh))
    (sectionPointBundleSection_eq X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)).trans
    ((CategoryTheory.comp_comp_square_paste _ _ _ _ _ _ _ hk
      (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh
        σ hσ σ' hσ' comm)).trans
      (congrArg ((BigFppfOver.toScheme B S hS).map h ≫ ·)
        (sectionPointBundleSection_eq X E hE hb σ hσ T u).symm))

/-- **The identifications of the conormal sheaves of `s_u`, `k_u` and of `s'_v`, `k'_v` are
compatible with the two-space base change**: the base-change maps of conormal sheaves of the
squares of sections `s'_v, s_u` and `k'_v, k_u` intertwine `sectionPointConormalFibreIso`, given
that the identifications of the fibres are compatible with the comparison of fibres. -/
theorem sectionPointConormalFibreIso_twoSpace
    (hk : haveI := isQuasicoherent_pointZariskiModule X E hE T u
      haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
      (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map
          (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
        (pointFibreProjectiveBundleIso X E hE hb T u).hom)
    (hsec : haveI := isQuasicoherent_pointZariskiModule X E hE T u
      haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1 ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map h ≫ (sectionPointBundleSection X E hE hb σ hσ T u).1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T u).1
      (sectionPointBundleSection X E hE hb σ hσ T u).2
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1
      (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).2
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
    haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
    Stacks.Conormal.conormalBaseChangeMap hsec ≫
        (sectionPointConormalFibreIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointConormalFibreIso X E hE hb σ hσ T u).hom ≫
        Stacks.Conormal.conormalBaseChangeMap
          (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g
              hb' u v h hvh
            σ hσ σ' hσ' comm) := by
  have := isQuasicoherent_pointZariskiModule X E hE T u
  have := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T u).1
    (sectionPointBundleSection X E hE hb σ hσ T u).2
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).1
    (sectionPointBundleSection X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).2
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
  have := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
  unfold sectionPointConormalFibreIso
  refine Stacks.Conormal.conormalUnitSquareIso_baseChange _ _ _ _ _ ?_
  exact hk

/-- **The compatibility of the source readings along `h` from the two-space squares**: given the
compatibility of the fibre identifications with the comparison of fibres (`hk`) and the
compatibility `hsrc` of the source readings `s_u`, `s'_v` with the base change of the conormal
source of Stacks 0B3V along `pointZariskiModuleTwoSpaceIso`, the source readings, the conormal
isomorphisms of Stacks 0B3V and the fibre identifications satisfy
`ConormalChartSourceCompat`. -/
theorem conormalChartSourceCompat_of_twoSpace
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ = Quotient.mk
        _ (Q.baseChange g (Iso.refl _)))
    (s : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj
          (haveI : IsInvertible (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L := Q.invertible.toAlgebraicGeometry;
            (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
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
            (sectionPointQuotient X E hE Q T x).L (-1))))))
    (s' : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1),
      (zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj
          (haveI : IsInvertible (structureCommRings B S hS X')
              (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L :=
              (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
            (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
              (kernel (Q.baseChange g (Iso.refl _)).q)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))) ⟶
      (letI := (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
              (kernel (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
              ((BigFppfOver.toScheme B S hS).obj T).presheaf
              ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
                (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
                (Q.baseChange g (Iso.refl _)) T x).L (-1))))))
    (hk : haveI := isQuasicoherent_pointZariskiModule X E hE T u
      haveI := isQuasicoherent_pointZariskiModule X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) T' v
      (pointFibreProjectiveBundleIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' T' v).hom ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T u)
              (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
          (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) =
      (BigFppfOver.toScheme B S hS).map
          (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
        (pointFibreProjectiveBundleIso X E hE hb T u).hom)
    (hsrc : (CategoryTheory.Functor.conormalGlueComparison
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T')
        (Ku := ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q)))
        (Kx := ((modulePullback B S hS (pointHom v)).obj
        ((modulePullback B S hS g).obj (sectionConormalSource X E Q))))
        (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
        ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q))))
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫ eqToIso
        (congrArg (modulePullback B S hS)
        (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫
        (modulePullbackCompIso B S hS (pointHom v) g).symm).inv.app (sectionConormalSource X E Q))
        (zariskiReadingPullbackIso h
        ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u)
        (sectionConormalSource X E Q)
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q))).inv) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map (s T u) ≫
        (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (sectionConormalSourceBaseChangeHom X E Q g)) ≫ s' T' v) :
    ConormalChartSourceCompat X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
      (sectionConormalSourceBaseChangeHom X E Q g) (s T u)
      (sectionPointConormalIso X E hE hb σ hσ Q hQ T u)
      (sectionPointConormalFibreIso X E hE hb σ hσ T u) (s' T' v)
      (sectionPointConormalIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
          (Q.baseChange g (Iso.refl _)) hQ' T' v)
      (sectionPointConormalFibreIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) :=
  ⟨CategoryTheory.comp_conormalTwoSpace_paste _ _ _ _ _ _ _ _ _ _ _
    (sectionPointConormalIso_twoSpace X E hE g u v h hvh Q hb hb' σ hσ σ' hσ' hQ hQ'
      (sectionPointBundleSection_twoSpace X E hE g u v h hvh hb hb' σ hσ σ' hσ' comm hk))
    (sectionPointConormalFibreIso_twoSpace X E hE g u v h hvh hb hb' σ hσ σ' hσ' comm hk
      (sectionPointBundleSection_twoSpace X E hE g u v h hvh hb hb' σ hσ σ' hσ' comm hk)) hsrc⟩

end AlgebraicGeometry.Space

end
