module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSquare

/-!
# The homomorphism `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` of Stacks 084D

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084B,
`X = U/R` a presentation of its base and `P = P_U/P_R` the induced presentation of `P`.  On the
atlas `c : P_U ⟶ P` the source `π^*𝒜_n` of `ψ` is identified with the module attached to
`π_U^*(u^*𝒜)_n`, and `ψ` of Tag 01NR gives a morphism `c^*(π^*𝒜_n) ⟶ 𝒪(n)^a`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint`).  This file proves that this
morphism is compatible with the descent data, and descends it to the homomorphism
`ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` of Stacks 084D (`n ≥ 0`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`: **the homomorphism
  `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` of Stacks 084D.**

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChainIso_hom_eq_comp₂`: the
  identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of the sources of `ψ` as a chain of
  contractions and the comparison of restrictions of Stacks 084A.
* `modulePullback_map_psiChartSourceIso_hom_comp₂_eq` (in
  `AlgebraicGeometry.Space.RelativeProjSituation`): the chart square of the source of `ψ` along a
  morphism of the presentation lying over a morphism of the relation.
* `AlgebraicGeometry.Space.RelativeProjSituation.transitionCommutes_psiChartHomOfAdjoint`: **`ψ` on
  the atlas carries the canonical transition of `π^*𝒜_n` to the transition of `𝒪(n)`.**
* `modulePullback_map_psiTwistHom_comp_twistModuleChartIso_hom` (in
  `AlgebraicGeometry.Space.RelativeProjSituation`)
  and `…eq_psiTwistHom`: `ψ_n` is the unique morphism which is `ψ` on the atlas.

## Implementation notes

The compatibility is assembled on the represented projections `R ×_X P ⇉ U ×_X P` of the site
and transported to the groupoid of the presentation at free variables
(`AlgebraicGeometry.Space.RelativeProjPoints.transitionCommutes_spaceBaseDescent_of_represented`):
the kernel does not compare in reasonable time an inverse image along the source of the groupoid
with one along the represented source projection.  All terms in Situation 0849 are written over
the site of the situation (`(B := s.site)` for the restrictions of the shrunk algebra), so that
they agree syntactically with the instances of the generic identities, and the inverse images are
taken over the represented algebraic spaces `⟨yoneda.obj _, _⟩`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification of the pullbacks of a quasi-coherent module along two equal morphisms of
the site is the identification of the inverse images of modules on schemes along the equal
morphisms of schemes. -/
theorem eqToHom_hom_eq_pullbackCongr_hom_app {W U : BigFppfOver B S hS} {g₁ g₂ : W ⟶ U}
    (h : g₁ = g₂)
    (h' : (BigFppfOver.toScheme B S hS).map g₁ = (BigFppfOver.toScheme B S hS).map g₂)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (eqToHom (congrArg (fun g => quasicoherentPullbackObj B S hS g N) h)).hom =
      (Scheme.Modules.pullbackCongr h').hom.app N.obj := by
  subst h
  rfl

/-- **The comparison along a commutative square of the site, as a chain of quasi-coherent
modules**: for `y ≫ f_U = f_R ≫ k` and `T : k^*N_U ≅ N_R`, the comparison
`y^*f_U^*N_U ≅ f_R^*N_R` along the square (`AlgebraicGeometry.Space.pullbackIsoOfSquare`) is the
contraction `y^*f_U^* ≅ (y ≫ f_U)^*`, the identification along `y ≫ f_U = f_R ≫ k`, the inverse
of the contraction `f_R^*k^* ≅ (f_R ≫ k)^*` and the pullback along `f_R` of the morphism `t` of
`T`. -/
theorem isoMk_pullbackIsoOfSquare_hom_eq_comp₂ {W V U R : BigFppfOver B S hS} (y : W ⟶ V)
    (fU : V ⟶ U) (fR : W ⟶ R) (k : R ⟶ U) (e : y ≫ fU = fR ≫ k)
    (e₂ : (BigFppfOver.toScheme B S hS).map y ≫ (BigFppfOver.toScheme B S hS).map fU =
      (BigFppfOver.toScheme B S hS).map fR ≫ (BigFppfOver.toScheme B S hS).map k)
    (NU : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    (NR : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory)
    (T : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj NU.obj ≅ NR.obj)
    (t : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj NU.obj ⟶ NR.obj)
    (ht : T.hom = t) :
    (ObjectProperty.isoMk _ (pullbackIsoOfSquare ((BigFppfOver.toScheme B S hS).map fU)
        ((BigFppfOver.toScheme B S hS).map fR) ((BigFppfOver.toScheme B S hS).map y)
        ((BigFppfOver.toScheme B S hS).map k) e₂ T) :
        quasicoherentPullbackObj B S hS y (quasicoherentPullbackObj B S hS fU NU) ≅
          quasicoherentPullbackObj B S hS fR NR).hom =
      comp₂ (quasicoherentPullbackCompIso B S hS y fU NU).hom
        (comp₂ (eqToHom (congrArg (fun g => quasicoherentPullbackObj B S hS g NU) e :
            quasicoherentPullbackObj B S hS (y ≫ fU) NU =
              quasicoherentPullbackObj B S hS (fR ≫ k) NU))
          (comp₂ (quasicoherentPullbackCompIso B S hS fR k NU).inv
            (quasicoherentPullbackMap B S hS fR
              (ObjectProperty.homMk t : quasicoherentPullbackObj B S hS k NU ⟶ NR)))) := by
  subst ht
  ext1
  rw [comp₂_eq, comp₂_eq, comp₂_eq, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    eqToHom_hom_eq_pullbackCongr_hom_app e e₂]
  rfl

/-- The images under a functor into a full subcategory of the two morphisms of an isomorphism
compose to the identity, as named binary composites. -/
theorem map_hom_comp₂_map_inv_hom {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {X Y : C} (e : X ≅ Y) :
    comp₂ (F.map (Iso.hom (X := X) (Y := Y) e)).hom (F.map (Iso.inv (X := X) (Y := Y) e)).hom =
      𝟙 _ := by
  rw [comp₂_eq, ← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp, e.hom_inv_id,
    F.map_id]
  rfl

/-- A composite `C_t ≫ F(f ≫ g) ≫ C_s⁻¹`, with the image of `f ≫ g` under a functor into a full
subcategory split, as named binary composites. -/
theorem eq_comp₂_map_comp₂_map_of_eq {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {X Y Z : C} {A₀ A₁ : D}
    (Ct : A₀ ≅ (F.obj X).obj) (Cs : A₁ ≅ (F.obj Z).obj) (f : X ⟶ Y) (g : Y ⟶ Z) (τ : A₀ ⟶ A₁)
    (hτ : τ = Ct.hom ≫ (F.map (f ≫ g)).hom ≫ Cs.inv) :
    τ = comp₂ Ct.hom (comp₂ (F.map f).hom (comp₂ (F.map g).hom Cs.inv)) := by
  subst hτ
  rw [comp₂_eq, comp₂_eq, comp₂_eq, F.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc]

/-- An identity `a ≫ b ≫ c ≫ d = e ≫ f ≫ g` written with named binary composites. -/
theorem comp₂_comp₂_comp₂_eq_of_eq {C : Type*} [Category C] {X Y₁ Y₂ Y₃ Z Y₁' Y₂' : C}
    {a : X ⟶ Y₁} {b : Y₁ ⟶ Y₂} {c : Y₂ ⟶ Y₃} {d : Y₃ ⟶ Z} {e : X ⟶ Y₁'} {f : Y₁' ⟶ Y₂'}
    {g : Y₂' ⟶ Z} (h : a ≫ b ≫ c ≫ d = e ≫ f ≫ g) :
    comp₂ a (comp₂ b (comp₂ c d)) = comp₂ e (comp₂ f g) :=
  h

end Generic

namespace RelativeProjPoints

section ChartSquare

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)

/-- A morphism `y : R ×_X P ⟶ U ×_X P` lying over `k : R ⟶ U`, followed by the atlas `c` of the
    presentation of `P` and by `π`, is the structure morphism of `R ×_X P` followed by
the point `r` of `X`, as morphisms of algebraic spaces. -/
theorem comp_presentationAtlas_comp_homMk_of_liesOver {k : Px.R ⟶ Px.U}
    (y : d.fibre Px.R (relationPoint Px) ⟶ d.fibre Px.U Px.toSpace) (hy : d.LiesOver y k) :
    CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Y :=
        (⟨P, hP⟩ : AlgebraicSpaces B S hS))
        (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z :=
            (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (representedSpaceMap B S hS y) (presentationAtlas
                (d.spacePresentation Px hP))) (ObjectProperty.homMk π :
                    (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS
          (d.fibreHom Px.R (relationPoint Px))) (pointHom (relationPoint Px)) :=
  ObjectProperty.hom_ext _ ((congrArg (· ≫ π) hy.2).trans (d.isPullback Px.R (relationPoint Px)).w)

/-- The target and the source projections of the presentation of `P` have the same composite with
its atlas, as represented morphisms. -/
theorem representedSpaceMap_spaceTarget_comp_presentationAtlas :
    CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z := (⟨P, hP⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (d.spaceTarget Px hP))
        (presentationAtlas (d.spacePresentation Px hP)) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z := (⟨P, hP⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (d.spaceSource Px hP))
        (presentationAtlas (d.spacePresentation Px hP)) :=
  presentationAtlas_comm _

/-- **A transition compatibility on the groupoid of the presentation of `P`, from the represented
projections**: `AlgebraicGeometry.Space.TransitionCommutes` for the canonical transition morphism
of the inverse image of `Y` along the atlas and the transition `τ^a`, stated on the represented
projections `R ×_X P ⇉ U ×_X P`, is the same statement on the groupoid of the presentation (the
hypothesis of `AlgebraicGeometry.Space.presentationDescendedIntoHom`). -/
theorem transitionCommutes_spaceBaseDescent_of_represented
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
    (τ : quasicoherentPullbackObj B S hS (d.spacePresentation Px hP).target M ⟶
      quasicoherentPullbackObj B S hS (d.spacePresentation Px hP).source M)
    (Y : QuasicoherentSheaves.{u, u} B S hS (⟨P, hP⟩ : AlgebraicSpaces B S hS).obj
      (⟨P, hP⟩ : AlgebraicSpaces B S hS).property)
    (χ : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj Y.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS
        (d.spacePresentation Px hP).U).functor.obj M).obj)
    (h : TransitionCommutes B S hS
      (U := ⟨yoneda.obj (d.fibre Px.U Px.toSpace),
        isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩)
      (V := ⟨yoneda.obj (d.fibre Px.R (relationPoint Px)),
        isAlgebraicSpace_yoneda B S hS (d.fibre Px.R (relationPoint Px))⟩)
      (a := representedSpaceMap B S hS (d.spaceTarget Px hP))
      (b := representedSpaceMap B S hS (d.spaceSource Px hP))
      (modulePullbackUnflatten (X := ⟨yoneda.obj (d.fibre Px.R (relationPoint Px)),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.R (relationPoint Px))⟩)
        (Y := ⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩)
        (a := representedSpaceMap B S hS (d.spaceTarget Px hP))
        (b := representedSpaceMap B S hS (d.spaceSource Px hP))
        (presentationAtlas (d.spacePresentation Px hP))
        (pullbackTransport (T := ⟨yoneda.obj (d.fibre Px.R (relationPoint Px)),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.R (relationPoint Px))⟩)
          (X := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) Y.obj
          (d.representedSpaceMap_spaceTarget_comp_presentationAtlas Px hP)))
      (presentationSchemeTransition (d.spacePresentation Px hP) M τ) χ) :
    TransitionCommutes B S hS (U := (presentationGroupoid (d.spacePresentation Px hP)).objects)
      (V := (presentationGroupoid (d.spacePresentation Px hP)).arrows)
      (a := (presentationGroupoid (d.spacePresentation Px hP)).target)
      (b := (presentationGroupoid (d.spacePresentation Px hP)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (d.spacePresentation Px hP))
        (presentationAtlas (d.spacePresentation Px hP))
        (presentationAtlas_comm (d.spacePresentation Px hP)) Y.obj)
      (presentationSchemeTransition (d.spacePresentation Px hP) M τ) χ :=
  h

end ChartSquare

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

section Chain

variable {U V : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
  {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U) (hv : yoneda.map k ≫ u = v)
  (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
  (hy : s.relativeProjPoints.LiesOver y k)

omit y hy in
/-- The comparison of the restrictions of Stacks 084A in Situation 0849 shrunk to the universe
`u`, in degree `n`, is the comparison of restrictions of its graded algebra
(`AlgebraicGeometry.Space.pointComparison`), read over the site of Situation 0849. -/
theorem pointComparisonUnital_shrink_app_eq (n : ℤ) :
    (pointComparisonUnital (s := s.shrink) k u v hv).app n =
      (pointComparison (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := s.space) s.shrink.algebra k u v hv).app n :=
  (rfl : (pointComparisonUnital (s := s.shrink) k u v hv).app n =
    (pointComparison s.shrink.algebra k u v hv).app n).trans
    (rfl : (pointComparison s.shrink.algebra k u v hv).app n =
      (pointComparison (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := s.space) s.shrink.algebra k u v hv).app n)

omit y hy in
/-- The comparison of the restrictions of Stacks 084A in Situation 0849 shrunk to the universe
`u`, in degree `n`, as an isomorphism of the Zariski readings over the site of Situation 0849, is
the comparison of restrictions of its graded algebra
(`AlgebraicGeometry.Space.pointComparison`). -/
theorem asIso_pointComparisonUnital_shrink_app_hom (n : ℤ) :
    (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k u v hv).app n)
        (isIso_pointComparisonUnital_app (s := s.shrink) k u v hv n) :
      (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)).obj
          (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra U u).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent u
              n)).obj ≅
        (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra V v).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent v
            n)).obj).hom =
      (pointComparison (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := s.space) s.shrink.algebra k u v hv).app n :=
  s.pointComparisonUnital_shrink_app_eq k hv n

/-- **The identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of the sources of `ψ` as a chain**:
the contraction along `y`, the identification along `y ≫ π_U = π_V ≫ k`, the inverse of the
contraction along `k`, and the pullback along `π_V` of the comparison `k^*(u^*𝒜)_n ⟶ (v^*𝒜)_n` of
the restrictions of Stacks 084A. -/
theorem pointPieceChainIso_hom_eq_comp₂ (n : ℤ) :
    Iso.hom (X := quasicoherentPullbackObj s.site s.base s.containsBase y
        (quasicoherentPullbackObj s.site s.base s.containsBase (s.relativeProjPoints.fibreHom U u)
          (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
              s.shrink.isQuasicoherent u n))))
      (Y := quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom V v) (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site)
            (S := s.base) (hS := s.containsBase) (X := s.space)
        s.shrink.algebra V v).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
              s.shrink.isQuasicoherent v n)))
      (s.pointPieceChainIso k hv y hy n) =
      comp₂ (quasicoherentPullbackCompIso s.site s.base s.containsBase y
          (s.relativeProjPoints.fibreHom U u)
          (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
              s.shrink.isQuasicoherent u n))).hom
        (comp₂ (eqToHom (congrArg (fun g => quasicoherentPullbackObj s.site s.base s.containsBase
            g (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                s.shrink.isQuasicoherent u n))) hy.1 :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (y ≫ s.relativeProjPoints.fibreHom U u)
                (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
                    (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
                  (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                    s.shrink.isQuasicoherent u n)) =
              quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom V v ≫ k)
                (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
                    (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
                  (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                    s.shrink.isQuasicoherent u n))))
          (comp₂ (quasicoherentPullbackCompIso s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom V v) k
              (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
                (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                    (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                  s.shrink.isQuasicoherent u n))).inv
            (quasicoherentPullbackMap s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom V v)
              (ObjectProperty.homMk ((pointComparison (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space) s.shrink.algebra k u v hv).app n) :
                quasicoherentPullbackObj s.site s.base s.containsBase k
                    (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base)
                        (hS := s.containsBase) (X := s.space)
        s.shrink.algebra U u).piece n)
                      (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                          (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                        s.shrink.isQuasicoherent u n)) ⟶
                  zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
        s.shrink.algebra V v).piece n)
                    (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                        (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                      s.shrink.isQuasicoherent v n))))) :=
  isoMk_pullbackIsoOfSquare_hom_eq_comp₂ y (s.relativeProjPoints.fibreHom U u)
    (s.relativeProjPoints.fibreHom V v) k hy.1 (s.fibreToBase_comp_of_liesOver k y hy)
    (zariskiReadingQcoh U ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := s.space)
        s.shrink.algebra U u).piece n)
      (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent u n))
    (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := s.space)
        s.shrink.algebra V v).piece n)
      (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent v n)) _ _
    (s.asIso_pointComparisonUnital_shrink_app_hom k hv n)

end Chain

section ChartSquare

attribute [local irreducible] CategoryTheory.yoneda

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The chart square of the source of `ψ` along a morphism of the presentation**
(`AlgebraicGeometry.Space.RelativeProjPoints.modulePullback_map_chartPullbackIso_hom_comp₂_eq` in
Situation 0849, with the chain the identification of the sources of `ψ`,
`AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChainIso`): for `y : R ×_X P ⟶ U ×_X P`
lying over `k : R ⟶ U` with `k ≫ u = r`, the identification `c^*π^*𝒜_n ≅ (π_U^*(u^*𝒜)_n)^a`
pulled back along `y`, followed by `y^*(N^a) ≅ (y^*N)^a` and the module attached to the
identification of the sources, is the contraction of Stacks 03LU followed by the identification
at `R`. -/
theorem modulePullback_map_psiChartSourceIso_hom_comp₂_eq (n : ℤ) (k : Px.R ⟶ Px.U)
    (hv : yoneda.map k ≫ Px.toSpace = RelativeProjPoints.relationPoint Px)
    (y : s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px) ⟶
      s.relativeProjPoints.fibre Px.U Px.toSpace)
    (hy : s.relativeProjPoints.LiesOver y k) :
    comp₂ ((modulePullback s.site s.base s.containsBase
        (representedSpaceMap s.site s.base s.containsBase y)).map (Iso.hom (X :=
        (modulePullback s.site s.base s.containsBase (X := (⟨yoneda.obj
            (s.relativeProjPoints.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
          (s.relativeProjPoints.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces s.site s.base
              s.containsBase))
          (presentationAtlas
              (s.relativeProjPoints.spacePresentation Px
                  s.isAlgebraicSpace_relativeProjFunctor))).obj
                      ((modulePullback s.site s.base s.containsBase
              (ObjectProperty.homMk s.relativeProjπ :
                  (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
          (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)))
        (Y := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
            (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
        s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n)))).obj)
        (s.relativeProjPoints.chartPullbackIso Px s.isAlgebraicSpace_relativeProjFunctor
          s.shrink.algebra s.shrink.isQuasicoherent n)))
      (comp₂ (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase y
          (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
              ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n)))).hom
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
            (s.relativeProjPoints.fibre Px.R
            (RelativeProjPoints.relationPoint Px))).functor.map
          (Iso.hom (X := quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (zariskiReadingQcoh Px.U ((etalePointAlgebra (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra Px.U Px.toSpace).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                s.shrink.isQuasicoherent Px.toSpace n))))
            (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
              (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra Px.R
              (RelativeProjPoints.relationPoint Px)).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra
                s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
            (s.pointPieceChainIso k hv y hy n))).hom) =
    comp₂ (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase (Z :=
        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
        (representedSpaceMap s.site s.base s.containsBase y) (presentationAtlas
            (s.relativeProjPoints.spacePresentation Px
                s.isAlgebraicSpace_relativeProjFunctor))).hom.app
            ((modulePullback s.site s.base s.containsBase (ObjectProperty.homMk s.relativeProjπ :
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
          (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)))
        (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase (Y :=
            (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
            (CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase) (Z :=
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
          (representedSpaceMap s.site s.base s.containsBase y)
                    (presentationAtlas
                        (s.relativeProjPoints.spacePresentation Px
                            s.isAlgebraicSpace_relativeProjFunctor)))
                                (ObjectProperty.homMk s.relativeProjπ :
                        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).hom.app
            (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
          (pullbackTransport (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)
            (s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
            s.isAlgebraicSpace_relativeProjFunctor y hy))))
      (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase (s.relativeProjPoints.fibreHom Px.R
          (RelativeProjPoints.relationPoint Px))) (pointHom
              (RelativeProjPoints.relationPoint Px))).inv.app (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
        (comp₂ ((modulePullback s.site s.base s.containsBase
            (representedSpaceMap s.site s.base s.containsBase (s.relativeProjPoints.fibreHom Px.R
            (RelativeProjPoints.relationPoint Px)))).map (zariskiReadingQuasicoherentIso Px.R
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
        s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)).hom)
          (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
              (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent
            (RelativeProjPoints.relationPoint Px) n))).hom)) :=
  by
  have hch := s.pointPieceChainIso_hom_eq_comp₂ k hv y hy n
  have e' := (representedSpaceMap_comp s.site s.base s.containsBase y _).trans
      ((congrArg (representedSpaceMap s.site s.base s.containsBase) hy.1).trans
        (representedSpaceMap_comp s.site s.base s.containsBase _ k).symm)
  have ht := s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
            s.isAlgebraicSpace_relativeProjFunctor y hy
  have hLy := RelativeProjPoints.modulePullback_map_chartPullbackIso_hom_comp₂_eq
    s.relativeProjPoints Px
    s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent n k hv y hy.1
    e' ht _ hch
  exact hLy

/-- **`ψ` on the atlas carries the canonical transition of `π^*𝒜_n` to the transition of
`𝒪(n)`** (Stacks 084D, the compatibility of `ψ` with the descent data): on the arrow space
`P_R` of the groupoid of the presentation `P = P_U/P_R`, the canonical transition morphism of the
inverse image of `π^*𝒜_n` followed by the pullback of `ψ` along the source is the pullback of
`ψ` along the target followed by the transition attached to `𝒪(n)`.  It is proved on the
represented projections `R ×_X P ⇉ U ×_X P`: the chart squares along the two projections
(`AlgebraicGeometry.Space.RelativeProjSituation.modulePullback_map_psiChartSourceIso_hom_comp₂_eq`)
and the coherence of Stacks 03LU give the compatibility of the identification of the source, and
`AlgebraicGeometry.Space.RelativeProjSituation.transitionCommutes_psiChartSchemeHom` that of `ψ`
on the scheme of `P_U`.  The source is written as an object of the category of quasi-coherent
modules over the algebraic space `⟨P, _⟩`, as in the hypothesis of
`AlgebraicGeometry.Space.presentationDescendedIntoHom`. -/
theorem transitionCommutes_psiChartHomOfAdjoint (n : ℕ) :
    TransitionCommutes s.site s.base s.containsBase (U := (presentationGroupoid
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)).objects)
      (V := (presentationGroupoid
          (s.relativeProjPoints.spacePresentation Px
              s.isAlgebraicSpace_relativeProjFunctor)).arrows) (a := (presentationGroupoid
                  (s.relativeProjPoints.spacePresentation Px
                      s.isAlgebraicSpace_relativeProjFunctor)).target)
      (b := (presentationGroupoid
          (s.relativeProjPoints.spacePresentation Px
              s.isAlgebraicSpace_relativeProjFunctor)).source)
      (spaceBaseDescent s.site s.base s.containsBase (presentationGroupoid
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
        (presentationAtlas
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
                (presentationAtlas_comm
                    (s.relativeProjPoints.spacePresentation Px
                        s.isAlgebraicSpace_relativeProjFunctor))
        (show QuasicoherentSheaves.{u, u} s.site s.base s.containsBase
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
          AlgebraicSpaces s.site s.base s.containsBase).obj
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
          AlgebraicSpaces s.site s.base s.containsBase).property from s.psiSourceQcoh (n : ℤ)).obj)
      (presentationSchemeTransition
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
              (s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))
        (s.twistTransition Px (n : ℤ)))
      (s.psiChartHomOfAdjoint Px n) := by
  have hsqT := s.modulePullback_map_psiChartSourceIso_hom_comp₂_eq Px (n : ℤ) Px.target rfl
    (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
  have hsqS := s.modulePullback_map_psiChartSourceIso_hom_comp₂_eq Px (n : ℤ) Px.source
    (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
  have hCoh := comp₂_comp₂_comp₂_eq_of_eq
    (modulePullbackUnflatten_pullbackTransport_comp_modulePullbackCompIso (V := (⟨yoneda.obj
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px)),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) (U := (⟨yoneda.obj
          (s.relativeProjPoints.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces s.site s.base
            s.containsBase))
      (P := (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) (X := s.space)
      (representedSpaceMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
      (representedSpaceMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
              (presentationAtlas
                  (s.relativeProjPoints.spacePresentation Px
                      s.isAlgebraicSpace_relativeProjFunctor))
      (s.relativeProjPoints.representedSpaceMap_spaceTarget_comp_presentationAtlas Px
          s.isAlgebraicSpace_relativeProjFunctor) (ObjectProperty.homMk s.relativeProjπ :
              (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)
      (s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
          s.isAlgebraicSpace_relativeProjFunctor
              (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
                  (s.relativeProjPoints.liesOver_spaceTarget Px
                      s.isAlgebraicSpace_relativeProjFunctor))
      (s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
          s.isAlgebraicSpace_relativeProjFunctor
              (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                  (s.relativeProjPoints.liesOver_spaceSource Px
                      s.isAlgebraicSpace_relativeProjFunctor))
      (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
  have hchS := map_hom_comp₂_map_inv_hom
      (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).functor
          (X := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.source (s.map_source_comp_toSpace Px)
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceSource Px
                            s.isAlgebraicSpace_relativeProjFunctor) n)
  have hτ := eq_comp₂_map_comp₂_map_of_eq
      (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).functor
          (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
              (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
                (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
    (Iso.hom (X := quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.target rfl
                    (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceTarget Px
                            s.isAlgebraicSpace_relativeProjFunctor) n)) (Iso.inv
                                (X := quasicoherentPullbackObj s.site s.base s.containsBase
                                    (s.relativeProjPoints.spaceSource Px
                                        s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.source (s.map_source_comp_toSpace Px)
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceSource Px
                            s.isAlgebraicSpace_relativeProjFunctor) n))
    (representedSchemeTransition s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
        (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ))) (s.psiSourceTransition Px (n : ℤ))) rfl
  have hι := transitionCommutes_of_chartSquares (U := (⟨yoneda.obj
      (s.relativeProjPoints.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces s.site s.base
            s.containsBase)) (V := (⟨yoneda.obj (s.relativeProjPoints.fibre Px.R
                (RelativeProjPoints.relationPoint Px)),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
    (a := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
    (b := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
            (modulePullbackUnflatten (X := (⟨yoneda.obj (s.relativeProjPoints.fibre Px.R
                (RelativeProjPoints.relationPoint Px)),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) (Y := (⟨yoneda.obj
          (s.relativeProjPoints.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces s.site s.base
            s.containsBase))
      (a := representedSpaceMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
      (b := representedSpaceMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
              (presentationAtlas
                  (s.relativeProjPoints.spacePresentation Px
                      s.isAlgebraicSpace_relativeProjFunctor))
      (pullbackTransport (T := (⟨yoneda.obj (s.relativeProjPoints.fibre Px.R
          (RelativeProjPoints.relationPoint Px)),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) (X :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) ((modulePullback s.site s.base s.containsBase
          (ObjectProperty.homMk s.relativeProjπ :
              (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
          (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
            (s.relativeProjPoints.representedSpaceMap_spaceTarget_comp_presentationAtlas Px
                s.isAlgebraicSpace_relativeProjFunctor))) _
                    (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
                        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
                (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).functor.map (Iso.hom
          (X := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.target rfl
                    (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceTarget Px
                            s.isAlgebraicSpace_relativeProjFunctor) n))).hom
                                ((representedQuasicoherentSchemeEquivalence s.site s.base
                                    s.containsBase
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).functor.map (Iso.hom
          (X := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.source (s.map_source_comp_toSpace Px)
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceSource Px
                            s.isAlgebraicSpace_relativeProjFunctor) n))).hom
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).functor.map (Iso.inv
          (X := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
            (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                    ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                        (X := s.space)
          s.shrink.algebra Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent Px.toSpace n))))
          (Y := quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
                  (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                      (hS := s.containsBase) (X := s.space)
          s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
            s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)))
                (s.pointPieceChainIso Px.source (s.map_source_comp_toSpace Px)
                    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                        (s.relativeProjPoints.liesOver_spaceSource Px
                            s.isAlgebraicSpace_relativeProjFunctor) n))).hom hchS
    (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase (Z :=
        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
        (representedSpaceMap s.site s.base s.containsBase
            (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
                (presentationAtlas
                    (s.relativeProjPoints.spacePresentation Px
                        s.isAlgebraicSpace_relativeProjFunctor))).hom.app
            ((modulePullback s.site s.base s.containsBase (ObjectProperty.homMk s.relativeProjπ :
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
          (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)))
        (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase (Y :=
            (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
            (CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase) (Z :=
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
          (representedSpaceMap s.site s.base s.containsBase
              (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
                    (presentationAtlas
                        (s.relativeProjPoints.spacePresentation Px
                            s.isAlgebraicSpace_relativeProjFunctor)))
                                (ObjectProperty.homMk s.relativeProjπ :
                        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).hom.app
            (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
          (pullbackTransport (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)
            (s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
            s.isAlgebraicSpace_relativeProjFunctor
                (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
                    (s.relativeProjPoints.liesOver_spaceTarget Px
                        s.isAlgebraicSpace_relativeProjFunctor))))) (comp₂
                            ((modulePullbackCompIso s.site s.base s.containsBase (Z :=
                                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
        (representedSpaceMap s.site s.base s.containsBase
            (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
                (presentationAtlas
                    (s.relativeProjPoints.spacePresentation Px
                        s.isAlgebraicSpace_relativeProjFunctor))).hom.app
            ((modulePullback s.site s.base s.containsBase (ObjectProperty.homMk s.relativeProjπ :
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
          (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)))
        (comp₂ ((modulePullbackCompIso s.site s.base s.containsBase (Y :=
            (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
            (CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase) (Z :=
                (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
          (representedSpaceMap s.site s.base s.containsBase
              (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
                    (presentationAtlas
                        (s.relativeProjPoints.spacePresentation Px
                            s.isAlgebraicSpace_relativeProjFunctor)))
                                (ObjectProperty.homMk s.relativeProjπ :
                        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).hom.app
            (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
          (pullbackTransport (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n)
            (s.relativeProjPoints.comp_presentationAtlas_comp_homMk_of_liesOver Px
            s.isAlgebraicSpace_relativeProjFunctor
                (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
                    (s.relativeProjPoints.liesOver_spaceSource Px
                        s.isAlgebraicSpace_relativeProjFunctor))))) (comp₂
                            ((modulePullbackCompIso s.site s.base s.containsBase
                                (representedSpaceMap s.site s.base s.containsBase
                                    (s.relativeProjPoints.fibreHom Px.R
          (RelativeProjPoints.relationPoint Px))) (pointHom
              (RelativeProjPoints.relationPoint Px))).inv.app (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra n))
        (comp₂ ((modulePullback s.site s.base s.containsBase
            (representedSpaceMap s.site s.base s.containsBase (s.relativeProjPoints.fibreHom Px.R
            (RelativeProjPoints.relationPoint Px)))).map (zariskiReadingQuasicoherentIso Px.R
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
                    (X := s.space)
        s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent (RelativeProjPoints.relationPoint Px) n)).hom)
          (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
              (zariskiReadingQcoh Px.R ((etalePointAlgebra (B := s.site) (S := s.base)
                  (hS := s.containsBase) (X := s.space)
        s.shrink.algebra Px.R (RelativeProjPoints.relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space)
        s.shrink.algebra s.shrink.isQuasicoherent
            (RelativeProjPoints.relationPoint Px) n))).hom)) hCoh hsqT hsqS
    (representedSchemeTransition s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
        (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ))) (s.psiSourceTransition Px (n : ℤ))) hτ
  have hχ := TransitionCommutes.trans hι (s.transitionCommutes_psiChartSchemeHom Px n)
  exact RelativeProjPoints.transitionCommutes_spaceBaseDescent_of_represented s.relativeProjPoints
    Px s.isAlgebraicSpace_relativeProjFunctor (s.twistTransition Px (n : ℤ))
    (s.psiSourceQcoh (n : ℤ)) (s.psiChartHomOfAdjoint Px n) hχ

/-- **The homomorphism `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` of Stacks 084D**, `n ≥ 0`: the morphism of
`𝒪_P`-modules descended along the presentation `P = P_U/P_R` (Stacks 03M3) from `ψ` on the atlas
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint`), which carries the canonical
transition of `π^*𝒜_n` to the transition of `𝒪(n)`
(`AlgebraicGeometry.Space.RelativeProjSituation.transitionCommutes_psiChartHomOfAdjoint`). -/
def psiTwistHom (n : ℕ) : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj :=
  presentationDescendedIntoHom (s.relativeProjPoints.spacePresentation Px
      s.isAlgebraicSpace_relativeProjFunctor) (s.twistTransition Px (n : ℤ))
    (s.presentationSchemeCocycle_twistTransition Px (n : ℤ))
    (s.presentationSchemeUnit_twistTransition Px (n : ℤ)) (s.psiSourceQcoh (n : ℤ))
    (s.psiChartHomOfAdjoint Px n) (s.transitionCommutes_psiChartHomOfAdjoint Px n)

/-- **`ψ_n` on the atlas is `ψ` of Tag 01NR**: the inverse image of `ψ_n` along the atlas
`c : P_U ⟶ P`, read through the chart identification `c^*𝒪_P(n) ≅ 𝒪(n)^a`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleChartIso`), is
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint`. -/
theorem modulePullback_map_psiTwistHom_comp_twistModuleChartIso_hom (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        (s.psiTwistHom Px n) ≫ (s.twistModuleChartIso Px (n : ℤ)).hom =
      s.psiChartHomOfAdjoint Px n :=
  presentationDescendedIntoHom_spec (s.relativeProjPoints.spacePresentation Px
    s.isAlgebraicSpace_relativeProjFunctor) (s.twistTransition Px (n : ℤ))
    (s.presentationSchemeCocycle_twistTransition Px (n : ℤ))
    (s.presentationSchemeUnit_twistTransition Px (n : ℤ)) (s.psiSourceQcoh (n : ℤ))
    (s.psiChartHomOfAdjoint Px n) (s.transitionCommutes_psiChartHomOfAdjoint Px n)

/-- **`ψ_n` is the unique morphism `π^*𝒜_n ⟶ 𝒪_P(n)` which is `ψ` on the atlas**, through the
chart identification of `𝒪_P(n)`. -/
theorem eq_psiTwistHom (n : ℕ)
    (ψ : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj)
    (hψ : (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        ψ ≫ (s.twistModuleChartIso Px (n : ℤ)).hom = s.psiChartHomOfAdjoint Px n) :
    ψ = s.psiTwistHom Px n :=
  presentationDescendedIntoHom_unique (s.relativeProjPoints.spacePresentation Px
    s.isAlgebraicSpace_relativeProjFunctor) (s.twistTransition Px (n : ℤ))
    (s.presentationSchemeCocycle_twistTransition Px (n : ℤ))
    (s.presentationSchemeUnit_twistTransition Px (n : ℤ)) (s.psiSourceQcoh (n : ℤ))
    (s.psiChartHomOfAdjoint Px n) (s.transitionCommutes_psiChartHomOfAdjoint Px n) ψ hψ

end ChartSquare

end RelativeProjSituation

end AlgebraicGeometry.Space

end
