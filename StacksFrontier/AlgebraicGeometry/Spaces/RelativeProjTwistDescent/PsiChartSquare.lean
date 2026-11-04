module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonPullbackComp

/-!
# The chart squares of the source of `ψ` in Stacks 084D

In Situation 0849 the source `π^*𝒜_n` of the homomorphism `ψ` of Stacks 084D is identified on the
atlas `c : P_U ⟶ P` of the presentation `P = P_U/P_R` with the module attached to
`π_U^*(u^*𝒜)_n` (`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso`).  This file proves
that along a projection `y : P_R ⟶ P_U` of the presentation lying over `k : R ⟶ U` this
identification, pulled back along `y` and followed by the module attached to the chain
`y^*π_U^*(u^*𝒜)_n ≅ π_R^*k^*(u^*𝒜)_n ⟶ π_R^*(r^*𝒜)_n` of the comparison of restrictions of
Stacks 084A, is the contraction of Stacks 03LU followed by the identification at `R`: the
compatibility of the chart identification with the descent data, one projection at a time.

## Main results

* `Space.modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_pullback`:
  the comparison of restrictions of Stacks 084A read on the attached modules (bridge K), pulled
  back along a further morphism of the site.
* `AlgebraicGeometry.Space.modulePullback_map_map_comp₂_modulePullbackCompIso_eq`: the contraction
  of Stacks 03LU along a commutative square is natural.
* `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_eq_trans`: the chart
  identification with the inverse images taken over the represented algebraic space of `P_U`.
* `AlgebraicGeometry.Space.RelativeProjPoints.modulePullback_map_chartPullbackIso_hom_comp₂_eq`:
  **the chart square** along a projection of the presentation.

## Implementation notes

All identities are written with named binary composites (`CategoryTheory.comp₂`), and every
factor shared by two of the identities assembled is spelled identically in both, including the
algebraic spaces implicit in it: the kernel compares two composites of modules, or two images under
an inverse-image functor, whose implicit objects are spelled differently by unfolding the
inverse-image functors, which does not terminate in reasonable time when a transport
`AlgebraicGeometry.Space.pullbackTransport` occurs.  The chart identification is therefore read
over `⟨yoneda.obj P_U, _⟩` rather than over the object space of the groupoid of the presentation,
through an equality of isomorphisms (`chartPullbackIso_eq_trans`), which the kernel compares factor
by factor.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

section Generic

/-- The inverse image along `F` of an identity `x ≫ y ≫ z = (w ≫ v) ≫ t` written with named binary
composites. -/
theorem map_comp₂_comp₂_eq_comp₂_comp₂ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y₁ Y₂ Z Y₁' Y₂' : C} (x : X ⟶ Y₁) (y : Y₁ ⟶ Y₂) (z : Y₂ ⟶ Z) (w : X ⟶ Y₁')
    (v : Y₁' ⟶ Y₂') (t : Y₂' ⟶ Z) (h : comp₂ x (comp₂ y z) = comp₂ (comp₂ w v) t) :
    comp₂ (F.map x) (comp₂ (F.map y) (F.map z)) = comp₂ (comp₂ (F.map w) (F.map v)) (F.map t) := by
  simp only [comp₂_eq] at h ⊢
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, h]

/-- The image under `F` of the morphism of a composite of five isomorphisms, as named binary
composites, the second factor written through a given equal morphism. -/
theorem map_hom_eq_comp₂_of_eq_trans {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (ι : X₀ ≅ X₅) (i₁ : X₀ ≅ X₁) (i₂ : X₁ ≅ X₂) (i₃ : X₂ ≅ X₃)
    (i₄ : X₃ ≅ X₄) (i₅ : X₄ ≅ X₅) (h : ι = i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅) (f₂ : X₁ ⟶ X₂)
    (hf₂ : i₂.hom = f₂) :
    F.map ι.hom = comp₂ (F.map i₁.hom) (comp₂ (F.map f₂) (comp₂ (F.map i₃.hom)
      (comp₂ (F.map i₄.hom) (F.map i₅.hom)))) := by
  subst h hf₂
  simp only [Iso.trans_hom, Functor.map_comp, comp₂_eq]

/-- The underlying morphism of the image under `F` of a composite of four morphisms in a full
subcategory, as named binary composites. -/
theorem map_hom_eq_comp₂_of_eq_comp₂ {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {X Y₁ Y₂ Y₃ Z : C} (ch : X ⟶ Z)
    (q₁ : X ⟶ Y₁) (q₂ : Y₁ ⟶ Y₂) (q₃ : Y₂ ⟶ Y₃) (q₄ : Y₃ ⟶ Z)
    (h : ch = comp₂ q₁ (comp₂ q₂ (comp₂ q₃ q₄))) :
    (F.map ch).hom = comp₂ (F.map q₁).hom (comp₂ (F.map q₂).hom
      (comp₂ (F.map q₃).hom (F.map q₄).hom)) := by
  subst h
  simp only [comp₂_eq, Functor.map_comp]
  rfl

/-- The image under `F` of a component of a natural isomorphism, in its two spellings. -/
theorem map_app_hom_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : E ⥤ C} (α : G ≅ H) (M : E) :
    F.map (α.app M).hom = F.map (α.hom.app M) :=
  rfl

/-- The image under `F` of the inverse of a component of a natural isomorphism, in its two
spellings. -/
theorem map_app_symm_hom_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : E ⥤ C} (α : G ≅ H) (M : E) :
    F.map (α.app M).symm.hom = F.map (α.inv.app M) :=
  rfl

/-- The image under `F` of the image under `G` of an isomorphism, in its two spellings. -/
theorem map_mapIso_hom_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ C) {M N : E} (i : M ≅ N) :
    F.map (G.mapIso i).hom = F.map (G.map i.hom) :=
  rfl

/-- The abstract shape of
`AlgebraicGeometry.Space.RelativeProjPoints.modulePullback_map_chartPullbackIso_hom_comp₂_eq`, at
variables. -/
private theorem comp₂_eq_of_chart_square_pieces {D : Type*} [Category D]
    {O0 O1 O2 O3 O4 O5 O6 O7 P1 P2 P3 X1 X2 X3 X4 X5 Y1 Y2 Y3 Q1 Q2 G1 G2 G3 : D}
    {ιm : O0 ⟶ O5} {m1 : O0 ⟶ O1} {m2 : O1 ⟶ O2} {m3 : O2 ⟶ O3} {m4 : O3 ⟶ O4} {m5 : O4 ⟶ O5}
    {C3y : O5 ⟶ O6} {chA : O6 ⟶ O7} {a1 : O6 ⟶ P1} {a2 : P1 ⟶ P2} {a3 : P2 ⟶ P3} {a4 : P3 ⟶ O7}
    {c1 : O4 ⟶ X1} {p : X1 ⟶ X2} {ci : X2 ⟶ X3} {n1 : X3 ⟶ X4} {n2 : X4 ⟶ X5} {n3 : X5 ⟶ O7}
    {c1' : O3 ⟶ Y1} {p' : Y1 ⟶ Y2} {ci' : Y2 ⟶ Y3} {n0 : Y3 ⟶ X3}
    {q1 : Y3 ⟶ Q1} {q2 : Q1 ⟶ Q2} {n4 : Q2 ⟶ X5}
    {g1 : O0 ⟶ G1} {g2 : G1 ⟶ G2} {g3 : G2 ⟶ G3} {g4 : G3 ⟶ Q2}
    {m1b : O0 ⟶ O1} {m3b : O2 ⟶ O3} {m4b : O3 ⟶ O4}
    (hι : ιm = comp₂ m1 (comp₂ m2 (comp₂ m3 (comp₂ m4 m5))))
    (hch : chA = comp₂ a1 (comp₂ a2 (comp₂ a3 a4)))
    (hm1 : m1 = m1b) (hm3 : m3 = m3b) (hm4 : m4 = m4b)
    (hLa : comp₂ m5 (comp₂ C3y (comp₂ a1 (comp₂ a2 (comp₂ a3 a4)))) =
      comp₂ c1 (comp₂ p (comp₂ ci (comp₂ n1 (comp₂ n2 n3)))))
    (hnat : comp₂ m4b (comp₂ c1 (comp₂ p ci)) = comp₂ c1' (comp₂ p' (comp₂ ci' n0)))
    (hK : comp₂ n0 (comp₂ n1 n2) = comp₂ (comp₂ q1 q2) n4)
    (hLb : comp₂ m1b (comp₂ m2 (comp₂ m3b (comp₂ c1' (comp₂ p' (comp₂ ci' (comp₂ q1 q2)))))) =
      comp₂ g1 (comp₂ g2 (comp₂ g3 g4))) :
    comp₂ ιm (comp₂ C3y chA) = comp₂ (comp₂ g1 (comp₂ g2 g3)) (comp₂ g4 (comp₂ n4 n3)) := by
  subst hι hch hm1 hm3 hm4
  simp only [comp₂_eq, Category.assoc] at hLa hnat hK hLb ⊢
  have k1 : m4 ≫ m5 ≫ C3y ≫ a1 ≫ a2 ≫ a3 ≫ a4 = c1' ≫ p' ≫ ci' ≫ q1 ≫ q2 ≫ n4 ≫ n3 := by
    rw [hLa, reassoc_of% hnat, reassoc_of% hK]
  rw [k1, reassoc_of% hLb]

end Generic

section Coherence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The contraction of Stacks 03LU along a commutative square is natural**: for
`y ≫ f_U = f_R ≫ k`, the contraction `y^*f_U^* ≅ f_R^*k^*` (through `(y ≫ f_U)^* = (f_R ≫ k)^*`)
commutes with the inverse images of a morphism `f : M ⟶ N`. -/
theorem modulePullback_map_map_comp₂_modulePullbackCompIso_eq {W V U R : AlgebraicSpaces B S hS}
    (y : W ⟶ V) (fU : V ⟶ U) (fR : W ⟶ R) (k : R ⟶ U) (e : y ≫ fU = fR ≫ k)
    {M N : Modules.{u, u} B S hS U.1 U.2} (f : M ⟶ N) :
    comp₂ ((modulePullback B S hS y).map ((modulePullback B S hS fU).map f))
      (comp₂ ((modulePullbackCompIso B S hS y fU).hom.app N)
        (comp₂ (pullbackTransport N e) ((modulePullbackCompIso B S hS fR k).inv.app N))) =
    comp₂ ((modulePullbackCompIso B S hS y fU).hom.app M)
      (comp₂ (pullbackTransport M e)
        (comp₂ ((modulePullbackCompIso B S hS fR k).inv.app M) ((modulePullback B S hS fR).map
            ((modulePullback B S hS k).map f)))) := by
  have h1 : (modulePullback B S hS y).map ((modulePullback B S hS fU).map f) ≫
      (modulePullbackCompIso B S hS y fU).hom.app N =
      (modulePullbackCompIso B S hS y fU).hom.app M ≫ (modulePullback B S hS (y ≫ fU)).map f :=
          (modulePullbackCompIso B S hS y fU).hom.naturality f
  have h3 : (modulePullback B S hS (fR ≫ k)).map f ≫ (modulePullbackCompIso B S hS fR k).inv.app N =
      (modulePullbackCompIso B S hS fR k).inv.app M ≫ (modulePullback B S hS fR).map
          ((modulePullback B S hS k).map f) :=
    (modulePullbackCompIso B S hS fR k).inv.naturality f
  simp only [comp₂_eq]
  rw [reassoc_of% h1, pullbackTransport_naturality_assoc, h3]

end Coherence

section K

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- **The comparison of the restrictions of Stacks 084A, read on the attached modules, pulled back
along a further morphism `g : W ⟶ T'` of the site**
(`Space.modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison`
under `g^*`), written with named binary composites. -/
theorem modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_pullback
    {W : BigFppfOver B S hS} (g : W ⟶ T') {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    comp₂ ((modulePullback B S hS (representedSpaceMap B S hS g)).map
      ((modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n) :
          (modulePullback B S hS (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
              (pointHom f)).obj
            (A.piece n) ≅ _).hom))
      (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS g)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS τ
          (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n))).hom)
        ((modulePullback B S hS (representedSpaceMap B S hS g)).map
         ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk ((pointComparison A τ f f' hf).app n) :
            quasicoherentPullbackObj B S hS τ
              (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)) ⟶
            zariskiReadingQcoh T' ((etalePointAlgebra A T' f').piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n))).hom)) =
      comp₂ (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
              (A.piece n)))
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map (pullbackTransport
            (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
                (representedSpaceMap B S hS τ) (pointHom f))
            (A.piece n) (pointHom_comp τ hf))))
        ((modulePullback B S hS (representedSpaceMap B S hS g)).map
          (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom) := by
  have hK : comp₂ ((modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n) :
          (modulePullback B S hS (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
              (pointHom f)).obj
            (A.piece n) ≅ _).hom)
      (comp₂ (modulePullbackRepresentedQuasicoherentIso B S hS τ
          (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n))).hom
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk ((pointComparison A τ f f' hf).app n) :
            quasicoherentPullbackObj B S hS τ
              (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)) ⟶
            zariskiReadingQcoh T' ((etalePointAlgebra A T' f').piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n))).hom) =
      comp₂ (comp₂ ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ)
          (pointHom f)).hom.app
          (A.piece n)) (pullbackTransport
            (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
                (representedSpaceMap B S hS τ) (pointHom f))
            (A.piece n) (pointHom_comp τ hf)))
        (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom :=
    modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison τ A hA f f' hf n
  exact map_comp₂_comp₂_eq_comp₂_comp₂ _ _ _ _ _ _ _ hK

end K

namespace RelativeProjPoints

section ChartSquare

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso` with the inverse images taken
over the represented algebraic space of `P_U` and the reading of `(u^*𝒜)_n` spelled as a Zariski
reading. -/
theorem chartPullbackIso_eq_trans (n : ℤ) :
    @Eq ((modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
          ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj)
      (d.chartPullbackIso Px hP A hA n)
      (((modulePullbackCompIso B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).app (A.piece n)) ≪≫ (eqToIso (X :=
                      (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
                          (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X))).obj (A.piece n))
          (Y := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X :=
              (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace))).obj (A.piece n))
          (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n))
            (d.presentationAtlas_comp_homMk Px hP : CategoryStruct.comp
                (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) = CategoryStruct.comp
                      (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace)))) ≪≫ (((modulePullbackCompIso B S hS
                      (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                          (pointHom Px.toSpace)).app (A.piece n)).symm) ≪≫ ((modulePullback B S hS
                              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).mapIso
                                  ((zariskiReadingQuasicoherentIso Px.U
                                      ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom Px.toSpace)).obj
                          (A.piece n) ≅ _)) ≪≫ modulePullbackRepresentedQuasicoherentIso B S hS
                              (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                                  ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
        (modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
          ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj) :=
  rfl

/-- **The chart square of the source of `ψ` of Stacks 084D along a projection of the
presentation**: for `y : P_R ⟶ P_U` of the presentation of `P` lying over `k : R ⟶ U`, the
identification `c^*π^*𝒜_n ≅ (π_U^*(u^*𝒜)_n)^a` pulled back along `y`, read through
`y^*(N^a) ≅ (y^*N)^a` and followed by the module attached to the chain
`y^*π_U^*(u^*𝒜)_n ≅ π_R^*k^*(u^*𝒜)_n ⟶ π_R^*(r^*𝒜)_n` of the comparison of the restrictions of
Stacks 084A, is the contraction `y^*c^*π^*𝒜_n ≅ (π_R ≫ p_R)^*𝒜_n` of Stacks 03LU followed by the
identification at `R`. -/
theorem modulePullback_map_chartPullbackIso_hom_comp₂_eq (n : ℤ) (k : Px.R ⟶ Px.U)
    (hv : yoneda.map k ≫ Px.toSpace = relationPoint Px)
    (y : (d.fibre Px.R (relationPoint Px)) ⟶ (d.fibre Px.U Px.toSpace)) (e : y ≫
        (d.fibreHom Px.U Px.toSpace) = (d.fibreHom Px.R (relationPoint Px)) ≫ k)
    (e' : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS
          (d.fibreHom Px.R (relationPoint Px))) (representedSpaceMap B S hS k))
    (ht : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Y :=
        (⟨P, hP⟩ : AlgebraicSpaces B S hS))
        (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z :=
            (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (representedSpaceMap B S hS y) (presentationAtlas
                (d.spacePresentation Px hP))) (ObjectProperty.homMk π :
                    (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS
          (d.fibreHom Px.R (relationPoint Px))) (pointHom (relationPoint Px)))
    (ch : quasicoherentPullbackObj B S hS y (quasicoherentPullbackObj B S hS
        (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
            ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))) ⟶
      quasicoherentPullbackObj B S hS (d.fibreHom Px.R (relationPoint Px)) (zariskiReadingQcoh Px.R
          ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n)))
    (hch : ch = comp₂ (quasicoherentPullbackCompIso B S hS y (d.fibreHom Px.U Px.toSpace)
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))).hom
      (comp₂ (eqToHom (congrArg (fun g => quasicoherentPullbackObj B S hS g
          (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))) e :
          quasicoherentPullbackObj B S hS (y ≫ (d.fibreHom Px.U Px.toSpace))
              (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) =
            quasicoherentPullbackObj B S hS ((d.fibreHom Px.R (relationPoint Px)) ≫ k)
                (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))))
        (comp₂ (quasicoherentPullbackCompIso B S hS (d.fibreHom Px.R (relationPoint Px)) k
            (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))).inv
          (quasicoherentPullbackMap B S hS (d.fibreHom Px.R (relationPoint Px))
              (ObjectProperty.homMk ((pointComparison A k Px.toSpace (relationPoint Px) hv).app n) :
          quasicoherentPullbackObj B S hS k (zariskiReadingQcoh Px.U
              ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) ⟶
              (zariskiReadingQcoh Px.R ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n))))))) :
    comp₂ ((modulePullback B S hS (representedSpaceMap B S hS y)).map (Iso.hom (X :=
        (modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)))
        (Y := ((representedQuasicoherentSchemeEquivalence B S hS
            (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj)
        (d.chartPullbackIso Px hP A hA n)))
      (comp₂ (modulePullbackRepresentedQuasicoherentIso B S hS y (quasicoherentPullbackObj B S hS
          (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
              ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).hom
        ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.R
            (relationPoint Px))).functor.map ch).hom) =
    comp₂ (comp₂ ((modulePullbackCompIso B S hS (Z := (⟨P, hP⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS y) (presentationAtlas (d.spacePresentation Px hP))).hom.app
            ((modulePullback B S hS (ObjectProperty.homMk π :
                (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)))
        (comp₂ ((modulePullbackCompIso B S hS (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS))
            (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z :=
                (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (representedSpaceMap B S hS y)
                    (presentationAtlas (d.spacePresentation Px hP))) (ObjectProperty.homMk π :
                        (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).hom.app
            (A.piece n))
          (pullbackTransport (A.piece n) ht)))
      (comp₂ ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (d.fibreHom Px.R
          (relationPoint Px))) (pointHom (relationPoint Px))).inv.app (A.piece n))
        (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom Px.R
            (relationPoint Px)))).map (zariskiReadingQuasicoherentIso Px.R
                ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n)).hom)
          (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom Px.R (relationPoint Px))
              (zariskiReadingQcoh Px.R ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n))).hom)) := by
  have hι := map_hom_eq_comp₂_of_eq_trans (modulePullback B S hS (representedSpaceMap B S hS y))
      (X₀ := (modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)))
    (X₅ := ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj)
              (d.chartPullbackIso Px hP A hA n)
    ((modulePullbackCompIso B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).app (A.piece n))
    (eqToIso (X := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X))).obj (A.piece n))
          (Y := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X :=
              (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace))).obj (A.piece n))
          (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n))
            (d.presentationAtlas_comp_homMk Px hP : CategoryStruct.comp
                (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) = CategoryStruct.comp
                      (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace))))
    (((modulePullbackCompIso B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
        (pointHom Px.toSpace)).app (A.piece n)).symm) ((modulePullback B S hS
            (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).mapIso
                ((zariskiReadingQuasicoherentIso Px.U
                    ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom Px.toSpace)).obj (A.piece n) ≅ _))
                          (modulePullbackRepresentedQuasicoherentIso B S hS
                              (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                                  ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))
    (d.chartPullbackIso_eq_trans Px hP A hA n) (pullbackTransport (T := (⟨yoneda.obj
        (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (X := X)
          (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj
              (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X))
      (g := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj
          (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace)) (A.piece n) (d.presentationAtlas_comp_homMk Px hP)) rfl
  have hchA := map_hom_eq_comp₂_of_eq_comp₂
    (representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.R
        (relationPoint Px))).functor ch _ _ _ _ hch
  have hLa := modulePullback_map_modulePullbackRepresentedQuasicoherentIso_comp_chain y
      (d.fibreHom Px.U Px.toSpace) (d.fibreHom Px.R (relationPoint Px)) k
    e e' (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))
              (zariskiReadingQcoh Px.R ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n))
              (ObjectProperty.homMk ((pointComparison A k Px.toSpace (relationPoint Px) hv).app n) :
          quasicoherentPullbackObj B S hS k (zariskiReadingQcoh Px.U
              ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) ⟶
              (zariskiReadingQcoh Px.R ((etalePointAlgebra A Px.R (relationPoint Px)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (relationPoint Px) n)))
  have hnat := modulePullback_map_map_comp₂_modulePullbackCompIso_eq (W := (⟨yoneda.obj
      (d.fibre Px.R (relationPoint Px)),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.R (relationPoint Px))⟩ : AlgebraicSpaces B S hS))
          (V := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
    (U := (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS)) (R :=
        (⟨yoneda.obj Px.R, isAlgebraicSpace_yoneda B S hS Px.R⟩ : AlgebraicSpaces B S hS))
            (representedSpaceMap B S hS y) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
    (representedSpaceMap B S hS (d.fibreHom Px.R (relationPoint Px)))
        (representedSpaceMap B S hS k) e' (M := (modulePullback B S hS (X :=
            (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS))
                (pointHom Px.toSpace)).obj (A.piece n))
    (N := ((representedQuasicoherentSchemeEquivalence B S hS Px.U).functor.obj
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))).obj)
    ((zariskiReadingQuasicoherentIso Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom Px.toSpace)).obj (A.piece n) ≅ _).hom
  have hK := modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_pullback
    k (d.fibreHom Px.R (relationPoint Px)) A hA Px.toSpace (relationPoint Px) hv n
  have hLb := modulePullback_map_comp_modulePullbackCompIso_eq_of_squares (W := (⟨yoneda.obj
      (d.fibre Px.R (relationPoint Px)),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.R (relationPoint Px))⟩ : AlgebraicSpaces B S hS))
          (V := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
    (P := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (X := X) (U :=
        (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S hS)) (R :=
            (⟨yoneda.obj Px.R, isAlgebraicSpace_yoneda B S hS Px.R⟩ : AlgebraicSpaces B S hS))
                (representedSpaceMap B S hS y) (presentationAtlas (d.spacePresentation Px hP))
                    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace)
        (representedSpaceMap B S hS (d.fibreHom Px.R (relationPoint Px)))
            (representedSpaceMap B S hS k) (pointHom (relationPoint Px))
                (d.presentationAtlas_comp_homMk Px hP)
    e' (pointHom_comp k hv) ht (A.piece n)
  exact comp₂_eq_of_chart_square_pieces hι hchA
    (map_app_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullbackCompIso B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)) (A.piece n))
    (map_app_symm_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
            (pointHom Px.toSpace)) (A.piece n))
    (map_mapIso_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)))
      ((zariskiReadingQuasicoherentIso Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj Px.U, isAlgebraicSpace_yoneda B S hS Px.U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom Px.toSpace)).obj (A.piece n) ≅ _)) hLa hnat hK hLb

end ChartSquare

end RelativeProjPoints

end AlgebraicGeometry.Space

end
