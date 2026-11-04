module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisSections

/-!
# The Mayer–Vietoris triangle of global sections, with its four maps named

This file proves the three clauses of Stacks 0CRS — the distinguished triangle
`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`, its long exact cohomology
sequence, and their functoriality in `E` — with the **four first maps written out in the
statement**: the right derived transformations of the restriction maps `RΓ(X, -) ⟶ RΓ(U, -)`,
`RΓ(V, -)` and `RΓ(U, -)`, `RΓ(V, -) ⟶ RΓ(U ×_X V, -)`. Only the connecting map `δ` is
existentially quantified, as in the source.

## Main results

In the namespace `CategoryTheory.PushforwardMayerVietoris`:

* `exists_delta_mem_distTriang_mapMayerVietoris_of_injective`: the abstract Mayer–Vietoris
  triangle of a right derived functor, with its four maps named.

In the namespace `AlgebraicGeometry.Space`:

* `exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek`: all three clauses
  with the four maps named, for any extension by zero.
* `exists_delta_mem_distTriang_edsSectionsMayerVietoris_unconditional`,
  `exists_delta_homologySequence_exact_edsSectionsMayerVietoris_unconditional`,
  `exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`: **the three
  clauses of Stacks 0CRS with the four maps named.**

## Implementation notes

The four maps out of and into the outer terms are the right derived transformations of
`Γ(X, -)` applied to the units `F ⟶ j_{U,*}F|_U`, `F ⟶ j_{V,*}F|_V` of the adjunctions
`(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU (`CategoryTheory.PushforwardMayerVietoris.mapUnit`) and to the
two comparisons `j_{U,*}F|_U ⟶ j_{P,*}F|_P`, `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW part (1),
the conjugates of the extension-by-zero comparisons
`AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` of Stacks 08GV.

## References

* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.PushforwardMayerVietoris

section Functorial

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]

section Assembly

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- **The long exact homology sequence of a natural Mayer–Vietoris triangle whose four first
maps are given.**  `exists_natTrans_homologySequence_exact_of_exists_natTrans` with the four
transformations *not* quantified away: whatever they are, the homology sequence of the triangle
they assemble is exact at every object and every `n`, and its maps are the images under `H^n` of
theirs. -/
lemma exists_delta_homologySequence_exact_of_exists_delta
    {RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C}
    {aU : RX ⟶ RU} {aV : RX ⟶ RV} {bU : RU ⟶ RP} {bV : RV ⟶ RP}
    (h : ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A, Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈ distTriang (DerivedCategory C)) :
    ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A,
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact :=
  h.imp fun _ hT E =>
    ⟨hT E, fun n => Functor.homologySequenceComposableArrows₅_exact _ _ (hT E) n (n + 1) rfl⟩

/-- **The component at one object of a natural Mayer–Vietoris triangle whose four first maps are
given.**  The same four maps, at a fixed object, with the connecting map taken to be the
component there of the connecting transformation. -/
lemma exists_app_mem_distTriang_of_exists_delta
    {RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C}
    {aU : RX ⟶ RU} {aV : RX ⟶ RV} {bU : RU ⟶ RP} {bV : RV ⟶ RP}
    (h : ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A,
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact)
    (E : DerivedCategory A) :
    ∃ δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) δ ∈ distTriang (DerivedCategory C) :=
  h.elim fun δ hδ => ⟨δ.app E, (hδ E).1⟩

/-- **The component at one object of a natural Mayer–Vietoris triangle whose four first maps are
given, with its exact homology sequence.**
`CategoryTheory.PushforwardMayerVietoris.exists_app_mem_distTriang_of_exists_delta` keeping the
second half of the conclusion. -/
lemma exists_app_homologySequence_exact_of_exists_delta
    {RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C}
    {aU : RX ⟶ RU} {aV : RX ⟶ RV} {bU : RU ⟶ RP} {bV : RV ⟶ RP}
    (h : ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A,
        Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E) ∈
          distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) (δ.app E)) n (n + 1) rfl).Exact)
    (E : DerivedCategory A) :
    ∃ δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift (aU.app E) (aV.app E))
          (biprod.desc (bU.app E) (-(bV.app E))) δ ∈ distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift (aU.app E) (aV.app E))
            (biprod.desc (bU.app E) (-(bV.app E))) δ) n (n + 1) rfl).Exact :=
  h.elim fun δ hδ => ⟨δ.app E, hδ E⟩

end Assembly

section Functoriality

variable {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

include hzero in
/-- **The abstract Mayer–Vietoris triangle of a right derived functor, with its four maps
named.**

In the situation of
`CategoryTheory.PushforwardMayerVietoris.exists_mem_distTriang_mapMayerVietoris` — additive
endofunctors `Φ_U`, `Φ_V`, `Φ_P` of an abelian category `A` admitting termwise injective
K-injective resolutions, natural transformations `η_U`, `η_V`, `d_U`, `d_V` whose Mayer–Vietoris
sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` is short exact at the injective objects, an
additive functor `G : A ⥤ C`, and right derived functors `R_X`, `R_U`, `R_V`, `R_P` of `G`,
`Φ_U ⋙ G`, `Φ_V ⋙ G`, `Φ_P ⋙ G` — there is a distinguished triangle

`R_X E ⟶ R_U E ⊕ R_V E ⟶ R_P E ⟶ (R_X E)[1]`

at every object `E` of `D(A)`.

**Its four first maps are written out in the statement, not existentially quantified.**  Each
is `CategoryTheory.Functor.rightDerivedNatTrans` of the corresponding transformation of the
underlying functors: `G(η_U) : G ⟶ Φ_U ⋙ G` and `G(η_V) : G ⟶ Φ_V ⋙ G`
(`CategoryTheory.PushforwardMayerVietoris.mapUnit`) for the two maps out of `R_X`, and
`d_U ⋙ G : Φ_U ⋙ G ⟶ Φ_P ⋙ G`, `d_V ⋙ G` for the two maps into `R_P`.  They are natural
transformations of the four derived functors, so the triangle is also functorial in `E`: a
morphism `E ⟶ E'` induces a morphism of triangles.

Only the connecting map `δ : R_P ⟶ R_X ⋙ (-)[1]` is existentially quantified, the library
attaching no canonical such map to an object of `D(A)`; the sources of Stacks 08JK and Stacks
0CRS likewise assert only that a triangle with these three terms is distinguished.  It too is a
natural transformation: it is assembled from the connecting maps of the Mayer–Vietoris
sequences at a chosen termwise injective K-injective resolution of each object, and its
naturality is the naturality of `DerivedCategory.triangleOfSESδ` in the short exact sequence,
together with the fact that every morphism between the resolutions' images in `D(A)` comes from
a morphism of complexes, which is K-injectivity.

The Mayer–Vietoris hypothesis is taken in its weakest useful form: the image under `G` of the
sequence is required to be short exact only at the *injective* objects.  Those are the only
objects at which it is used, and for Stacks 0CRS they are the only ones at which it is
available without the étale-local argument of Stacks 01FW. -/
theorem exists_delta_mem_distTriang_mapMayerVietoris_of_injective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : (ΦU ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : (ΦV ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : (ΦP ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ E : DerivedCategory A, Triangle.mk
          (biprod.lift
            ((Functor.rightDerivedNatTrans RX RU αX αU
              (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
              (Functor.whiskerRight
                (NatTrans.mapHomotopyCategory (mapUnit ηU G) (ComplexShape.up ℤ))
                DerivedCategory.Qh)).app E)
            ((Functor.rightDerivedNatTrans RX RV αX αV
              (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
              (Functor.whiskerRight
                (NatTrans.mapHomotopyCategory (mapUnit ηV G) (ComplexShape.up ℤ))
                DerivedCategory.Qh)).app E))
          (biprod.desc
            ((Functor.rightDerivedNatTrans RU RP αU αP
              (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
              (Functor.whiskerRight
                (NatTrans.mapHomotopyCategory (Functor.whiskerRight dU G) (ComplexShape.up ℤ))
                DerivedCategory.Qh)).app E)
            (-((Functor.rightDerivedNatTrans RV RP αV αP
              (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
              (Functor.whiskerRight
                (NatTrans.mapHomotopyCategory (Functor.whiskerRight dV G) (ComplexShape.up ℤ))
                DerivedCategory.Qh)).app E)))
          (δ.app E) ∈
        distTriang (DerivedCategory C) := by
  have := hRX
  have := hRU
  have := hRV
  have := hRP
  have hres' : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i :=
    fun K => (hres K).imp fun _ ⟨i, h₁, h₂, _⟩ => ⟨i, h₁, h₂⟩
  choose Res hResK hResInj hResNe using
    fun E : DerivedCategory A => exists_isKInjective_injective_representative hres E
  have e : ∀ E : DerivedCategory A, DerivedCategory.Q.obj (Res E) ≅ E :=
    fun E => (hResNe E).some
  have hiso : ∀ (F : A ⥤ C) [F.Additive] (R : DerivedCategory A ⥤ DerivedCategory C)
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ R)
      [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
      (J : CochainComplex A ℤ), J.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)) :=
    fun F _ R α _ J hJ =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres').2
        DerivedCategory.Qh R α J hJ
  have hX := hiso G RX αX
  have hU := hiso (ΦU ⋙ G) RU αU
  have hV := hiso (ΦV ⋙ G) RV αV
  have hP := hiso (ΦP ⋙ G) RP αP
  refine exists_natTrans_mem_distTriang_of_resolutions _ _ _ _
    (fun E => mvShortComplex ηU ηV dU dV hzero G (Res E))
    (fun E => shortExact_mvShortComplex_of_injective ηU ηV dU dV hzero G hMV (Res E)
      (hResInj E))
    (fun E => kinjIso G RX αX (Res E) (hX _ (hResK E)) ≪≫ RX.mapIso (e E))
    (fun E => DerivedCategory.Q.biprodIsoOfAdditive _ _ ≪≫
      biprod.mapIso (kinjIso (ΦU ⋙ G) RU αU (Res E) (hU _ (hResK E)) ≪≫ RU.mapIso (e E))
        (kinjIso (ΦV ⋙ G) RV αV (Res E) (hV _ (hResK E)) ≪≫ RV.mapIso (e E)))
    (fun E => kinjIso (ΦP ⋙ G) RP αP (Res E) (hP _ (hResK E)) ≪≫ RP.mapIso (e E))
    (fun E => ?_) (fun E => ?_) (fun {E E'} φ => ?_)
  · have cU := kinjIso_trans_hom_rightDerivedNatTrans RX RU αX αU hRX hRU (mapUnit ηU G)
      (hX _ (hResK E)) (hU _ (hResK E)) (e E)
    have cV := kinjIso_trans_hom_rightDerivedNatTrans RX RV αX αV hRX hRV (mapUnit ηV G)
      (hX _ (hResK E)) (hV _ (hResK E)) (e E)
    dsimp only [mvShortComplex, Iso.trans_hom]
    rw [← Category.assoc, Functor.biprodIsoOfAdditive_hom_map_lift, biprod.mapIso_hom]
    refine biprod.hom_ext _ _ ?_ ?_
    · simpa using cU
    · simpa using cV
  · have cU := kinjIso_trans_hom_rightDerivedNatTrans RU RP αU αP hRU hRP
      (Functor.whiskerRight dU G) (hU _ (hResK E)) (hP _ (hResK E)) (e E)
    have cV := kinjIso_trans_hom_rightDerivedNatTrans RV RP αV αP hRV hRP
      (Functor.whiskerRight dV G) (hV _ (hResK E)) (hP _ (hResK E)) (e E)
    dsimp only [mvShortComplex, Iso.trans_hom]
    rw [Category.assoc, biprod.mapIso_hom, biprod.map_desc, ← Iso.inv_comp_eq,
      Functor.biprodIsoOfAdditive_inv_map_desc_assoc, DerivedCategory.Q.map_neg]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simpa using cU
    · simp only [biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.comp_neg,
        Preadditive.neg_comp]
      rw [neg_inj]
      simpa using cV
  · obtain ⟨g, hg⟩ := exists_eq_Q_map_of_isKInjective (hResK E')
      ((e E).hom ≫ φ ≫ (e E').inv)
    refine ⟨mvShortComplexMap ηU ηV dU dV hzero G g, ?_, ?_⟩
    · exact (kinjIso_trans_hom_naturality G RX αX (hX _ (hResK E)) (hX _ (hResK E'))
        (e E) (e E') φ g hg).symm
    · exact (kinjIso_trans_hom_naturality (ΦP ⋙ G) RP αP (hP _ (hResK E)) (hP _ (hResK E'))
        (e E) (e E') φ g hg).symm

end Functoriality

end Functorial

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Unconditional

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} (RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))]

include adjU adjV adjP in
/-- All three clauses of Stacks 0CRS **with the four maps of the triangle named**, for left
adjoints `shriekU`, `shriekV`, `shriekP` of restriction along the three étale morphisms of the
square (extensions by zero).

The first two maps are the right derived transformations of the restriction maps on sections
`Γ(X, F) ⟶ Γ(X, j_{U,*}F|_U)` and `Γ(X, F) ⟶ Γ(X, j_{V,*}F|_V)`, that is of `Γ(X, -)` applied
to the units of the adjunctions `(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU
(`CategoryTheory.PushforwardMayerVietoris.mapUnit`); the next two are the right derived
transformations of `Γ(X, -)` applied to the two comparisons
`j_{U,*}F|_U ⟶ j_{P,*}F|_P`, `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW part (1) — the
conjugates, under `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the extension-by-zero comparisons
`AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` of Stacks 08GV.  Only the connecting
transformation `δ` is existentially quantified, as in Stacks 08GV part (2), Stacks 08GW
part (2) and the source of this tag.

The Mayer–Vietoris sequence of Stacks 08GW part (1) is used at the terms of a termwise
injective K-injective resolution and nowhere else, and at an injective module it is proved
outright from part (1) of Stacks 08GV:
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`. -/
theorem exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1}
        (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) (1 : ℤ),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk
            (biprod.lift
              ((Functor.rightDerivedNatTrans RX RU αX αU
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjOpen B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              ((Functor.rightDerivedNatTrans RX RV αX αV
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjEtale B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
            (biprod.desc
              ((Functor.rightDerivedNatTrans RU RP αU αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
                      ((edsAdjInter B S hS hsq).comp adjP)
                      (edsShriekOpenComparison B S hS hsq adjU adjP))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              (-((Functor.rightDerivedNatTrans RV RP αV αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
                      ((edsAdjInter B S hS hsq).comp adjP)
                      (edsShriekEtaleComparison B S hS hsq adjV adjP))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)))
            (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
            0).homologySequenceComposableArrows₅
          (Triangle.mk
            (biprod.lift
              ((Functor.rightDerivedNatTrans RX RU αX αU
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjOpen B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              ((Functor.rightDerivedNatTrans RX RV αX αV
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjEtale B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
            (biprod.desc
              ((Functor.rightDerivedNatTrans RU RP αU αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
                      ((edsAdjInter B S hS hsq).comp adjP)
                      (edsShriekOpenComparison B S hS hsq adjU adjP))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              (-((Functor.rightDerivedNatTrans RV RP αV αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
                      ((edsAdjInter B S hS hsq).comp adjP)
                      (edsShriekEtaleComparison B S hS hsq adjV adjP))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)))
            (δ.app E)) n (n + 1) rfl).Exact :=
  exists_delta_homologySequence_exact_of_exists_delta
    (exists_delta_mem_distTriang_mapMayerVietoris_of_injective
      (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
      (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
        ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
      (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
        ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
      (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
        (edsShriekOpenComparison B S hS hsq adjU adjP)
        (edsShriekEtaleComparison B S hS hsq adjV adjP)
        (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)))
      (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2)
      (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
        adjU adjV adjP M hM)
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP)

/-- **Stacks 0CRS, functoriality in `E`, with nothing granted.**

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V`.  Write `Γ(X, -)` for global sections of `𝒪_X`-modules on the
small étale ringed site, `Φ_Y = j_{Y,*}((-)|_Y)` for the three restrict-then-push composites of
the square, and let `RΓ(X, -)`, `RΓ(U, -)`, `RΓ(V, -)`, `RΓ(P, -)` be right derived functors of
`Γ(X, -)`, `Γ(X, -) ∘ Φ_U`, `Γ(X, -) ∘ Φ_V` and `Γ(X, -) ∘ Φ_P`.  Then the five maps of the
Mayer–Vietoris triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`

are the components of *natural transformations* of functors on `D(𝒪_X)`, every component
triangle is distinguished, and its homology sequence is exact at every `n`.  So a morphism
`E ⟶ E'` induces a morphism of the two triangles and of the two long exact sequences.

**The four maps are the restriction maps, written out in the statement and not existentially
quantified.**  The two out of `RΓ(X, -)` are `CategoryTheory.Functor.rightDerivedNatTrans` of
`Γ(X, -)` applied to the units `F ⟶ j_{U,*}F|_U` and `F ⟶ j_{V,*}F|_V` of the adjunctions
`(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU — that is, of the restriction maps
`Γ(X, F) ⟶ Γ(X, j_{U,*}F|_U) = Γ(U, F|_U)` and `Γ(X, F) ⟶ Γ(V, F|_V)` — and the two into
`RΓ(U ×_X V, -)` are `CategoryTheory.Functor.rightDerivedNatTrans` of `Γ(X, -)` applied to the
two comparisons `j_{U,*}F|_U ⟶ j_{P,*}F|_P` and `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW
part (1): the conjugates, under the adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the
extension-by-zero comparisons `AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` of Stacks 08GV, at the extension by zero the
library constructs (`AlgebraicGeometry.Space.edsLowerShriekAdjOpen` and its two companions).
They are the same four maps as in Stacks 08GW part (2),
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`.

Only the connecting transformation `δ : RΓ(P, -) ⟶ RΓ(X, -) ⋙ (-)[1]` is existentially
quantified: the library attaches no canonical such map to an object of `D(𝒪_X)`, and the source
likewise asserts only that a triangle with these three terms and these four maps is
distinguished, as Stacks 08GV part (2) and Stacks 08GW part (2) do.

This is `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsSectionsMayerVietoris` with
its hypothesis `hMV` — part (1) of Stacks 08GW — discharged and its four maps named.  The
sequence
`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` enters the proof only at the terms of a termwise injective
K-injective resolution of `E` (Stacks 079P,
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_injective_modules`), and at an *injective*
module it is proved outright from part (1) of Stacks 08GV:
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`.  So the
surjectivity on the right, which at a general module is the étale-local vanishing of an
obstruction in `Ext¹(𝒪_X, F) = H¹(X, F)` (Stacks 01FW) and is still the hypothesis `hepi` of
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris`, is not needed here at all.

As in the conditional statements, the three outer terms are the derived functors of
`Γ(X, -) ∘ j_{Y,*} ∘ (-)|_Y` in that factored form; that this is `RΓ(Y, E|_Y)` is the
adjunction of Stacks 03LU, `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, and is
not transported here. -/
@[stacks 0CRS "THIRD CLAUSE: functoriality in E of the distinguished triangle and of its long
exact cohomology sequence. The four maps are NAMED in the statement -- the right derived
transformations of the restriction maps RGamma(X,-) -> RGamma(U,-), RGamma(V,-) and
RGamma(U,-) -> RGamma(U x_X V,-), RGamma(V,-) -> RGamma(U x_X V,-) -- and are components of
natural transformations of functors on D(O_X); only the connecting delta is existential, as in
the source. No hypothesis beyond the square and the four derived functors presenting RGamma. The
other two clauses are exists_delta_mem_distTriang_edsSectionsMayerVietoris_unconditional and
exists_delta_homologySequence_exact_edsSectionsMayerVietoris_unconditional"]
theorem exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))) :
    ∃ δ : RP ⟶ RX ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1}
        (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) (1 : ℤ),
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        Triangle.mk
            (biprod.lift
              ((Functor.rightDerivedNatTrans RX RU αX αU
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjOpen B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              ((Functor.rightDerivedNatTrans RX RV αX αV
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjEtale B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
            (biprod.desc
              ((Functor.rightDerivedNatTrans RU RP αU αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv
                      ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
                      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                        (edsLowerShriekAdjInter B S hS hsq)))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              (-((Functor.rightDerivedNatTrans RV RP αV αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv
                      ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
                      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                        (edsLowerShriekAdjInter B S hS hsq)))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)))
            (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
            0).homologySequenceComposableArrows₅
          (Triangle.mk
            (biprod.lift
              ((Functor.rightDerivedNatTrans RX RU αX αU
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjOpen B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              ((Functor.rightDerivedNatTrans RX RV αX αV
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (mapUnit (edsAdjEtale B S hS hsq).unit
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
            (biprod.desc
              ((Functor.rightDerivedNatTrans RU RP αU αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv
                      ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
                      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                        (edsLowerShriekAdjInter B S hS hsq)))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
              (-((Functor.rightDerivedNatTrans RV RP αV αP
                (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
                (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                  (Functor.whiskerRight (conjugateEquiv
                      ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
                      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                        (edsLowerShriekAdjInter B S hS hsq)))
                    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                      ((Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS W.1 W.2).O))))
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)))
            (δ.app E)) n (n + 1) rfl).Exact :=
  exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_of_shriek B S hS hsq
    (edsLowerShriekAdjOpen B S hS hsq) (edsLowerShriekAdjEtale B S hS hsq)
    (edsLowerShriekAdjInter B S hS hsq) RX RU RV RP αX αU αV αP hRX hRU hRV hRP

/-- **Stacks 0CRS, the distinguished triangle, with nothing granted.**

In the situation of `exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`,
every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)[1]`.

**Its four first maps are the restriction maps, written out in the statement and not
existentially quantified**, exactly as in
`exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional`, whose component
at `E` this is: the right derived transformations of `Γ(X, -)` applied to the units
`F ⟶ j_{U,*}F|_U`, `F ⟶ j_{V,*}F|_V` of Stacks 03LU and to the two comparisons
`j_{U,*}F|_U ⟶ j_{P,*}F|_P`, `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW part (1).  Only the
connecting map `δ : RΓ(P, E) ⟶ RΓ(X, E)[1]` is existentially quantified, as it is in the source
and in Stacks 08GV part (2) and Stacks 08GW part (2).

This is `AlgebraicGeometry.Space.exists_mem_distTriang_edsSectionsMayerVietoris` with its
hypothesis `hMV` — part (1) of Stacks 08GW — discharged, by the same observation: the sequence
is used at an injective module only, and there it is a theorem; and with its four maps named. -/
@[stacks 0CRS "FIRST CLAUSE: every E of D(O_X) sits in a distinguished triangle
RGamma(X,E) -> RGamma(U,E) (+) RGamma(V,E) -> RGamma(U x_X V,E) -> RGamma(X,E)[1] whose four
first maps are NAMED in the statement: the right derived transformations of the restriction maps
RGamma(X,-) -> RGamma(U,-), RGamma(V,-) and RGamma(U,-), RGamma(V,-) -> RGamma(U x_X V,-). Only
the connecting delta is existential, as in the source. No hypothesis beyond the square and the
four derived functors presenting RGamma. The other two clauses are
exists_delta_homologySequence_exact_edsSectionsMayerVietoris_unconditional and
exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional"]
theorem exists_delta_mem_distTriang_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
          (biprod.lift
            ((Functor.rightDerivedNatTrans RX RU αX αU
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjOpen B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            ((Functor.rightDerivedNatTrans RX RV αX αV
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjEtale B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
          (biprod.desc
            ((Functor.rightDerivedNatTrans RU RP αU αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            (-((Functor.rightDerivedNatTrans RV RP αV αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) :=
  exists_app_mem_distTriang_of_exists_delta
    (exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional B S hS hsq
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP) E

/-- **Stacks 0CRS, the long exact cohomology sequence, with nothing granted.**

The distinguished triangle of
`AlgebraicGeometry.Space.exists_delta_mem_distTriang_edsSectionsMayerVietoris_unconditional` has an
exact homology sequence, which at each `n` is the six-term exact sequence

`H^n(X,E) ⟶ H^n(U,E) ⊕ H^n(V,E) ⟶ H^n(U ×_X V,E) ⟶ H^{n+1}(X,E) ⟶ H^{n+1}(U,E) ⊕ H^{n+1}(V,E)
⟶ H^{n+1}(U ×_X V,E)`

— the Mayer–Vietoris long exact sequence of the source, since the homology functor is additive
and so carries the biproduct `RΓ(U,E) ⊕ RΓ(V,E)` to `H^n(U,E) ⊕ H^n(V,E)`.

**Its maps are the restriction maps on cohomology**, because the triangle whose homology
sequence this is carries its four maps written out: they are the right derived transformations
of `Γ(X, -)` applied to the units `F ⟶ j_{U,*}F|_U`, `F ⟶ j_{V,*}F|_V` of Stacks 03LU and to
the two comparisons `j_{U,*}F|_U ⟶ j_{P,*}F|_P`, `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW
part (1), so the maps of the long exact sequence are `H^n` of them.  Only the connecting map
`δ`, and with it `H^n(U ×_X V,E) ⟶ H^{n+1}(X,E)`, is existentially quantified, as in the
source.

This is `AlgebraicGeometry.Space.exists_homologySequence_exact_edsSectionsMayerVietoris` with
its hypothesis `hMV` — part (1) of Stacks 08GW — discharged and its four maps named. -/
@[stacks 0CRS "SECOND CLAUSE: every E of D(O_X) sits in a long exact cohomology sequence
... -> H^n(X,E) -> H^n(U,E) (+) H^n(V,E) -> H^n(U x_X V,E) -> H^{n+1}(X,E) -> ... whose maps are
H^n of the NAMED restriction maps -- the triangle it is the homology sequence of has its four
first maps written out, the right derived transformations of RGamma(X,-) -> RGamma(U,-),
RGamma(V,-) and RGamma(U,-), RGamma(V,-) -> RGamma(U x_X V,-); only the connecting delta is
existential, as in the source. No hypothesis beyond the square and the four derived functors
presenting RGamma. It is the homology sequence of the triangle of
exists_delta_mem_distTriang_edsSectionsMayerVietoris_unconditional; functoriality is
exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional"]
theorem exists_delta_homologySequence_exact_edsSectionsMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj)))
    (αX : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (edsRestrictPushOpen B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
          (biprod.lift
            ((Functor.rightDerivedNatTrans RX RU αX αU
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjOpen B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            ((Functor.rightDerivedNatTrans RX RV αX αV
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjEtale B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
          (biprod.desc
            ((Functor.rightDerivedNatTrans RU RP αU αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            (-((Functor.rightDerivedNatTrans RV RP αV αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))) ∧
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj))
          0).homologySequenceComposableArrows₅
        (Triangle.mk
          (biprod.lift
            ((Functor.rightDerivedNatTrans RX RU αX αU
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjOpen B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            ((Functor.rightDerivedNatTrans RX RV αX αV
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (mapUnit (edsAdjEtale B S hS hsq).unit
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))
          (biprod.desc
            ((Functor.rightDerivedNatTrans RU RP αU αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
            (-((Functor.rightDerivedNatTrans RV RP αV αP
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (Functor.whiskerRight (conjugateEquiv
                    ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
                    ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                    (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                      (edsLowerShriekAdjInter B S hS hsq)))
                  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
                    ((Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS W.1 W.2).O))))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))) δ) n (n + 1) rfl).Exact :=
  exists_app_homologySequence_exact_of_exists_delta
    (exists_delta_natTrans_mem_distTriang_edsSectionsMayerVietoris_unconditional B S hS hsq
      RX RU RV RP αX αU αV αP hRX hRU hRV hRP) E

end Unconditional

end AlgebraicGeometry.Space

end
