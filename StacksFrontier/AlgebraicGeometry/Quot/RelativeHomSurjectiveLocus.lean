module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Quot.TestSchemeTotalSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace

/-!
# The locus of surjections in a representation of the relative Hom functor

Let `Hom(F, G)` be the relative Hom functor of Stacks 08JT for a morphism `f : X ⟶ Y` of
algebraic spaces and quasi-coherent `𝒪_X`-modules `F`, `G`, and let `H` be an algebraic space
over `Y` representing it, as Stacks 08K6 provides.  A section `h` of `H` over a scheme `T`
corresponds to a homomorphism `u_h : F_T ⟶ G_T`; the sections whose homomorphism is surjective
form a subfunctor of `H`.  This file shows that it is an open subspace of `H` when `f` is locally
of finite presentation, `G` is of finite type and the support of `G` is proper over `Y`: its
inverse image under a scheme-valued point `h` is the open subspace of Stacks 09TP for the map
`u_h`.  This is the open subspace of the proof of Stacks 09TU.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.sectionHom`: the homomorphism `F_T ⟶ G_T` a section of
  the representing space corresponds to.
* `AlgebraicGeometry.Space.HomSituation.surjLocus`: the subfunctor of the sections whose
  homomorphism is surjective.

## Main results

* `AlgebraicGeometry.Space.HomSituation.sectionHom_map`: the homomorphism of a restricted section
  is the pullback of the homomorphism.
* `AlgebraicGeometry.Space.HomSituation.isOpenSubspace_surjLocus`: the locus of surjections is an
  open subspace.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]

/-- The conjugate of a morphism by a comparison of functors is an epimorphism exactly when the
image of the morphism is. -/
theorem epi_conjHom_iff {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (α : P₁.obj M ⟶ P₁.obj N) : Epi (conjHom e α) ↔ Epi (L.map α) := by
  refine ⟨fun _ => ?_, fun _ => by unfold conjHom; infer_instance⟩
  rw [show L.map α = e.inv.app M ≫ conjHom e α ≫ e.hom.app N by simp [conjHom]]
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory

/-- A morphism conjugated by two isomorphisms is an epimorphism as soon as it is one. -/
theorem epi_iso_hom_comp_comp_iso_hom {C : Type*} [Category* C] {X Y Z W : C} (e : X ≅ Y)
    (f : Y ⟶ Z) (e' : Z ≅ W) (hf : Epi f) : Epi (e.hom ≫ f ≫ e'.hom) :=
  inferInstance

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Surjectivity of inverse images along isomorphic base changes -/

/-- The inverse image of an epimorphism along `a'` stays an epimorphism after a further inverse
image along any `b`: inverse image is a left adjoint. -/
theorem epi_modulePullback_map_of_comp {W W' X : AlgebraicSpaces B S hS} {a : W ⟶ X}
    {a' : W' ⟶ X} (b : W ⟶ W') (h : b ≫ a' = a) {M N : Modules.{u, u} B S hS X.1 X.2}
    (v : M ⟶ N) (hv : Epi ((modulePullback B S hS a').map v)) :
    Epi ((modulePullback B S hS a).map v) := by
  have := Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS b)
  have hb : Epi ((modulePullback B S hS b).map ((modulePullback B S hS a').map v)) :=
    Functor.map_epi _ _
  rw [← NatIso.naturality_2 (modulePullbackTriangle B S hS h) v, Functor.comp_map]
  exact epi_iso_hom_comp_comp_iso_hom ((modulePullbackTriangle B S hS h).app M) _
    ((modulePullbackTriangle B S hS h).app N).symm hb

/-- Inverse images along two morphisms which differ by an isomorphism of their sources reflect
each other's epimorphisms. -/
theorem epi_modulePullback_map_iff_of_iso {W W' X : AlgebraicSpaces B S hS} {a : W ⟶ X}
    {a' : W' ⟶ X} (φ : W ≅ W') (h : φ.hom ≫ a' = a) {M N : Modules.{u, u} B S hS X.1 X.2}
    (v : M ⟶ N) :
    Epi ((modulePullback B S hS a).map v) ↔ Epi ((modulePullback B S hS a').map v) :=
  ⟨fun hv => epi_modulePullback_map_of_comp φ.inv (by rw [← h, Iso.inv_hom_id_assoc]) v hv,
    fun hv => epi_modulePullback_map_of_comp φ.hom h v hv⟩

/-- **Inverse image along an isomorphism reflects surjections.** -/
theorem epi_of_epi_modulePullback_map_of_isIso (hc : ModulePushforwardCoherence B S hS)
    {W X : AlgebraicSpaces B S hS} (b : W ⟶ X) [IsIso b] {M N : Modules.{u, u} B S hS X.1 X.2}
    (v : M ⟶ N) (hv : Epi ((modulePullback B S hS b).map v)) : Epi v := by
  have h₁ : Epi ((modulePullback B S hS (𝟙 X)).map v) :=
    (epi_modulePullback_map_iff_of_iso (asIso b) (Category.comp_id b) v).1 hv
  have h₂ : (hc.modulePullbackIdIso X).symm.hom.app M ≫ (modulePullback B S hS (𝟙 X)).map v ≫
      (hc.modulePullbackIdIso X).symm.inv.app N = v :=
    NatIso.naturality_2 (hc.modulePullbackIdIso X).symm v
  rw [← h₂]
  exact epi_iso_hom_comp_comp_iso_hom ((hc.modulePullbackIdIso X).symm.app M) _
    ((hc.modulePullbackIdIso X).app N) h₁

/-- **Conjugation by a comparison whose last factor is the inverse image along an isomorphism
reflects surjections.** -/
theorem epi_of_epi_conjHom_of_isIso (hc : ModulePushforwardCoherence B S hS)
    {C : Type*} [Category* C] {W X : AlgebraicSpaces B S hS} (b : W ⟶ X) [IsIso b]
    {P₁ : C ⥤ Modules.{u, u} B S hS X.1 X.2} {P₂ : C ⥤ Modules.{u, u} B S hS W.1 W.2}
    (e : P₂ ≅ P₁ ⋙ modulePullback B S hS b) {M N : C} (α : P₁.obj M ⟶ P₁.obj N)
    (h : Epi (Functor.conjHom e α)) : Epi α :=
  epi_of_epi_modulePullback_map_of_isIso hc b α ((Functor.epi_conjHom_iff e α).1 h)

/-- A morphism from a representable presheaf to `yoneda.obj T` factors through a subfunctor
exactly when the morphism of schemes it is lies in the subfunctor. -/
theorem exists_comp_ι_eq_yoneda_map_iff {T T' : BigFppfOver B S hS}
    (U : Subfunctor (yoneda.obj T)) (k : T' ⟶ T) :
    (∃ k' : yoneda.obj T' ⟶ U.toFunctor, k' ≫ U.ι = yoneda.map k) ↔ k ∈ U.obj (op T') :=
  ⟨fun ⟨k', hk'⟩ =>
    ((congrArg (fun t => t.app (op T') (𝟙 T')) hk').trans (Category.id_comp k)) ▸
      (k'.app (op T') (𝟙 T')).2,
    fun hk => ⟨yonedaEquiv.symm ⟨k, hk⟩, by ext; rfl⟩⟩

/-- Surjectivity at a test scheme, for the inverse images of `𝒪`-modules, is surjectivity of the
inverse image of the map along the base-change projection. -/
theorem ModuleMapSituation.isSurjectiveAt_modulePullbackSystem_iff
    (D : ModuleMapSituation.{u, u} B S hS) (T : D.SchemesOver) :
    D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      Epi ((modulePullback B S hS (D.baseChangeProjection T)).map D.u) :=
  Iff.rfl

namespace HomSituation

variable (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)
  {H : AlgebraicSpaces B S hS} (p : H ⟶ s.base)
  (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.homFunctor hc)

/-- The test scheme over the base of a section of `H`: the scheme it is a section over, with the
image of the section in the base. -/
abbrev sectionTest {T : BigFppfOver B S hS} (h : H.1.obj (op T)) : s.SchemesOver :=
  testOf T (p.hom.app (op T) h)

/-- A section of `H` as a point of `H` over the base at its own test scheme. -/
def sectionPoint {T : BigFppfOver B S hS} (h : H.1.obj (op T)) :
    spacePointsOverObj p (s.sectionTest p h) :=
  ⟨h, (testPoint_testOf T (p.hom.app (op T) h)).symm⟩

/-- **The homomorphism `F_T ⟶ G_T` a section of the representing space corresponds to.** -/
def sectionHom {T : BigFppfOver B S hS} (h : H.1.obj (op T)) :
    s.homAt (s.sectionTest p h) :=
  c.hom.app (op (s.sectionTest p h)) (ULift.up (s.sectionPoint p h))

/-- The morphism of test schemes over the base underlying the restriction of a section. -/
def sectionTestMap {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (h : H.1.obj (op T)) :
    s.sectionTest p (H.1.map g.op h) ⟶ s.sectionTest p h :=
  CostructuredArrow.homMk g (by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map g ≫ yonedaEquiv.symm (p.hom.app (op T) h) =
      yonedaEquiv.symm (p.hom.app (op T') (H.1.map g.op h))
    rw [NatTrans.naturality_apply, yonedaEquiv_symm_map]
    rfl)

/-- The correspondence `c` is natural: restricting a point of `H` along a morphism of test schemes
pulls back its homomorphism. -/
private theorem hom_app_map_eq_homMap {Tt Tt' : s.SchemesOver} (g : Tt' ⟶ Tt)
    (x : (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj (op Tt)) :
    c.hom.app (op Tt') ((spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).map g.op x) =
      s.homMap g (c.hom.app (op Tt) x) :=
  (NatTrans.naturality_apply c.hom g.op x).trans
    ((congrArg (fun φ : (s.homFunctor hc).obj (op Tt) ⟶ (s.homFunctor hc).obj (op Tt') =>
      φ (c.hom.app (op Tt) x)) (s.homFunctor_map hc g)).trans rfl)

/-- **The homomorphism of a restricted section is the pullback of the homomorphism of the
section.** -/
theorem sectionHom_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (h : H.1.obj (op T)) :
    s.sectionHom hc p c (H.1.map g.op h) =
      s.homMap (s.sectionTestMap p g h) (s.sectionHom hc p c h) := by
  exact s.hom_app_map_eq_homMap hc p c (s.sectionTestMap p g h) (ULift.up (s.sectionPoint p h))

/-- **The locus of surjections**: the sections of `H` whose homomorphism `F_T ⟶ G_T` is an
epimorphism. -/
def surjLocus : Subfunctor H.1 where
  obj T := {h | Epi (s.toModuleHom (s.sectionHom hc p c h))}
  map {T T'} g h hh := by
    change Epi (s.toModuleHom (s.sectionHom hc p c (H.1.map g.unop.op h)))
    rw [s.sectionHom_map hc p c g.unop h, s.toModuleHom_homMap, Functor.epi_conjHom_iff]
    have : Epi (s.toModuleHom (s.sectionHom hc p c h)) := hh
    have := Functor.preservesEpimorphisms_of_adjunction
      (modulePullbackAdjunction B S hS (baseChangeMap s.f (s.sectionTestMap p g.unop h)))
    exact Functor.map_epi _ _

/-- A section of `H` lies in the locus of surjections exactly when its homomorphism
`F_T ⟶ G_T` is an epimorphism. -/
theorem mem_surjLocus_iff {T : BigFppfOver B S hS} (h : H.1.obj (op T)) :
    h ∈ (s.surjLocus hc p c).obj (op T) ↔ Epi (s.toModuleHom (s.sectionHom hc p c h)) :=
  Iff.rfl

/-- The morphism from the test scheme of a point of `H` over the base to the test scheme it is a
point at, the identity of the underlying scheme. -/
def pointTestMap {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt) :
    s.sectionTest p x.1 ⟶ Tt :=
  CostructuredArrow.homMk (𝟙 Tt.left) (by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map (𝟙 Tt.left) ≫ Tt.hom.hom = yonedaEquiv.symm (p.hom.app (op Tt.left) x.1)
    rw [x.2, yonedaEquiv_symm_testPoint, CategoryTheory.Functor.map_id]
    exact Category.id_comp _)

/-- The homomorphism `F_T ⟶ G_T` a point of `H` over the base at a test scheme `T` corresponds
to. -/
def pointHom {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt) : s.homAt Tt :=
  c.hom.app (op Tt) (ULift.up.{u + 1} x)

/-- The homomorphism of a section of `H` which is a point at a test scheme `T` is the pullback
of the homomorphism at `T` along the identification of the two test schemes. -/
theorem sectionHom_eq_homMap {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt) :
    s.sectionHom hc p c x.1 = s.homMap (s.pointTestMap p x) (s.pointHom hc p c x) := by
  have hpt : (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).map (s.pointTestMap p x).op
      (ULift.up.{u + 1} x) = ULift.up.{u + 1} (s.sectionPoint p x.1) :=
    congrArg ULift.up (Subtype.ext (by exact Functor.map_id_apply H.1 _ x.1))
  exact (congrArg _ hpt.symm).trans (s.hom_app_map_eq_homMap hc p c _ _)

/-- The identification of the two test schemes of a point is an isomorphism. -/
instance isIso_pointTestMap {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt) :
    IsIso (s.pointTestMap p x) :=
  ⟨⟨CostructuredArrow.homMk (𝟙 Tt.left) (by
      refine ObjectProperty.hom_ext _ ?_
      change yoneda.map (𝟙 Tt.left) ≫ yonedaEquiv.symm (p.hom.app (op Tt.left) x.1) = Tt.hom.hom
      rw [x.2, yonedaEquiv_symm_testPoint, CategoryTheory.Functor.map_id]
      exact Category.id_comp _),
    CostructuredArrow.hom_ext _ _ (Category.id_comp _),
    CostructuredArrow.hom_ext _ _ (Category.id_comp _)⟩⟩

/-- The morphism of base changes along an isomorphism of test schemes is an isomorphism. -/
instance isIso_baseChangeMap {U T : s.SchemesOver} (g : U ⟶ T) [IsIso g] :
    IsIso (baseChangeMap s.f g) :=
  ⟨⟨baseChangeMap s.f (inv g), by rw [← baseChangeMap_comp, IsIso.hom_inv_id, baseChangeMap_id],
    by rw [← baseChangeMap_comp, IsIso.inv_hom_id, baseChangeMap_id]⟩⟩

/-- **The homomorphism of a point in the locus of surjections is surjective.** -/
theorem epi_pointHom_of_mem {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt)
    (hx : x.1 ∈ (s.surjLocus hc p c).obj (op Tt.left)) :
    Epi (s.toModuleHom (s.pointHom hc p c x)) := by
  have hx' : Epi (s.toModuleHom (s.homMap (s.pointTestMap p x) (s.pointHom hc p c x))) := by
    rw [← s.sectionHom_eq_homMap hc p c x]
    exact hx
  rw [s.toModuleHom_homMap] at hx'
  exact epi_of_epi_conjHom_of_isIso hc (baseChangeMap s.f (s.pointTestMap p x))
    (s.baseChangeComparison (s.pointTestMap p x)) _ hx'

/-- **A point whose homomorphism is surjective lies in the locus of surjections.** -/
theorem mem_surjLocus_of_epi {Tt : s.SchemesOver} (x : spacePointsOverObj p Tt)
    (hx : Epi (s.toModuleHom (s.pointHom hc p c x))) :
    x.1 ∈ (s.surjLocus hc p c).obj (op Tt.left) := by
  rw [mem_surjLocus_iff, s.sectionHom_eq_homMap hc p c x, s.toModuleHom_homMap,
    Functor.epi_conjHom_iff]
  have := Functor.preservesEpimorphisms_of_adjunction
    (modulePullbackAdjunction B S hS (baseChangeMap s.f (s.pointTestMap p x)))
  exact Functor.map_epi _ _

/-! ### The locus of surjections is open -/

/-- **The situation of Stacks 083F attached to a homomorphism over a test scheme**: the base
change `X_T ⟶ T` of the morphism, the two base-changed modules, and the homomorphism. -/
abbrev mapSituationAt (Tt : s.SchemesOver)
    (v : s.baseChangedModule Tt s.F ⟶ s.baseChangedModule Tt s.G) :
    ModuleMapSituation.{u, u} B S hS where
  X := s.baseChange Tt
  Y := (schemeSpaceFunctor B S hS).obj Tt.left
  f := baseChangeInclusion s.f Tt
  F := s.baseChangedModule Tt s.F
  G := s.baseChangedModule Tt s.G
  quasicoherent_F := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ s.F
    s.quasicoherent_F
  quasicoherent_G := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ s.G
    s.quasicoherent_G
  u := v

/-- The test scheme of the situation over `T` attached to a morphism of test schemes into `T`. -/
abbrev mapSituationTest {Tt Tt' : s.SchemesOver}
    (v : s.baseChangedModule Tt s.F ⟶ s.baseChangedModule Tt s.G) (g : Tt' ⟶ Tt) :
    (s.mapSituationAt Tt v).SchemesOver :=
  CostructuredArrow.mk (Y := Tt'.left) ((schemeSpaceFunctor B S hS).map g.left)

/-- The homomorphism of the situation attached to `v` is `v`, read in either spelling of the
base change. -/
theorem epi_map_mapSituationAt_u_iff {Tt : s.SchemesOver} {W : AlgebraicSpaces B S hS}
    (v : s.baseChangedModule Tt s.F ⟶ s.baseChangedModule Tt s.G)
    (b : W ⟶ (s.mapSituationAt Tt v).X) :
    Epi ((modulePullback B S hS (Y := (s.mapSituationAt Tt v).X) b).map
        (s.mapSituationAt Tt v).u) ↔
      Epi ((modulePullback B S hS (Y := s.baseChange Tt) b).map v) :=
  Iff.rfl

/-- **Surjectivity in the sense of Stacks 083F at a test scheme over `T` is surjectivity of the
inverse image along the morphism of base changes.** -/
theorem isSurjectiveAt_mapSituationTest_iff {Tt Tt' : s.SchemesOver}
    (v : s.baseChangedModule Tt s.F ⟶ s.baseChangedModule Tt s.G) (g : Tt' ⟶ Tt) :
    (s.mapSituationAt Tt v).IsSurjectiveAt (modulePullbackSystem B S hS)
        (s.mapSituationTest v g) ↔
      Epi ((modulePullback B S hS (baseChangeMap s.f g)).map v) := by
  have hpb₁ := isPullback_baseChangeMap s.f g
  have hpb₂ : IsPullback ((s.mapSituationAt Tt v).baseChangeProjection (s.mapSituationTest v g))
      ((s.mapSituationAt Tt v).baseChangeInclusion (s.mapSituationTest v g))
      (s.mapSituationAt Tt v).f (s.mapSituationTest v g).hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS
      (s.mapSituationAt Tt v).f (s.mapSituationTest v g).hom
  rw [ModuleMapSituation.isSurjectiveAt_modulePullbackSystem_iff,
    ← s.epi_map_mapSituationAt_u_iff v (baseChangeMap s.f g)]
  exact (epi_modulePullback_map_iff_of_iso (X := (s.mapSituationAt Tt v).X)
    (M := (s.mapSituationAt Tt v).F) (N := (s.mapSituationAt Tt v).G)
    (hpb₁.isoIsPullback _ _ hpb₂) (hpb₁.isoIsPullback_hom_fst _ _ hpb₂)
    (s.mapSituationAt Tt v).u).symm

/-- The situation of Stacks 083F at a section of `H`. -/
abbrev sectionMapSituation {T : BigFppfOver B S hS} (h : H.1.obj (op T)) :
    ModuleMapSituation.{u, u} B S hS :=
  s.mapSituationAt (s.sectionTest p h) (s.toModuleHom (s.sectionHom hc p c h))

/-- **Surjectivity of the homomorphism of a restricted section is surjectivity of the base change
of the homomorphism of the section**, in the sense of Stacks 083F. -/
theorem isSurjectiveAt_sectionMapTest_iff {T T' : BigFppfOver B S hS} (h : H.1.obj (op T))
    (k : T' ⟶ T) :
    (s.sectionMapSituation hc p c h).IsSurjectiveAt (modulePullbackSystem B S hS)
        (s.mapSituationTest (s.toModuleHom (s.sectionHom hc p c h)) (s.sectionTestMap p k h)) ↔
      H.1.map k.op h ∈ (s.surjLocus hc p c).obj (op T') := by
  rw [s.isSurjectiveAt_mapSituationTest_iff, mem_surjLocus_iff, s.sectionHom_map hc p c k h,
    s.toModuleHom_homMap, Functor.epi_conjHom_iff]

/-- The inverse image of the locus of surjections under a scheme-valued point is an open
subspace: it is the open subspace of Stacks 09TP for the homomorphism of the point. -/
theorem isOpenSubspace_preimage_surjLocus (hf : IsLocallyOfFinitePresentation B S hS s.f.hom)
    (hG : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hproper : HasProperSupport B S hS s.X.property s.base.property s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj s.G))
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ H.1) :
    IsOpenSubspace B S hS ((s.surjLocus hc p c).preimage g) := by
  set h := yonedaEquiv g with hh
  let M := s.sectionMapSituation hc p c h
  have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS s.f
    ((schemesOverToOver s.base).obj (s.sectionTest p h)).hom
  have hMf : IsLocallyOfFinitePresentation B S hS M.f.hom :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq hf
  have hMG : SheafOfModules.IsFiniteTypeOnSite M.G :=
    isFiniteTypeOnSite_modulePullback B S hS _ s.G hG
  have hMproper : HasProperSupport B S hS M.X.property M.Y.property M.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hMf)
      ((SheafOfModules.toSheaf _).obj M.G) :=
    ⟨isClosed_supportOfSheaf_modulePullback B S hS _ s.G hG,
      isProperOver_supportOfSheaf_modulePullback B S hS hsq
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf) s.G
        s.quasicoherent_G hG hproper.2⟩
  obtain ⟨U, hU, hiff⟩ := M.exists_isOpenSubspace_isSurjectiveAt_iff hMf hMG hMproper
  have hEq : (s.surjLocus hc p c).preimage g = U := by
    refine Subfunctor.ext (funext fun T' => Set.ext fun k => ?_)
    show g.app T' k ∈ (s.surjLocus hc p c).obj T' ↔ k ∈ U.obj T'
    have hgk : g.app T' k = H.1.map k.op h := by
      rw [hh, map_yonedaEquiv']
      rfl
    rw [hgk, ← s.isSurjectiveAt_sectionMapTest_iff hc p c h k,
      hiff (s.mapSituationTest (s.toModuleHom (s.sectionHom hc p c h)) (s.sectionTestMap p k h))]
    exact exists_comp_ι_eq_yoneda_map_iff U k
  rw [hEq]
  exact hU

/-- **The locus of surjections is an open subspace** of the space representing the relative Hom
functor, when `f` is locally of finite presentation, `G` is of finite type and the support of
`G` is proper over the base. -/
theorem isOpenSubspace_surjLocus (hf : IsLocallyOfFinitePresentation B S hS s.f.hom)
    (hG : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hproper : HasProperSupport B S hS s.X.property s.base.property s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj s.G)) :
    IsOpenSubspace B S hS (s.surjLocus hc p c) := by
  have hι : IsOpenImmersion B S hS (s.surjLocus hc p c).ι :=
    isOpenImmersion_of_isOpenSubspace_range_preimage B S hS _ fun T g => by
      rw [Subfunctor.range_ι]
      exact s.isOpenSubspace_preimage_surjLocus hc p c hf hG hproper T g
  exact ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS _ hι.1 H.2, hι⟩

end HomSituation

end AlgebraicGeometry.Space

end
