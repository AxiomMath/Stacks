module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionGroupoidModules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModule

/-!
# Descending a quasi-coherent module from the presenting scheme of an algebraic space

Let `X = U/R` be a presentation of an algebraic space (Stacks 0263): a surjective étale atlas
`U ⟶ X` from a scheme and its kernel pair `R = U ×_X U`, with target and source projections
`t, s : R ⟶ U`.  Let `M` be a quasi-coherent module on the scheme `U` and
`τ : t^*M ⟶ s^*M` a morphism of modules on the scheme `R`, satisfying the cocycle condition on
the scheme of composable pairs `R ×_U R` and the unit condition along the diagonal `U ⟶ R`, both
read on schemes.  Then `(M, τ)` descends to a quasi-coherent `𝒪_X`-module whose inverse image
along the atlas is (the module attached through Stacks 03DX (2) to) `M`, compatibly with `τ`;
and a morphism of such data on the scheme `U` descends uniquely.

## Main definitions

* `AlgebraicGeometry.Space.representedSchemeTransition`: the transition morphism
  `τ^a : t^*(M^a) ⟶ s^*(M^a)` attached to a scheme transition `τ : t^*M ⟶ s^*M` along two
  morphisms `t, s : R ⟶ U` of the site, and
  `AlgebraicGeometry.Space.schemeTransitionReindex` the reindexing `h^*τ : (h ≫ t)^*M ⟶
  (h ≫ s)^*M` of `τ` along a morphism `h` of the site into `R`, on schemes.
* `AlgebraicGeometry.Space.PresentationSchemeCocycle` and
  `AlgebraicGeometry.Space.PresentationSchemeUnit`: the cocycle condition of `τ` on `R ×_U R`
  (`AlgebraicGeometry.Space.presentationDouble`) and its unit condition along the diagonal
  (`AlgebraicGeometry.Space.presentationDiag`), on schemes.
* `AlgebraicGeometry.Space.presentationSchemeModule`: the quasi-coherent module `(M^a, τ^a)` on
  the groupoid of a presentation (Stacks 0441).
* `AlgebraicGeometry.Space.presentationQuasicoherentEquivalence`: the equivalence of Stacks 03M3
  for the groupoid of a presentation.
* `AlgebraicGeometry.Space.presentationDescendedModule`: **the descended quasi-coherent
  `𝒪_X`-module**, with `AlgebraicGeometry.Space.presentationDescendedModuleCounitIso` the
  identification of its groupoid module with `(M^a, τ^a)` and
  `AlgebraicGeometry.Space.presentationDescendedModuleChartIso` the resulting identification of
  its inverse image along the atlas with `M^a`.
* `AlgebraicGeometry.Space.presentationDescendedHom`: the descent of a morphism of scheme data.
* `AlgebraicGeometry.Space.TransitionCommutes`: the square `α ≫ b^*f = a^*f ≫ β` saying that a
  morphism of modules carries one transition morphism to another.

## Main results

* `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_naturality`: the
  identification `g^*(M^a) ≅ (g^*M)^a` is natural in `M`.
* `AlgebraicGeometry.Space.transitionReindex_representedSchemeTransition`: the reindexing of
  `τ^a` along a represented morphism `h` is `(h^*τ)^a`.
* `AlgebraicGeometry.Space.transitionCocycle_representedSchemeTransition` and
  `AlgebraicGeometry.Space.transitionUnit_representedSchemeTransition`: the cocycle and unit laws
  of `τ^a` at represented morphisms, from those of `τ` on schemes.
* `AlgebraicGeometry.Space.composableToPresentationDouble_comp_comp` and
  `AlgebraicGeometry.Space.identityArrow_presentationGroupoid`: the composition and the unit of
  the groupoid of a presentation are read off the scheme composition leg and diagonal.
* `AlgebraicGeometry.Space.presentationDescendedModuleChartIso_comm`: the chart identification
  carries the canonical transition morphism of the inverse image
  (`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_functor_obj_alpha`) to `τ^a`.
* `AlgebraicGeometry.Space.existsUnique_presentationDescendedHom`, with
  `AlgebraicGeometry.Space.presentationDescendedHom_spec` and
  `AlgebraicGeometry.Space.presentationDescendedHom_unique`: **a morphism of scheme data descends
  uniquely** to a morphism of the descended `𝒪_X`-modules whose inverse image along the atlas is
  the given one.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Naturality of the identification `g^*(M^a) ≅ (g^*M)^a` -/

section Naturality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback of a morphism of quasi-coherent modules on the scheme underlying `U` along a
morphism `g : V ⟶ U` of the site, as a morphism of quasi-coherent modules on the scheme
underlying `V`. -/
abbrev quasicoherentPullbackMap {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    quasicoherentPullbackObj B S hS g M ⟶ quasicoherentPullbackObj B S hS g N :=
  ObjectProperty.homMk ((Scheme.Modules.pullback
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map φ.hom)

/-- A naturality square read through a functor, from three squares and two readings. -/
private theorem map_comp_eq_map_comp_of_readings {E C C' : Type*} [Category E] [Category C]
    [Category C'] (ρ : E ⥤ C) (Pb : C' ⥤ C) {a a' k k' : E} {c c' m n : C'}
    (A : a ⟶ a') (cM : a ≅ k) (cN : a' ≅ k') (Y : k ⟶ k') (x : c ⟶ c') (φ : m ⟶ n)
    (iM : Pb.obj c ≅ ρ.obj a) (iN : Pb.obj c' ≅ ρ.obj a') (bM : c ≅ m) (bN : c' ≅ n)
    (gM : ρ.obj k ≅ Pb.obj m) (gN : ρ.obj k' ≅ Pb.obj n)
    (e1 : ρ.map cM.hom = iM.inv ≫ (Pb.mapIso bM).hom ≫ gM.inv)
    (e2 : ρ.map cN.hom = iN.inv ≫ (Pb.mapIso bN).hom ≫ gN.inv)
    (n1 : Pb.map x ≫ iN.hom = iM.hom ≫ ρ.map A)
    (n2 : φ ≫ bN.inv = bM.inv ≫ x)
    (n3 : Pb.map φ ≫ gN.inv = gM.inv ≫ ρ.map Y) :
    ρ.map (A ≫ cN.hom) = ρ.map (cM.hom ≫ Y) := by
  have hA : ρ.map A = iM.inv ≫ Pb.map x ≫ iN.hom := by rw [n1, Iso.inv_hom_id_assoc]
  have hx : x = bM.hom ≫ φ ≫ bN.inv := by rw [n2, Iso.hom_inv_id_assoc]
  rw [ρ.map_comp, ρ.map_comp, e1, e2, hA, hx]
  simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    ← n3]
  rw [Iso.inv_hom_id_map_assoc]

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` is natural in `M`.**  For `g : V ⟶ U` of the
site and a morphism `φ : M ⟶ N` of quasi-coherent modules on the scheme underlying `U`, the
inverse image along `g` of the morphism of attached `𝒪`-modules corresponds to the module
attached to the pullback of `φ`. -/
theorem modulePullbackRepresentedQuasicoherentIso_naturality {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map φ).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom =
    (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
        (quasicoherentPullbackMap B S hS g φ)).hom := by
  have hM := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property
  have hN := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).property
  refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) _ hM)).1 ?_
  have e1 := congrArg Iso.hom
    (representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso B S hS g M)
  have e2 := congrArg Iso.hom
    (representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso B S hS g N)
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] at e1 e2
  exact map_comp_eq_map_comp_of_readings
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    _ _ _ _ _ _ _ _ _ _ _ _ e1 e2
    (representedZariskiModulePullbackIso_naturality B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) hM hN
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map φ).hom)
    (representedZariskiModuleQuasicoherentSchemeIso_naturality B S hS φ)
    (representedZariskiModuleQuasicoherentSchemeIso_naturality B S hS
      (quasicoherentPullbackMap B S hS g φ))

end Naturality

/-! ### The transition morphism attached to a scheme transition, and its reindexings -/

section Reindex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of modules carries one transition morphism to another**: for `f : ℱ ⟶ 𝒢` of
modules on `U` and transition morphisms `α : a^*ℱ ⟶ b^*ℱ`, `β : a^*𝒢 ⟶ b^*𝒢` along two morphisms
`a, b : V ⟶ U`, the square `α ≫ b^*f = a^*f ≫ β`. -/
def TransitionCommutes {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G) (f : F ⟶ G) :
    Prop :=
  α ≫ (modulePullback B S hS b).map f = (modulePullback B S hS a).map f ≫ β

/-- The compatibility of a morphism of quasi-coherent modules on a groupoid is
`AlgebraicGeometry.Space.TransitionCommutes` at the target and the source of the groupoid. -/
theorem QuasicoherentModule.compatible_iff_transitionCommutes {A : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS A} {M N : QuasicoherentModule B S hS G}
    (h : M.F.obj ⟶ N.F.obj) :
    QuasicoherentModule.Compatible h ↔
      TransitionCommutes B S hS (U := G.objects) (V := G.arrows) (a := G.target) (b := G.source)
        M.alpha N.alpha h :=
  Iff.rfl

variable {U R : BigFppfOver B S hS} (t s : R ⟶ U)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)

/-- **The transition morphism `τ^a : t^*(M^a) ⟶ s^*(M^a)` attached to a scheme transition
`τ : t^*M ⟶ s^*M`.**  For morphisms `t, s : R ⟶ U` of the site and a quasi-coherent module `M` on
the scheme underlying `U`, the module attached to `τ` through Stacks 03DX (2), read between the
inverse images of `M^a` along the represented morphisms through
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`. -/
def representedSchemeTransition :
    (modulePullback B S hS (representedSpaceMap B S hS t)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ⟶
      (modulePullback B S hS (representedSpaceMap B S hS s)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj :=
  (modulePullbackRepresentedQuasicoherentIso B S hS t M).hom ≫
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map τ).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS s M).inv

/-- **The reindexing `h^*τ : (h ≫ t)^*M ⟶ (h ≫ s)^*M` of a scheme transition** along a morphism
`h : V ⟶ R` of the site: the pullback of `τ` along `h`, between the contractions of the two
pullbacks. -/
def schemeTransitionReindex {V : BigFppfOver B S hS} (h : V ⟶ R) :
    quasicoherentPullbackObj B S hS (h ≫ t) M ⟶ quasicoherentPullbackObj B S hS (h ≫ s) M :=
  (quasicoherentPullbackCompIso B S hS h t M).inv ≫ quasicoherentPullbackMap B S hS h τ ≫
    (quasicoherentPullbackCompIso B S hS h s M).hom

/-- The transport along an equality of morphisms, inside the contraction isomorphism of two
inverse images of represented morphisms, is `AlgebraicGeometry.Space.pullbackTransport`. -/
private theorem eqToIso_congrArg_modulePullback_app_hom {T Y : AlgebraicSpaces B S hS}
    {a b : T ⟶ Y} (h : a = b) (F : Modules.{u, u} B S hS Y.1 Y.2) :
    ((eqToIso (congrArg (modulePullback B S hS) h)).app F).hom = pullbackTransport F h := by
  subst h
  rfl

/-- Transporting along an equality of morphisms and back is the identity. -/
private theorem pullbackTransport_comp_symm {T Y : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Y.1 Y.2) {a b : T ⟶ Y} (h : a = b) :
    pullbackTransport F h ≫ pullbackTransport F h.symm = 𝟙 _ := by
  subst h
  simp [pullbackTransport]

/-- The contraction isomorphism of the inverse images along two represented morphisms is the
contraction of Stacks 03LU followed by the transport to the represented composite. -/
private theorem representedModulePullbackCompIso_app_hom {W V U : BigFppfOver B S hS}
    (h : W ⟶ V) (g : V ⟶ U)
    (F : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2) :
    ((representedModulePullbackCompIso B S hS h g).app F).hom =
      ((modulePullbackCompIso B S hS (X := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (Y := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (Z := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)).app F).hom ≫
        pullbackTransport (T := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) F
          (representedSpaceMap_comp B S hS h g) := by
  rw [NatIso.trans_app, Iso.trans_hom, eqToIso_congrArg_modulePullback_app_hom]

/-- Conjugating `Pg.map α` by `cT` and `cS`, for `α` factoring through `τR`, gives the composite
through `Z`, given the compatibilities `hcT`, `hcS`, `ha₀`, `hb₀`, `hd` and `hZ`. -/
private theorem reindex_reading {D Dr : Type*} [Category D] [Category Dr] (Pg : Dr ⥤ D)
    {Ft Fs Kt Ks : Dr} {At As Bt Bs Ct Cs Et Es : D}
    (cT : Pg.obj Ft ≅ At) (cS : Pg.obj Fs ≅ As) (trT : At ⟶ Bt) (trS : As ⟶ Bs)
    (trS' : Bs ⟶ As) (htrS : trS ≫ trS' = 𝟙 As)
    (C3gt : Bt ≅ Ct) (C3gs : Bs ≅ Cs) (C3t : Ft ≅ Kt) (C3s : Fs ≅ Ks)
    (C3gT : Pg.obj Kt ≅ Et) (C3gS : Pg.obj Ks ≅ Es) (Qt : Et ≅ Ct) (Qs : Es ≅ Cs)
    (τR : Kt ⟶ Ks) (τV : Et ⟶ Es) (Z : Ct ⟶ Cs) (α : Ft ⟶ Fs)
    (hα : α = C3t.hom ≫ τR ≫ C3s.inv)
    (cTr : Pg.obj Ft ≅ Bt) (cSr : Pg.obj Fs ≅ Bs)
    (hcT : cTr.hom = cT.hom ≫ trT) (hcS : cSr.hom = cS.hom ≫ trS)
    (ha₀ : cTr.hom ≫ C3gt.hom = (Pg.mapIso C3t).hom ≫ C3gT.hom ≫ Qt.hom)
    (hb₀ : cSr.hom ≫ C3gs.hom = (Pg.mapIso C3s).hom ≫ C3gS.hom ≫ Qs.hom)
    (hd : Pg.map τR ≫ C3gS.hom = C3gT.hom ≫ τV)
    (hZ : Z = Qt.inv ≫ τV ≫ Qs.hom) :
    cT.inv ≫ Pg.map α ≫ cS.hom =
      trT ≫ C3gt.hom ≫ Z ≫ C3gs.inv ≫ trS' := by
  subst hα
  have ha : cT.hom ≫ trT ≫ C3gt.hom = Pg.map C3t.hom ≫ C3gT.hom ≫ Qt.hom := by
    rw [← Category.assoc, ← hcT, ha₀, Functor.mapIso_hom]
  have hb : cS.hom ≫ trS ≫ C3gs.hom = Pg.map C3s.hom ≫ C3gS.hom ≫ Qs.hom := by
    rw [← Category.assoc, ← hcS, hb₀, Functor.mapIso_hom]
  have ha' : Pg.map C3t.hom = cT.hom ≫ trT ≫ C3gt.hom ≫ Qt.inv ≫ C3gT.inv := by
    rw [reassoc_of% ha]
    simp
  have hb' : Pg.map C3s.inv = C3gS.hom ≫ Qs.hom ≫ C3gs.inv ≫ trS' ≫ cS.inv := by
    rw [← cancel_epi (Pg.map C3s.hom), ← Pg.map_comp, Iso.hom_inv_id, Pg.map_id,
      ← reassoc_of% hb]
    simp only [Iso.hom_inv_id_assoc]
    rw [reassoc_of% htrS, Iso.hom_inv_id]
  rw [Pg.map_comp, Pg.map_comp, ha', hb', hZ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hd]
  simp

/-- `reindex_reading` for a reindexing `AlgebraicGeometry.Space.transitionReindex`, the two
contractions of inverse images being those of the reindexing itself. -/
private theorem transitionReindex_eq_of_readings {W V Y : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Y.1 Y.2) {a b : V ⟶ Y} (f : W ⟶ V)
    {Kt Ks : Modules.{u, u} B S hS V.1 V.2} {Bt Bs Ct Cs Et Es : Modules.{u, u} B S hS W.1 W.2}
    (trT : (modulePullback B S hS (f ≫ a)).obj F ⟶ Bt)
    (trS : (modulePullback B S hS (f ≫ b)).obj F ⟶ Bs)
    (trS' : Bs ⟶ (modulePullback B S hS (f ≫ b)).obj F) (htrS : trS ≫ trS' = 𝟙 _)
    (C3gt : Bt ≅ Ct) (C3gs : Bs ≅ Cs) (C3t : (modulePullback B S hS a).obj F ≅ Kt)
    (C3s : (modulePullback B S hS b).obj F ≅ Ks)
    (C3gT : (modulePullback B S hS f).obj Kt ≅ Et) (C3gS : (modulePullback B S hS f).obj Ks ≅ Es)
    (Qt : Et ≅ Ct) (Qs : Es ≅ Cs)
    (τR : Kt ⟶ Ks) (τV : Et ⟶ Es) (Z : Ct ⟶ Cs)
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (hα : α = C3t.hom ≫ τR ≫ C3s.inv)
    (cTr : (modulePullback B S hS f).obj ((modulePullback B S hS a).obj F) ≅ Bt)
    (cSr : (modulePullback B S hS f).obj ((modulePullback B S hS b).obj F) ≅ Bs)
    (hcT : cTr.hom = ((modulePullbackCompIso B S hS f a).app F).hom ≫ trT)
    (hcS : cSr.hom = ((modulePullbackCompIso B S hS f b).app F).hom ≫ trS)
    (ha₀ : cTr.hom ≫ C3gt.hom = ((modulePullback B S hS f).mapIso C3t).hom ≫ C3gT.hom ≫ Qt.hom)
    (hb₀ : cSr.hom ≫ C3gs.hom = ((modulePullback B S hS f).mapIso C3s).hom ≫ C3gS.hom ≫ Qs.hom)
    (hd : (modulePullback B S hS f).map τR ≫ C3gS.hom = C3gT.hom ≫ τV)
    (hZ : Z = Qt.inv ≫ τV ≫ Qs.hom) :
    transitionReindex B S hS F α f = trT ≫ C3gt.hom ≫ Z ≫ C3gs.inv ≫ trS' := by
  unfold transitionReindex
  exact reindex_reading (modulePullback B S hS f) ((modulePullbackCompIso B S hS f a).app F)
    ((modulePullbackCompIso B S hS f b).app F) trT trS trS' htrS C3gt C3gs C3t C3s C3gT C3gS
    Qt Qs τR τV Z α hα cTr cSr hcT hcS ha₀ hb₀ hd hZ

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite in
/-- **The reindexing of `τ^a` along a represented morphism is `(h^*τ)^a`.**  For `h : V ⟶ R` of
the site, the reindexing `AlgebraicGeometry.Space.transitionReindex` of
`AlgebraicGeometry.Space.representedSchemeTransition` along the represented morphism of `h` is
the transition attached to the scheme reindexing `AlgebraicGeometry.Space.schemeTransitionReindex`,
between the transports to the represented composites. -/
theorem transitionReindex_representedSchemeTransition {V : BigFppfOver B S hS} (h : V ⟶ R) :
    transitionReindex B S hS (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
        (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        (representedSchemeTransition B S hS t s M τ) (representedSpaceMap B S hS h) =
      pullbackTransport _ (representedSpaceMap_comp B S hS h t) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ t) M).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
            (schemeTransitionReindex B S hS t s M τ h)).hom ≫
            (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ s) M).inv ≫
              pullbackTransport _ (representedSpaceMap_comp B S hS h s).symm := by
  have hZ : ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
        (schemeTransitionReindex B S hS t s M τ h)).hom =
      ((ObjectProperty.ι _).mapIso
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
          (quasicoherentPullbackCompIso B S hS h t M))).inv ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
          (quasicoherentPullbackMap B S hS h τ)).hom ≫
          ((ObjectProperty.ι _).mapIso
            ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
            (quasicoherentPullbackCompIso B S hS h s M))).hom := by
    simp only [schemeTransitionReindex, Functor.map_comp]
    rfl
  refine transitionReindex_eq_of_readings B S hS
    (W := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
    (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
    (representedSpaceMap B S hS h)
    _
    _
    _
    (pullbackTransport_comp_symm B S hS (T := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      (representedSpaceMap_comp B S hS h s))
    (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ t) M)
    (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ s) M)
    (modulePullbackRepresentedQuasicoherentIso B S hS t M)
    (modulePullbackRepresentedQuasicoherentIso B S hS s M)
    (modulePullbackRepresentedQuasicoherentIso B S hS h (quasicoherentPullbackObj B S hS t M))
    (modulePullbackRepresentedQuasicoherentIso B S hS h (quasicoherentPullbackObj B S hS s M))
    _ _ _ _ _ _ rfl _ _
    (representedModulePullbackCompIso_app_hom B S hS h t
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
    (representedModulePullbackCompIso_app_hom B S hS h s
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
    (congrArg Iso.hom (modulePullbackRepresentedQuasicoherentIso_comp B S hS h t M))
    (congrArg Iso.hom (modulePullbackRepresentedQuasicoherentIso_comp B S hS h s M))
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS h τ) hZ

/-- If `φt`, `φs` carry `τ` to `σ` and `ft`, `fs` correspond to `Φ.map φt`, `Φ.map φs`, then
`fs` and `ft` intertwine the conjugates of `Φ.map τ` and `Φ.map σ`. -/
private theorem transition_naturality_of_readings {D E : Type*} [Category D] [Category E]
    (Φ : E ⥤ D) {At As Bt Bs : D} {Kt Ks Lt Ls : E}
    (ft : At ⟶ Bt) (fs : As ⟶ Bs) (cMt : At ≅ Φ.obj Kt) (cMs : As ≅ Φ.obj Ks)
    (cNt : Bt ≅ Φ.obj Lt) (cNs : Bs ≅ Φ.obj Ls) (τ : Kt ⟶ Ks) (σ : Lt ⟶ Ls)
    (φt : Kt ⟶ Lt) (φs : Ks ⟶ Ls) (hφ : τ ≫ φs = φt ≫ σ)
    (nt : ft ≫ cNt.hom = cMt.hom ≫ Φ.map φt) (ns : fs ≫ cNs.hom = cMs.hom ≫ Φ.map φs) :
    (cMt.hom ≫ Φ.map τ ≫ cMs.inv) ≫ fs = ft ≫ cNt.hom ≫ Φ.map σ ≫ cNs.inv := by
  have ns' : cMs.inv ≫ fs = Φ.map φs ≫ cNs.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ns, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc, ns', ← Φ.map_comp_assoc, hφ, Φ.map_comp_assoc,
    reassoc_of% nt]

/-- **`τ^a` is natural in the scheme datum.**  For a morphism `φ : M ⟶ N` of quasi-coherent
modules on the scheme underlying `U` carrying a scheme transition `τ` of `M` to a scheme
transition `σ` of `N` (`τ ≫ s^*φ = t^*φ ≫ σ`), the morphism `φ^a` carries `τ^a` to `σ^a`. -/
theorem representedSchemeTransition_naturality
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (σ : quasicoherentPullbackObj B S hS t N ⟶ quasicoherentPullbackObj B S hS s N) (φ : M ⟶ N)
    (hφ : τ ≫ quasicoherentPullbackMap B S hS s φ = quasicoherentPullbackMap B S hS t φ ≫ σ) :
    TransitionCommutes B S hS (representedSchemeTransition B S hS t s M τ)
      (representedSchemeTransition B S hS t s N σ)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map φ).hom :=
  transition_naturality_of_readings
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor ⋙ ObjectProperty.ι _)
    _ _ (modulePullbackRepresentedQuasicoherentIso B S hS t M)
    (modulePullbackRepresentedQuasicoherentIso B S hS s M)
    (modulePullbackRepresentedQuasicoherentIso B S hS t N)
    (modulePullbackRepresentedQuasicoherentIso B S hS s N) τ σ _ _ hφ
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS t φ)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS s φ)

end Reindex

/-! ### The cocycle and unit laws, read on schemes -/

section Laws

/-- If three reindexings `ρp`, `ρq`, `ρr` are read through `c3` as `σx`, `σy`, `σz`, and `σz` is
the composite of `σx` and `σy`, then `ρr` is the composite of `ρp` and `ρq`. -/
private theorem cocycle_of_readings {D E 𝒮 C : Type*} [Category D] [Category E] [Category 𝒮]
    [Category C] (Φ : E ⥤ D) {Wsp Usp : 𝒮} {w u : C} (obj : (Wsp ⟶ Usp) → D)
    (objS : (w ⟶ u) → E) (rep : (w ⟶ u) → (Wsp ⟶ Usp)) (c3 : ∀ k, obj (rep k) ≅ Φ.obj (objS k))
    (tr : ∀ {a b : Wsp ⟶ Usp}, a = b → (obj a ⟶ obj b)) (htr : ∀ a, tr (rfl : a = a) = 𝟙 _)
    {xt xs yt ys zt zs : w ⟶ u} (σx : objS xt ⟶ objS xs) (σy : objS yt ⟶ objS ys)
    (σz : objS zt ⟶ objS zs) (h1 : zt = xt) (h2 : xs = yt) (h3 : ys = zs)
    (hσ : σz = eqToHom (congrArg objS h1) ≫ σx ≫ eqToHom (congrArg objS h2) ≫ σy ≫
      eqToHom (congrArg objS h3))
    {pa pb qa qb ra rb : Wsp ⟶ Usp}
    (ρp : obj pa ⟶ obj pb) (ρq : obj qa ⟶ obj qb) (ρr : obj ra ⟶ obj rb)
    (epa : pa = rep xt) (epb : rep xs = pb) (eqa : qa = rep yt) (eqb : rep ys = qb)
    (era : ra = rep zt) (erb : rep zs = rb)
    (hp : ρp = tr epa ≫ (c3 xt).hom ≫ Φ.map σx ≫ (c3 xs).inv ≫
      tr epb)
    (hq : ρq = tr eqa ≫ (c3 yt).hom ≫ Φ.map σy ≫ (c3 ys).inv ≫
      tr eqb)
    (hr : ρr = tr era ≫ (c3 zt).hom ≫ Φ.map σz ≫ (c3 zs).inv ≫
      tr erb)
    (ht : ra = pa) (hm : pb = qa) (hs : rb = qb) :
    ρr = comp₃ (tr ht) (comp₃ ρp (tr hm) ρq)
      (tr hs.symm) := by
  subst hp hq hr hσ epa epb eqa eqb era erb h1 h2 h3
  simp [comp₃, htr]

/-- If `ρd` is read through `c3` as the identification `σd` of two equal endpoints, then `ρd` is
the transport `tr h`. -/
private theorem unit_of_reading {D E 𝒮 C : Type*} [Category D] [Category E] [Category 𝒮]
    [Category C] (Φ : E ⥤ D) {Wsp Usp : 𝒮} {w u : C} (obj : (Wsp ⟶ Usp) → D)
    (objS : (w ⟶ u) → E) (rep : (w ⟶ u) → (Wsp ⟶ Usp)) (c3 : ∀ k, obj (rep k) ≅ Φ.obj (objS k))
    (tr : ∀ {a b : Wsp ⟶ Usp}, a = b → (obj a ⟶ obj b)) (htr : ∀ a, tr (rfl : a = a) = 𝟙 _)
    {dt ds : w ⟶ u} (σd : objS dt ⟶ objS ds) (hd : dt = ds)
    (hσ : σd = eqToHom (congrArg objS hd)) {da db : Wsp ⟶ Usp} (ρd : obj da ⟶ obj db)
    (eda : da = rep dt) (edb : rep ds = db)
    (hρ : ρd = tr eda ≫ (c3 dt).hom ≫ Φ.map σd ≫ (c3 ds).inv ≫
      tr edb)
    (h : da = db) : ρd = tr h := by
  subst hρ hσ eda edb hd
  simp [htr]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U R : BigFppfOver B S hS} (t s : R ⟶ U)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)

/-- **The cocycle law of `τ^a` at a represented triple, from the cocycle law of `τ` on schemes.**
For morphisms `x, y, z : W ⟶ R` of the site with `z ≫ t = x ≫ t`, `x ≫ s = y ≫ t` and
`y ≫ s = z ≫ s`, if `z^*τ` is the composite of `x^*τ` and `y^*τ` on the scheme underlying `W`,
then `τ^a` satisfies the cocycle law `AlgebraicGeometry.Space.TransitionCocycle` at the
represented triple. -/
theorem transitionCocycle_representedSchemeTransition {W : BigFppfOver B S hS} (x y z : W ⟶ R)
    (h1 : z ≫ t = x ≫ t) (h2 : x ≫ s = y ≫ t) (h3 : y ≫ s = z ≫ s)
    (hσ : schemeTransitionReindex B S hS t s M τ z =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) h1) ≫
        schemeTransitionReindex B S hS t s M τ x ≫
          eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) h2) ≫
            schemeTransitionReindex B S hS t s M τ y ≫
              eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) h3)) :
    TransitionCocycle B S hS
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
      (W := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      (representedSchemeTransition B S hS t s M τ) (representedSpaceMap B S hS x)
      (representedSpaceMap B S hS y) (representedSpaceMap B S hS z) := by
  intro ht hm hs
  exact cocycle_of_readings
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor ⋙ ObjectProperty.ι _)
    (fun k => (modulePullback B S hS k).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
    (fun k => quasicoherentPullbackObj B S hS k M) (representedSpaceMap B S hS)
    (fun k => modulePullbackRepresentedQuasicoherentIso B S hS k M)
    (fun h => pullbackTransport
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj h)
    (fun _ => rfl)
    (schemeTransitionReindex B S hS t s M τ x) (schemeTransitionReindex B S hS t s M τ y)
    (schemeTransitionReindex B S hS t s M τ z) h1 h2 h3 hσ
    _
    _
    _
    (representedSpaceMap_comp B S hS x t) (representedSpaceMap_comp B S hS x s).symm
    (representedSpaceMap_comp B S hS y t) (representedSpaceMap_comp B S hS y s).symm
    (representedSpaceMap_comp B S hS z t) (representedSpaceMap_comp B S hS z s).symm
    (transitionReindex_representedSchemeTransition B S hS t s M τ x)
    (transitionReindex_representedSchemeTransition B S hS t s M τ y)
    (transitionReindex_representedSchemeTransition B S hS t s M τ z) ht hm hs

/-- **The unit law of `τ^a` at a represented morphism, from the unit law of `τ` on schemes.**  For
`d : W ⟶ R` of the site with `d ≫ t = d ≫ s`, if `d^*τ` is the identification of its two equal
endpoints on the scheme underlying `W`, then `τ^a` satisfies the unit law
`AlgebraicGeometry.Space.TransitionUnit` at the represented morphism. -/
theorem transitionUnit_representedSchemeTransition {W : BigFppfOver B S hS} (d : W ⟶ R)
    (hd : d ≫ t = d ≫ s)
    (hσ : schemeTransitionReindex B S hS t s M τ d =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hd)) :
    TransitionUnit B S hS
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
      (W := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      (representedSchemeTransition B S hS t s M τ) (representedSpaceMap B S hS d) := by
  intro h
  exact unit_of_reading
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor ⋙ ObjectProperty.ι _)
    (fun k => (modulePullback B S hS k).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
    (fun k => quasicoherentPullbackObj B S hS k M) (representedSpaceMap B S hS)
    (fun k => modulePullbackRepresentedQuasicoherentIso B S hS k M)
    (fun h => pullbackTransport
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj h)
    (fun _ => rfl)
    (schemeTransitionReindex B S hS t s M τ d) hd hσ
    _
    (representedSpaceMap_comp B S hS d t) (representedSpaceMap_comp B S hS d s).symm
    (transitionReindex_representedSchemeTransition B S hS t s M τ d) h

end Laws

/-! ### The groupoid of a presentation: composable pairs and units, on schemes -/

section Presentation

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits in presheaves on `BigFppfOver B S hS` exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_PresentationSchemeDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_PresentationSchemeDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The space of composable pairs of the groupoid of a presentation maps to the represented
scheme of composable pairs `R ×_U R`.** -/
def composableToPresentationDouble :
    AlgebraicSpaces.fiberProduct B S hS (presentationGroupoid P).source
        (presentationGroupoid P).target ⟶
      ⟨yoneda.obj (presentationDouble P), isAlgebraicSpace_yoneda B S hS (presentationDouble P)⟩ :=
  ObjectProperty.homMk (((isPullback_presentationDouble P).map yoneda).lift
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition)

/-- The first represented projection of `R ×_U R` restricts to the first projection of the space
of composable pairs. -/
theorem composableToPresentationDouble_comp_fst :
    composableToPresentationDouble P ≫ representedSpaceMap B S hS (presentationDoubleFst P) =
      firstArrow (presentationGroupoid P) :=
  ObjectProperty.hom_ext _ (((isPullback_presentationDouble P).map yoneda).lift_fst _ _ _)

/-- The second represented projection of `R ×_U R` restricts to the second projection of the
space of composable pairs. -/
theorem composableToPresentationDouble_comp_snd :
    composableToPresentationDouble P ≫ representedSpaceMap B S hS (presentationDoubleSnd P) =
      secondArrow (presentationGroupoid P) :=
  ObjectProperty.hom_ext _ (((isPullback_presentationDouble P).map yoneda).lift_snd _ _ _)

/-- Two morphisms into the arrow space of the groupoid of a presentation agree as soon as their
targets and their sources agree. -/
theorem presentationGroupoid_hom_ext {Z : AlgebraicSpaces B S hS}
    {f g : Z ⟶ (presentationGroupoid P).arrows}
    (ht : f ≫ (presentationGroupoid P).target = g ≫ (presentationGroupoid P).target)
    (hs : f ≫ (presentationGroupoid P).source = g ≫ (presentationGroupoid P).source) : f = g :=
  ObjectProperty.hom_ext _ (P.isPullback.hom_ext (congrArg (fun k => k.hom) ht)
    (congrArg (fun k => k.hom) hs))

/-- **The represented composition leg of `R ×_U R` restricts to the composition of the groupoid
of a presentation.** -/
theorem composableToPresentationDouble_comp_comp :
    composableToPresentationDouble P ≫ representedSpaceMap B S hS (presentationComp P) =
      (presentationGroupoid P).comp := by
  refine presentationGroupoid_hom_ext P ?_ ?_
  · rw [comp_comp_target, ← composableToPresentationDouble_comp_fst, Category.assoc,
      Category.assoc]
    change _ ≫ representedSpaceMap B S hS (presentationComp P) ≫
        representedSpaceMap B S hS P.target =
      _ ≫ representedSpaceMap B S hS (presentationDoubleFst P) ≫
        representedSpaceMap B S hS P.target
    rw [representedSpaceMap_comp, representedSpaceMap_comp, presentationComp_comp_target]
  · rw [comp_comp_source, ← composableToPresentationDouble_comp_snd, Category.assoc,
      Category.assoc]
    change _ ≫ representedSpaceMap B S hS (presentationComp P) ≫
        representedSpaceMap B S hS P.source =
      _ ≫ representedSpaceMap B S hS (presentationDoubleSnd P) ≫
        representedSpaceMap B S hS P.source
    rw [representedSpaceMap_comp, representedSpaceMap_comp, presentationComp_comp_source]

/-- **The unit arrow of the groupoid of a presentation is the represented diagonal.** -/
theorem identityArrow_presentationGroupoid :
    identityArrow (presentationGroupoid P) = representedSpaceMap B S hS (presentationDiag P) := by
  refine presentationGroupoid_hom_ext P ?_ ?_
  · rw [identityArrow_comp_target]
    change 𝟙 _ = representedSpaceMap B S hS (presentationDiag P) ≫
      representedSpaceMap B S hS P.target
    rw [representedSpaceMap_comp, presentationDiag_comp_target]
    exact ObjectProperty.hom_ext _ (yoneda.map_id _).symm
  · rw [identityArrow_comp_source]
    change 𝟙 _ = representedSpaceMap B S hS (presentationDiag P) ≫
      representedSpaceMap B S hS P.source
    rw [representedSpaceMap_comp, presentationDiag_comp_source]
    exact ObjectProperty.hom_ext _ (yoneda.map_id _).symm

end Presentation

/-! ### The quasi-coherent module on the groupoid -/

section Module

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)

/-- **The cocycle condition of a scheme transition `τ : t^*M ⟶ s^*M` of a presentation**, on the
scheme of composable pairs `R ×_U R` (`AlgebraicGeometry.Space.presentationDouble`): the pullback
of `τ` along the composition leg is the pullback along the first projection followed by the
pullback along the second, the equal endpoints being identified. -/
def PresentationSchemeCocycle : Prop :=
  schemeTransitionReindex B S hS P.target P.source M τ (presentationComp P) =
    eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
        (presentationComp_comp_target P)) ≫
      schemeTransitionReindex B S hS P.target P.source M τ (presentationDoubleFst P) ≫
        eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
            (presentationDoubleFst_comp_source P)) ≫
          schemeTransitionReindex B S hS P.target P.source M τ (presentationDoubleSnd P) ≫
            eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
              (presentationComp_comp_source P).symm)

/-- **The unit condition of a scheme transition `τ : t^*M ⟶ s^*M` of a presentation**: the
pullback of `τ` along the diagonal `U ⟶ R` (`AlgebraicGeometry.Space.presentationDiag`) is the
identification of its two endpoints, both being `M`. -/
def PresentationSchemeUnit : Prop :=
  schemeTransitionReindex B S hS P.target P.source M τ (presentationDiag P) =
    eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
      ((presentationDiag_comp_target P).trans (presentationDiag_comp_source P).symm))

/-- The transition morphism `τ^a : t^*(M^a) ⟶ s^*(M^a)` on the arrow space of the groupoid of a
presentation. -/
abbrev presentationSchemeTransition :
    (modulePullback B S hS (presentationGroupoid P).target).obj
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj ⟶
      (modulePullback B S hS (presentationGroupoid P).source).obj
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj :=
  representedSchemeTransition B S hS P.target P.source M τ

/-- **The cocycle condition of Stacks 0441 for `τ^a`**, from the scheme cocycle condition. -/
theorem presentationSchemeTransition_cocycle (hc : PresentationSchemeCocycle P M τ) :
    groupoidPullbackTransition B S hS (presentationGroupoid P)
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        (presentationSchemeTransition P M τ) (presentationGroupoid P).comp =
      groupoidTransitionComposite B S hS (presentationGroupoid P)
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        (presentationSchemeTransition P M τ) :=
  groupoidPullbackTransition_comp_eq_groupoidTransitionComposite B S hS _ _ _ _ _ _
    (composableToPresentationDouble_comp_fst P) (composableToPresentationDouble_comp_snd P)
    (composableToPresentationDouble_comp_comp P)
    (TransitionCocycle.comp B S hS _ _
      ((representedSpaceMap_comp B S hS _ _).trans
        ((congrArg (representedSpaceMap B S hS) (presentationComp_comp_target P)).trans
          (representedSpaceMap_comp B S hS _ _).symm))
      ((representedSpaceMap_comp B S hS _ _).trans
        ((congrArg (representedSpaceMap B S hS) (presentationDoubleFst_comp_source P)).trans
          (representedSpaceMap_comp B S hS _ _).symm))
      ((representedSpaceMap_comp B S hS _ _).trans
        ((congrArg (representedSpaceMap B S hS) (presentationComp_comp_source P)).trans
          (representedSpaceMap_comp B S hS _ _).symm))
      (transitionCocycle_representedSchemeTransition B S hS P.target P.source M τ
        (presentationDoubleFst P) (presentationDoubleSnd P) (presentationComp P)
        (presentationComp_comp_target P) (presentationDoubleFst_comp_source P)
        (presentationComp_comp_source P).symm hc)
      (composableToPresentationDouble P) rfl rfl rfl)

/-- **The unit condition of Stacks 0441 for `τ^a`**, from the scheme unit condition. -/
theorem presentationSchemeTransition_unit (hu : PresentationSchemeUnit P M τ) :
    groupoidPullbackTransition B S hS (presentationGroupoid P)
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        (presentationSchemeTransition P M τ) (identityArrow (presentationGroupoid P)) =
      pullbackTransport ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        ((identityArrow_comp_target (presentationGroupoid P)).trans
          (identityArrow_comp_source (presentationGroupoid P)).symm) :=
  groupoidPullbackTransition_identityArrow_eq_pullbackTransport B S hS _ _ _ _
    (identityArrow_presentationGroupoid P)
    (transitionUnit_representedSchemeTransition B S hS P.target P.source M τ
      (presentationDiag P)
      ((presentationDiag_comp_target P).trans (presentationDiag_comp_source P).symm) hu)

/-- **The quasi-coherent module `(M^a, τ^a)` on the groupoid of a presentation** (Stacks 0441),
attached to a quasi-coherent module `M` on the presenting scheme and a scheme transition
`τ : t^*M ⟶ s^*M` satisfying the cocycle and unit conditions on schemes. -/
def presentationSchemeModule (hc : PresentationSchemeCocycle P M τ)
    (hu : PresentationSchemeUnit P M τ) : QuasicoherentModule B S hS (presentationGroupoid P) where
  F := (representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M
  alpha := presentationSchemeTransition P M τ
  cocycle := presentationSchemeTransition_cocycle P M τ hc
  unit := presentationSchemeTransition_unit P M τ hu

end Module

/-! ### Descent to the algebraic space -/

section Descent

attribute [local irreducible] CategoryTheory.yoneda AlgebraicGeometry.Space.modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (hc : PresentationSchemeCocycle P M τ) (hu : PresentationSchemeUnit P M τ)

/-- **The equivalence of Stacks 03M3 for the groupoid of a presentation**:
`QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` for a presentation `X = U/R`, with the atlas as `φ`. -/
abbrev presentationQuasicoherentEquivalence :
    QuasicoherentSheaves.{u, u} B S hS X.obj X.property ≌
      QuasicoherentModule B S hS (presentationGroupoid P) :=
  equivalenceQuasicoherentFromSpaceBase B S hS _ _ (presentationAtlas_isEtale P)
    (presentationAtlas_comm P) (presentationAtlas_isEtaleCovering P)
    (presentationAtlas_relativelyRepresentable P) (presentationGroupoid_isPullback P)

/-- **The descended quasi-coherent `𝒪_X`-module** of a quasi-coherent module `M` on the presenting
scheme of a presentation `X = U/R` with a scheme transition `τ : t^*M ⟶ s^*M` satisfying the
cocycle and unit conditions on schemes: the quasi-coherent `𝒪_X`-module corresponding to
`(M^a, τ^a)` under the equivalence of Stacks 03M3. -/
def presentationDescendedModule : QuasicoherentSheaves.{u, u} B S hS X.obj X.property :=
  (presentationQuasicoherentEquivalence P).inverse.obj (presentationSchemeModule P M τ hc hu)

/-- The descended module is quasi-coherent on the small étale site of `X`. -/
theorem isQuasicoherentOnSite_presentationDescendedModule :
    (presentationDescendedModule P M τ hc hu).obj.IsQuasicoherentOnSite :=
  (presentationDescendedModule P M τ hc hu).property

/-- **The groupoid module of the descended module is `(M^a, τ^a)`**: the counit of the
equivalence of Stacks 03M3 at `(M^a, τ^a)`. -/
def presentationDescendedModuleCounitIso :
    (presentationQuasicoherentEquivalence P).functor.obj (presentationDescendedModule P M τ hc hu) ≅
      presentationSchemeModule P M τ hc hu :=
  (presentationQuasicoherentEquivalence P).counitIso.app (presentationSchemeModule P M τ hc hu)

/-- **The inverse image along the atlas of the descended module is `M^a`**: the counit of the
equivalence of Stacks 03M3 at `(M^a, τ^a)`, read on the space of objects. -/
def presentationDescendedModuleChartIso :
    (modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P M τ hc hu).obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj :=
  (QuasicoherentModule.forget _).mapIso (presentationDescendedModuleCounitIso P M τ hc hu)

/-- The chart identification is the underlying morphism of the counit. -/
theorem presentationDescendedModuleChartIso_hom :
    (presentationDescendedModuleChartIso P M τ hc hu).hom =
      (presentationDescendedModuleCounitIso P M τ hc hu).hom.hom :=
  rfl

/-- **The chart identification carries the transition morphism of the inverse image to `τ^a`**:
the transition morphism of the groupoid module of the descended module (the canonical one,
`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_functor_obj_alpha`) is carried by the
chart identification to `τ^a`. -/
theorem presentationDescendedModuleChartIso_comm :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      ((presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P M τ hc hu)).alpha
      (presentationSchemeTransition P M τ) (presentationDescendedModuleChartIso P M τ hc hu).hom :=
  (QuasicoherentModule.compatible_iff_transitionCommutes B S hS _).1
    (QuasicoherentModule.compatible_hom (presentationDescendedModuleCounitIso P M τ hc hu).hom)

omit hc hu in
/-- The transition morphism of the groupoid module of a quasi-coherent `𝒪_X`-module under the
equivalence of Stacks 03M3 is the canonical transition morphism of its inverse image along the
atlas. -/
theorem presentationQuasicoherentEquivalence_functor_obj_alpha
    (Y : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    ((presentationQuasicoherentEquivalence P).functor.obj Y).alpha =
      spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Y.obj :=
  spaceBaseObj_alpha B S hS _ _ _ Y

variable {N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (σ : quasicoherentPullbackObj B S hS P.target N ⟶ quasicoherentPullbackObj B S hS P.source N)
  (hc' : PresentationSchemeCocycle P N σ) (hu' : PresentationSchemeUnit P N σ)
  (φ : M ⟶ N)
  (hφ : τ ≫ quasicoherentPullbackMap B S hS P.source φ =
    quasicoherentPullbackMap B S hS P.target φ ≫ σ)

/-- The morphism `φ^a : (M^a, τ^a) ⟶ (N^a, σ^a)` of quasi-coherent modules on the groupoid of a
presentation attached to a morphism `φ : M ⟶ N` compatible with the scheme transitions. -/
def presentationSchemeModuleHom :
    presentationSchemeModule P M τ hc hu ⟶ presentationSchemeModule P N σ hc' hu' :=
  QuasicoherentModule.homMk
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.map φ).hom
    ((QuasicoherentModule.compatible_iff_transitionCommutes B S hS _).2
      (representedSchemeTransition_naturality B S hS P.target P.source M τ σ φ hφ))

/-- **The descent of a morphism of scheme data**: the morphism of descended `𝒪_X`-modules
corresponding to `φ^a` under the equivalence of Stacks 03M3. -/
def presentationDescendedHom :
    presentationDescendedModule P M τ hc hu ⟶ presentationDescendedModule P N σ hc' hu' :=
  (presentationQuasicoherentEquivalence P).inverse.map
    (presentationSchemeModuleHom P M τ hc hu σ hc' hu' φ hφ)

/-- **The inverse image along the atlas of the descended morphism is `φ^a`**, through the chart
identifications. -/
theorem presentationDescendedHom_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedHom P M τ hc hu σ hc' hu' φ hφ).hom ≫
      (presentationDescendedModuleChartIso P N σ hc' hu').hom =
    (presentationDescendedModuleChartIso P M τ hc hu).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.map φ).hom :=
  congrArg QuasicoherentModule.Hom.hom ((presentationQuasicoherentEquivalence P).counit.naturality
    (presentationSchemeModuleHom P M τ hc hu σ hc' hu' φ hφ))

/-- **The descended morphism is unique**: a morphism of the descended `𝒪_X`-modules whose inverse
image along the atlas is `φ^a`, through the chart identifications, is the descended morphism. -/
theorem presentationDescendedHom_unique
    (ψ : presentationDescendedModule P M τ hc hu ⟶ presentationDescendedModule P N σ hc' hu')
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ.hom ≫
        (presentationDescendedModuleChartIso P N σ hc' hu').hom =
      (presentationDescendedModuleChartIso P M τ hc hu).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.map φ).hom) :
    ψ = presentationDescendedHom P M τ hc hu σ hc' hu' φ hφ := by
  refine (presentationQuasicoherentEquivalence P).functor.map_injective
    ((cancel_mono ((presentationQuasicoherentEquivalence P).counitIso.app
      (presentationSchemeModule P N σ hc' hu')).hom).1 ?_)
  refine QuasicoherentModule.Hom.ext ?_
  exact hψ.trans (presentationDescendedHom_spec P M τ hc hu σ hc' hu' φ hφ).symm

include hφ in
/-- **Morphism descent along a presentation**: a morphism `φ : M ⟶ N` of quasi-coherent modules on
the presenting scheme compatible with the scheme transitions descends to a unique morphism of the
descended `𝒪_X`-modules whose inverse image along the atlas is `φ^a`. -/
theorem existsUnique_presentationDescendedHom :
    ∃! ψ : presentationDescendedModule P M τ hc hu ⟶ presentationDescendedModule P N σ hc' hu',
      (modulePullback B S hS (presentationAtlas P)).map ψ.hom ≫
          (presentationDescendedModuleChartIso P N σ hc' hu').hom =
        (presentationDescendedModuleChartIso P M τ hc hu).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.map φ).hom :=
  ⟨presentationDescendedHom P M τ hc hu σ hc' hu' φ hφ,
    presentationDescendedHom_spec P M τ hc hu σ hc' hu' φ hφ,
    fun ψ hψ => presentationDescendedHom_unique P M τ hc hu σ hc' hu' φ hφ ψ hψ⟩

end Descent

end AlgebraicGeometry.Space

end
