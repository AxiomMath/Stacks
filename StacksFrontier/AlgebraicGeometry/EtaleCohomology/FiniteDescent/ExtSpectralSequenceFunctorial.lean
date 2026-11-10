module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectFunctor
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Homology.Ext.SpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hyper-Ext spectral sequence of a complex, functorially

Let `M` be an object of an abelian category `C` with a derived category. For a bounded below
cochain complex `K`, [Stacks, Tag 0AVI] gives a cohomological spectral sequence with
`E₁^{p,q} = Ext^q(M, Kᵖ)` abutting to `Ext^{p+q}(M, K)`. The statement
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` produces that spectral
sequence, but only as an existential: it asserts that *some* spectral sequence with those pages
exists. [Stacks, Tag 09Z2] uses the spectral sequence of a resolution and needs it to be
functorial in the complex, which an existential statement cannot supply.

This file rebuilds the same construction as a functor of the complex. Nothing new is proved
about the spectral sequence itself; what is supplied is the functoriality of each step of the
chain

`K  ↦  σ^{≥ ∙}K  ↦  Hom(M, cone(σ^{≥ ∙+1}K ⟶ σ^{≥ ∙}K))  ↦  E(K)`

and the naturality in `K` of the identification of the first page.

## Main definitions

* `StacksDraft.ExtSpectralSequenceFunctorial.precompFunctor`: for a spectral object `X` in a
  pretriangulated category indexed by `ι`, precomposition
  `CategoryTheory.Triangulated.SpectralObject.precomp` as a functor `(ι' ⥤ ι) ⥤ ...` of the
  index functor. Mathlib has the functoriality of `mapTriangulatedFunctor` and of
  `mapHomologicalFunctor` in the spectral object, but not this one.
* `StacksDraft.ExtSpectralSequenceFunctorial.stupidTruncTowerFunctor`: the tower of stupid
  truncations `StacksDraft.StupidTruncation.stupidTruncTower` as a functor of the complex.
* `StacksDraft.ExtSpectralSequenceFunctorial.towerExtSpectralObjectFunctor`: derived `Hom(M, -)`
  applied to a tower, as a functor of the tower.
* `StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFunctor`: the spectral
  sequence of Tag 0AVI as a functor `CochainComplex C ℤ ⥤ CohomologicalSpectralSequence _ 1`.
* `StacksDraft.ExtSpectralSequenceFunctorial.zExtXFunctor`: the functor `K ↦ Ext^q(M, Kᵖ)`.

## Main results

* `StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFirstPageNatIso`: the
  identification `E₁^{p,q}(K) ≅ Ext^q(M, Kᵖ)` as a natural isomorphism of functors of `K`.
* `StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFirstPageIso`: its
  component at a single complex, which is the isomorphism Tag 0AVI asserts.
* `StacksDraft.ExtSpectralSequenceFunctorial.stupidTruncGEConeIso_hom_naturality`: the only
  naturality square in the first-page identification that is not a formal consequence of an
  isomorphism which is already natural. It says that the quasi-isomorphism
  `cone(σ^{≥p+1}K ⟶ σ^{≥p}K) ⟶ Kᵖ[-p]` is natural in `K`, and it comes from
  `CochainComplex.mappingCone.map_descShortComplex`.
* `StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFunctor_obj`: the
  spectral sequence of this functor at a complex *is* the one
  `StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` produces, so its
  convergence is available verbatim.
* `StacksDraft.ExtSpectralSequenceFunctorial.exists_extComplexFiltration_le`: **the filtration
  of the abutment is natural in the complex** — a morphism `φ : K ⟶ L` carries
  `Fil^p Ext^n(M, K)` into `Fil^p Ext^n(M, L)`.

## Implementation notes

The spectral object route is the one that can be made functorial, because it involves no
choices. The two other routes in the library do not work: the functoriality of
`Stacks.Injectives.extSpectralSequenceInto` is with respect to a morphism of the *chosen*
K-injective resolutions, which a morphism of filtered complexes does not induce, and
`StacksFrontier/Homology/Injectives/Ext/SpectralSequenceIntoIndependence.lean` only produces
`Nonempty` of an isomorphism.

The indexing data `StacksDraft.ExtSpectralSequence.spectralSequenceDataCoreE₁` and its two
instances are the ones of `StacksFrontier/Homology/Ext/SpectralSequence.lean`, which is why the
spectral sequence built here is *the* spectral sequence that file produces
(`extComplexSpectralSequenceFunctor_obj`) and inherits its convergence. The first-page isomorphism
is not reused: the private `extComplexSpectralSequenceFirstPageIso` is recovered as the component
at `K` of the natural isomorphism, which is strictly more information.

The naturality of the first page is assembled so that every square is either free — a whiskering
of an isomorphism that is already natural, namely
`CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXNatIso`,
`CategoryTheory.DerivedCategory.quotientCompQhIso`, `CategoryTheory.shiftFunctorAdd` and
`CategoryTheory.SingleFunctors.shiftIso` — or is `stupidTruncGEConeIso_hom_naturality`.

No `@[stacks]` attribute is placed here: the content of Tag 0AVI is already registered on
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence`, and this file only adds
functoriality.

## References

* [Stacks Project, Tag 0AVI](https://stacks.math.columbia.edu/tag/0AVI)
* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

attribute [local instance] mono_ιStupidTrunc

namespace StacksDraft.ExtSpectralSequenceFunctorial

universe u v w

section Precomp

open CategoryTheory.Triangulated CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {ι : Type*} [Category* ι] {ι' : Type*} [Category* ι']

variable (X : SpectralObject D ι)

/-- A natural transformation `α : F ⟶ G` of functors `ι' ⥤ ι` induces, by postcomposition, a
natural transformation `F.mapComposableArrows 1 ⟶ G.mapComposableArrows 1`. Read through the
identifications `(F.mapComposableArrows 1).obj (mk₁ f) ≅ mk₁ (F.map f)`, its component at
`mk₁ f` is the morphism `mk₁ (F.map f) ⟶ mk₁ (G.map f)` with components `α` at the two ends. -/
lemma whiskeringRight_app_mk₁_conj {F G : ι' ⥤ ι} (α : F ⟶ G) {i j : ι'} (f : i ⟶ j) :
    (F.mapComposableArrowsObjMk₁Iso f).inv ≫
        ((Functor.whiskeringRight (Fin 2) ι' ι).map α).app (mk₁ f) =
      homMk₁ (α.app i) (α.app j) (α.naturality f) ≫
        (G.mapComposableArrowsObjMk₁Iso f).inv := by
  cat_disch

/-- The form of `whiskeringRight_app_mk₁_conj` used to rewrite inside `X.ω₁`: it is the previous
lemma with the two identifications moved to the other sides. -/
lemma ω₁_map_whiskeringRight_app_mk₁ {F G : ι' ⥤ ι} (α : F ⟶ G) {i j : ι'} (f : i ⟶ j) :
    X.ω₁.map (((Functor.whiskeringRight (Fin 2) ι' ι).map α).app (mk₁ f)) ≫
        X.ω₁.map (G.mapComposableArrowsObjMk₁Iso f).hom =
      X.ω₁.map (F.mapComposableArrowsObjMk₁Iso f).hom ≫
        X.ω₁.map (homMk₁ (α.app i) (α.app j) (α.naturality f) :
          (mk₁ (F.map f) : ComposableArrows ι 1) ⟶ mk₁ (G.map f)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  cat_disch

/-- **A spectral object precomposed with a natural transformation of index functors.** For
`α : F ⟶ G` with `F G : ι' ⥤ ι`, this is the morphism of spectral objects
`X.precomp F ⟶ X.precomp G` whose underlying transformation of `ω₁` is `α` postcomposed into
composable arrows and then whiskered with `X.ω₁`. Its compatibility with the connecting maps is
the naturality of `X.δ'` along the composable arrow `mk₂ f g` mapped by `α`. -/
noncomputable def precompMap {F G : ι' ⥤ ι} (α : F ⟶ G) :
    X.precomp F ⟶ X.precomp G where
  hom := Functor.whiskerRight ((Functor.whiskeringRight (Fin 2) ι' ι).map α) X.ω₁
  comm {i j k} f g := by
    have h := X.δ'.naturality (((Functor.whiskeringRight (Fin 3) ι' ι).map α).app (mk₂ f g))
    dsimp [SpectralObject.δ, SpectralObject.precomp, Functor.mapComposableArrows,
      Precomp.map, Precomp.obj] at h ⊢
    simp only [Category.assoc, ← Functor.map_comp]
    rw [whiskeringRight_app_mk₁_conj α]
    simp only [Functor.map_comp]
    rw [reassoc_of% ω₁_map_whiskeringRight_app_mk₁ X α, reassoc_of% h]

/-- **Precomposition of a fixed spectral object, as a functor of the index functor.** This is
the functoriality that `CategoryTheory.Triangulated.SpectralObject.precomp` leaves open; the
functor laws hold because the underlying transformation of `ω₁` is built by whiskering. -/
noncomputable def precompFunctor : (ι' ⥤ ι) ⥤ SpectralObject D ι' where
  obj F := X.precomp F
  map α := precompMap X α
  map_id F := by
    apply SpectralObject.hom_ext
    apply NatTrans.ext
    funext T
    exact X.ω₁.map_id _
  map_comp α β := by
    apply SpectralObject.hom_ext
    apply NatTrans.ext
    funext T
    exact X.ω₁.map_comp (((Functor.whiskeringRight (Fin 2) ι' ι).map α).app T)
      (((Functor.whiskeringRight (Fin 2) ι' ι).map β).app T)

end Precomp

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The comparisons of the tower of stupid truncations are natural in the complex.** Both
sides become the inclusion `σ^{≥b}K ⟶ K` followed by `φ` after composing with the monomorphism
`σ^{≥a}L ⟶ L`. -/
lemma stupidTruncGEMapLE_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L) {a b : ℤ}
    (hab : a ≤ b) :
    stupidTruncGEMapLE K hab ≫ stupidTruncMap φ (embeddingUpIntGE a) =
      stupidTruncMap φ (embeddingUpIntGE b) ≫ stupidTruncGEMapLE L hab := by
  apply (cancel_mono (ιStupidTrunc L (embeddingUpIntGE a))).1
  rw [Category.assoc, Category.assoc, stupidTruncMap_ιStupidTrunc, stupidTruncGEMapLE_ι,
    ← Category.assoc, stupidTruncGEMapLE_ι, stupidTruncMap_ιStupidTrunc]

/-- **The tower of stupid truncations as a functor of the complex.** On objects it is
`StacksDraft.StupidTruncation.stupidTruncTower`; a morphism `φ : K ⟶ L` goes to the family of
truncated maps `σ^{≥ -i}φ`. -/
noncomputable def stupidTruncTowerFunctor :
    CochainComplex C ℤ ⥤ (ℤ ⥤ CochainComplex C ℤ) where
  obj K := stupidTruncTower K
  map φ :=
    { app i := stupidTruncMap φ (embeddingUpIntGE (-i))
      naturality _ _ f := stupidTruncGEMapLE_naturality φ (neg_le_neg (leOfHom f)) }
  map_id K := NatTrans.ext (funext fun i ↦ stupidTruncMap_id K (embeddingUpIntGE (-i)))
  map_comp φ ψ := NatTrans.ext (funext fun i ↦ stupidTruncMap_comp φ ψ (embeddingUpIntGE (-i)))

open StacksDraft.ExtSpectralSequence

attribute [local instance] hasSpectralSequence_spectralSequenceDataCoreE₁
  hasFirstPageComputation_spectralSequenceDataCoreE₁

variable [HasDerivedCategory.{w} C]

/-- **Derived `Hom` out of `M` applied to a tower, as a functor of the tower.** The tower is
turned into a spectral object indexed by `ℤ` by precomposing the mapping-cone spectral object of
the homotopy category, the triangulated functor to the derived category is applied, and then the
homological functor `Hom(M, -)`. The first two steps are functorial by `precompFunctor` and
`CategoryTheory.Functor.mapTriangulatedSpectralObject`, the third by
`CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctorFunctor`. -/
noncomputable def towerExtSpectralObjectFunctor (M : DerivedCategory C) :
    (ℤ ⥤ CochainComplex C ℤ) ⥤ Abelian.SpectralObject AddCommGrpCat.{w} ℤ :=
  precompFunctor (HomotopyCategory.spectralObjectMappingCone C) ⋙
    DerivedCategory.Qh.mapTriangulatedSpectralObject ℤ ⋙
      Triangulated.SpectralObject.mapHomologicalFunctorFunctor
        (preadditiveCoyoneda.obj (Opposite.op M)) ℤ

/-- **The hyper-Ext spectral sequence of a complex, as a functor of the complex.** Its value at
`K` is the spectral sequence of [Stacks, Tag 0AVI]: the first page is `Extʲ(M, Kⁱ)` and the
abutment is `Ext(M[0], K)`. The functoriality of taking the spectral sequence of a spectral
object is `CategoryTheory.Abelian.SpectralObject.spectralSequenceFunctor`. -/
noncomputable def extComplexSpectralSequenceFunctor (M : C) :
    CochainComplex C ℤ ⥤ CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  stupidTruncTowerFunctor ⋙
    towerExtSpectralObjectFunctor ((DerivedCategory.singleFunctor C 0).obj M) ⋙
      Abelian.SpectralObject.spectralSequenceFunctor spectralSequenceDataCoreE₁

/-- **The short exact sequence `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ 0` is natural in `K`.** The
morphism induced by `φ : K ⟶ L` is the pair of truncated maps together with `φᵖ` in degree
`p`. -/
@[simps]
noncomputable def stupidTruncGEShortComplexMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    stupidTruncGEShortComplex K p ⟶ stupidTruncGEShortComplex L p where
  τ₁ := stupidTruncMap φ (embeddingUpIntGE (p + 1))
  τ₂ := stupidTruncMap φ (embeddingUpIntGE p)
  τ₃ := (HomologicalComplex.single C (ComplexShape.up ℤ) p).map (φ.f p)
  comm₁₂ := (stupidTruncGEMapLE_naturality φ (show p ≤ p + 1 by omega)).symm
  comm₂₃ := by
    dsimp only [stupidTruncGEShortComplex]
    apply to_single_hom_ext
    simp [stupidTruncGEπ_f, stupidTruncGEXIso, HomologicalComplex.single_map_f_self]

/-- The quasi-isomorphism `cone(σ^{≥p+1}K ⟶ σ^{≥p}K) ⟶ Kᵖ[-p]` of
`CochainComplex.mappingCone.descShortComplex`, read as an isomorphism in the derived category.
The objects are left in the form in which the short complex presents them; see
`stupidTruncGEConeIso` for the form the spectral object produces. -/
noncomputable def stupidTruncGEConeIsoAux (K : CochainComplex C ℤ) (p : ℤ) :
    DerivedCategory.Q.obj (CochainComplex.mappingCone (stupidTruncGEShortComplex K p).f) ≅
      DerivedCategory.Q.obj (stupidTruncGEShortComplex K p).X₃ :=
  haveI hq : QuasiIso (CochainComplex.mappingCone.descShortComplex
      (stupidTruncGEShortComplex K p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (stupidTruncGEShortComplex_shortExact K p)
  haveI : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
      (stupidTruncGEShortComplex K p))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C _).2 hq
  asIso (DerivedCategory.Q.map
    (CochainComplex.mappingCone.descShortComplex (stupidTruncGEShortComplex K p)))

/-- The isomorphism `stupidTruncGEConeIsoAux` is the image of `descShortComplex`. -/
lemma stupidTruncGEConeIsoAux_hom (K : CochainComplex C ℤ) (p : ℤ) :
    (stupidTruncGEConeIsoAux K p).hom = DerivedCategory.Q.map
      (CochainComplex.mappingCone.descShortComplex (stupidTruncGEShortComplex K p)) := rfl

/-- `stupidTruncGEConeIsoAux` is natural in `K`: this is
`CochainComplex.mappingCone.map_descShortComplex` for the morphism of short complexes
`stupidTruncGEShortComplexMap`, pushed to the derived category. -/
lemma stupidTruncGEConeIsoAux_hom_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    DerivedCategory.Q.map (CochainComplex.mappingCone.map
        (stupidTruncGEShortComplex K p).f (stupidTruncGEShortComplex L p).f
        (stupidTruncGEShortComplexMap φ p).τ₁ (stupidTruncGEShortComplexMap φ p).τ₂
        (stupidTruncGEShortComplexMap φ p).comm₁₂.symm) ≫
      (stupidTruncGEConeIsoAux L p).hom =
    (stupidTruncGEConeIsoAux K p).hom ≫
      DerivedCategory.Q.map (stupidTruncGEShortComplexMap φ p).τ₃ := by
  rw [stupidTruncGEConeIsoAux_hom, stupidTruncGEConeIsoAux_hom, ← Functor.map_comp,
    ← Functor.map_comp, CochainComplex.mappingCone.map_descShortComplex]

/-- **The successive cone of the tower of stupid truncations is `Kᵖ` in degree `p`.** The
truncation indices are taken as data satisfying `a = p` and `b = p + 1` rather than as `p` and
`p + 1` on the nose: the tower produces them as `-(-p)` and `-(-p-1)`, which are equal to `p`
and `p + 1` only propositionally. -/
noncomputable def stupidTruncGEConeIso (K : CochainComplex C ℤ) (p : ℤ) {a b : ℤ}
    (hab : a ≤ b) (ha : a = p) (hb : b = p + 1) :
    DerivedCategory.Q.obj (CochainComplex.mappingCone (stupidTruncGEMapLE K hab)) ≅
      (DerivedCategory.singleFunctor C p).obj (K.X p) := by
  subst ha hb
  exact stupidTruncGEConeIsoAux K _

/-- **The identification of the successive cone of the tower with `Kᵖ[-p]` is natural in `K`.**
This is the one naturality square in the first-page identification that is not formal; it is
`stupidTruncGEConeIsoAux_hom_naturality` at the tower's indexing. -/
lemma stupidTruncGEConeIso_hom_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ)
    {a b : ℤ} (hab : a ≤ b) (ha : a = p) (hb : b = p + 1)
    (comm : stupidTruncGEMapLE K hab ≫ stupidTruncMap φ (embeddingUpIntGE a) =
      stupidTruncMap φ (embeddingUpIntGE b) ≫ stupidTruncGEMapLE L hab) :
    DerivedCategory.Q.map (CochainComplex.mappingCone.map
        (stupidTruncGEMapLE K hab) (stupidTruncGEMapLE L hab)
        (stupidTruncMap φ (embeddingUpIntGE b)) (stupidTruncMap φ (embeddingUpIntGE a)) comm) ≫
      (stupidTruncGEConeIso L p hab ha hb).hom =
    (stupidTruncGEConeIso K p hab ha hb).hom ≫
      (DerivedCategory.singleFunctor C p).map (φ.f p) := by
  subst ha hb
  exact stupidTruncGEConeIsoAux_hom_naturality φ _

/-- **The cone `cone(σ^{≥p+1}K ⟶ σ^{≥p}K)` as a functor of `K`.** It is written as the
composite that the mapping-cone spectral object of the tower produces at the arrow
`-p-1 ⟶ -p`, so that it agrees with that spectral object on the nose; the functor laws are
those of the three functors it is composed from. -/
noncomputable def mappingConeTowerFunctor (p : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  stupidTruncTowerFunctor ⋙
    (Functor.whiskeringLeft (Fin 2) ℤ (CochainComplex C ℤ)).obj
      (ComposableArrows.mk₁ (homOfLE (show -p - 1 ≤ -p by omega))) ⋙
    HomotopyCategory.composableArrowsFunctor C

/-- **The successive cones of the tower are `Kᵖ[-p]`, naturally in `K`.** The components are
`stupidTruncGEConeIso` and the naturality is `stupidTruncGEConeIso_hom_naturality`. -/
noncomputable def mappingConeTowerQNatIso (p : ℤ) :
    mappingConeTowerFunctor.{u, v} p ⋙ DerivedCategory.Q.{w} ≅
      HomologicalComplex.eval C (ComplexShape.up ℤ) p ⋙ DerivedCategory.singleFunctor C p :=
  NatIso.ofComponents
    (fun K ↦ stupidTruncGEConeIso K p (a := -(-p)) (b := -(-p - 1))
      (by omega) (by omega) (by omega))
    (fun φ ↦ stupidTruncGEConeIso_hom_naturality φ p (a := -(-p)) (b := -(-p - 1))
      (by omega) (by omega) (by omega) (stupidTruncGEMapLE_naturality φ _))

/-- **`Ext^{p+q}(M, N[-p]) ≅ Ext^q(M, N[0])`, naturally in `N`.** The shift `p + q` is split as
`p` then `q` by `CategoryTheory.shiftFunctorAdd`, and the shift by `p` of the single functor in
degree `p` is the single functor in degree `0` by
`CategoryTheory.SingleFunctors.shiftIso`; both are natural, so no naturality square has to be
checked. -/
noncomputable def extSingleNatIso (M : DerivedCategory C) (p q : ℤ) :
    DerivedCategory.singleFunctor C p ⋙
        (preadditiveCoyoneda.obj (Opposite.op M)).shift (p + q) ≅
      DerivedCategory.singleFunctor C 0 ⋙
        (preadditiveCoyoneda.obj (Opposite.op M)).shift q :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor C p)
      ((preadditiveCoyoneda.obj (Opposite.op M)).isoShift (p + q)).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor C p)
      (Functor.isoWhiskerRight (shiftFunctorAdd (DerivedCategory C) p q)
        (preadditiveCoyoneda.obj (Opposite.op M))) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight ((DerivedCategory.singleFunctors C).shiftIso p 0 p (add_zero p))
        (shiftFunctor (DerivedCategory C) q))
      (preadditiveCoyoneda.obj (Opposite.op M)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor C 0)
      ((preadditiveCoyoneda.obj (Opposite.op M)).isoShift q)

/-- **The functor `K ↦ Extʲ(M, Kⁱ)`**, the intended first page in bidegree `(i, j)`. See
`zExtXFunctor_obj`. -/
noncomputable def zExtXFunctor (M : C) (p q : ℤ) :
    CochainComplex C ℤ ⥤ AddCommGrpCat.{w} :=
  HomologicalComplex.eval C (ComplexShape.up ℤ) p ⋙ DerivedCategory.singleFunctor C 0 ⋙
    (preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))).shift q

/-- The value of `zExtXFunctor` is the Ext group it is named for. -/
lemma zExtXFunctor_obj (M : C) (p q : ℤ) (K : CochainComplex C ℤ) :
    (zExtXFunctor.{u, v, w} M p q).obj K = AddCommGrpCat.of (Abelian.zExt M (K.X p) q) := rfl

/-- **The first page in bidegree `(p, q)`, naturally in `K`, as derived `Hom` out of `M` of the
successive cone of the tower.** This is
`CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXNatIso` whiskered with the
functor producing the spectral object. -/
noncomputable def firstPageNatIsoCone (M : C) (p q : ℤ) :
    extComplexSpectralSequenceFunctor.{u, v, w} M ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{w} _ 1 1 (le_refl 1) ⋙
          HomologicalComplex.eval AddCommGrpCat.{w} _ (p, q) ≅
      (stupidTruncTowerFunctor ⋙
          towerExtSpectralObjectFunctor ((DerivedCategory.singleFunctor C 0).obj M)) ⋙
        Abelian.SpectralObject.HObjFunctor (p + q)
          (ComposableArrows.mk₁ (homOfLE (spectralSequenceDataCoreE₁.le₁₂' (p, q) rfl rfl))) :=
  Functor.isoWhiskerLeft
    (stupidTruncTowerFunctor ⋙
      towerExtSpectralObjectFunctor ((DerivedCategory.singleFunctor C 0).obj M))
    (Abelian.SpectralObject.spectralSequenceFirstPageXNatIso
      spectralSequenceDataCoreE₁ (p, q) (-p - 1) (-p) rfl rfl (p + q) rfl)

/-- Evaluating the spectral object of the tower at the arrow `-p-1 ⟶ -p` *is* derived `Hom` out
of `M` of `mappingConeTowerFunctor p`: the two functors agree by definition, which is why
`mappingConeTowerFunctor` is written as that composite. -/
noncomputable def firstPageSrcIso (M : C) (p q : ℤ) :
    (stupidTruncTowerFunctor ⋙
        towerExtSpectralObjectFunctor ((DerivedCategory.singleFunctor C 0).obj M)) ⋙
      Abelian.SpectralObject.HObjFunctor (p + q)
        (ComposableArrows.mk₁ (homOfLE (spectralSequenceDataCoreE₁.le₁₂' (p, q) rfl rfl))) ≅
      mappingConeTowerFunctor p ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙
          (preadditiveCoyoneda.obj (Opposite.op
            ((DerivedCategory.singleFunctor C 0).obj M))).shift (p + q) :=
  Iso.refl _

/-- **From the cone form of the first page to `Extʲ(M, Kⁱ)`, naturally in `K`.** The three steps
are: the localisation of the homotopy category is the derived category
(`CategoryTheory.DerivedCategory.quotientCompQhIso`); the successive cone is `Kᵖ[-p]`
(`mappingConeTowerQNatIso`, the only non-formal step); and the shift bookkeeping
(`extSingleNatIso`). -/
noncomputable def firstPageNatIsoZExt (M : C) (p q : ℤ) :
    (stupidTruncTowerFunctor ⋙
        towerExtSpectralObjectFunctor ((DerivedCategory.singleFunctor C 0).obj M)) ⋙
      Abelian.SpectralObject.HObjFunctor (p + q)
        (ComposableArrows.mk₁ (homOfLE (spectralSequenceDataCoreE₁.le₁₂' (p, q) rfl rfl))) ≅
      zExtXFunctor.{u, v, w} M p q :=
  firstPageSrcIso M p q ≪≫
    Functor.isoWhiskerLeft (mappingConeTowerFunctor p)
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
        ((preadditiveCoyoneda.obj (Opposite.op
          ((DerivedCategory.singleFunctor C 0).obj M))).shift (p + q))) ≪≫
    Functor.isoWhiskerRight (mappingConeTowerQNatIso p)
      ((preadditiveCoyoneda.obj (Opposite.op
        ((DerivedCategory.singleFunctor C 0).obj M))).shift (p + q)) ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.eval C (ComplexShape.up ℤ) p)
      (extSingleNatIso ((DerivedCategory.singleFunctor C 0).obj M) p q)

/-- **The first page of the hyper-Ext spectral sequence is `Extʲ(M, Kⁱ)` naturally in `K`.**
This is the functorial form of the first-page identification of [Stacks, Tag 0AVI], and it is
what [Stacks, Tag 09Z2] needs: a morphism of complexes induces a morphism of spectral sequences
by `extComplexSpectralSequenceFunctor`, and on the first page that morphism is the one induced
on `Extʲ(M, -)` by the degreewise components. -/
noncomputable def extComplexSpectralSequenceFirstPageNatIso (M : C) (p q : ℤ) :
    extComplexSpectralSequenceFunctor.{u, v, w} M ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{w} _ 1 1 (le_refl 1) ⋙
          HomologicalComplex.eval AddCommGrpCat.{w} _ (p, q) ≅
      zExtXFunctor.{u, v, w} M p q :=
  firstPageNatIsoCone M p q ≪≫ firstPageNatIsoZExt M p q

/-- **The first page of the hyper-Ext spectral sequence of a single complex.** This is the
isomorphism `E₁^{p,q} ≅ Extʲ(M, Kᵖ)` of [Stacks, Tag 0AVI], obtained here as the component at
`K` of `extComplexSpectralSequenceFirstPageNatIso`. -/
noncomputable def extComplexSpectralSequenceFirstPageIso (M : C)
    (K : CochainComplex C ℤ) (p q : ℤ) :
    (((extComplexSpectralSequenceFunctor.{u, v, w} M).obj K).page 1).X (p, q) ≅
      AddCommGrpCat.of (Abelian.zExt M (K.X p) q) :=
  (extComplexSpectralSequenceFirstPageNatIso.{u, v, w} M p q).app K

/-- **The spectral sequence built here is the one [Stacks, Tag 0AVI] produces.** Both are the
spectral sequence of the tower of stupid truncations of `K` under derived `Hom` out of `M`, for the
same indexing data `StacksDraft.ExtSpectralSequence.spectralSequenceDataCoreE₁`; so the convergence
statements proved for `StacksDraft.ExtSpectralSequence.hyperExtSpectralSequence` are statements
about the functorial spectral sequence. -/
lemma extComplexSpectralSequenceFunctor_obj (M : C) (K : CochainComplex C ℤ) :
    (extComplexSpectralSequenceFunctor.{u, v, w} M).obj K =
      hyperExtSpectralSequence K M :=
  rfl

/-- **The abutment of the hyper-Ext spectral sequence, as a functor of the complex**:
`K ↦ Ext^n(M, K)`, which is `Hom(M, -)` of the shift by `n` of the image of `K` in the derived
category. It is the ambient object of the filtration
`StacksDraft.ExtSpectralSequence.hyperExtFiltration`. -/
@[sga "4½ Etat_0 3.2.1" "special case"]
noncomputable def zExtAbutmentFunctor (M : C) (n : ℤ) : CochainComplex C ℤ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ (preadditiveCoyoneda.obj
    (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))).shift n

/-- The value of `zExtAbutmentFunctor` is the abutment group it is named for. -/
lemma zExtAbutmentFunctor_obj (M : C) (n : ℤ) (K : CochainComplex C ℤ) :
    (zExtAbutmentFunctor.{u, v, w} M n).obj K =
      AddCommGrpCat.of (DerivedCategory.Ext ((DerivedCategory.singleFunctor C 0).obj M)
        (DerivedCategory.Q.obj K) n) :=
  rfl

/-- Degree `p` of the filtration is the image of the map induced by the inclusion of the stupid
truncation `σ^{≥p}K ⟶ K`, read through `zExtAbutmentFunctor`. -/
lemma extComplexFiltration_eq_imageSubobject (M : C) (K : CochainComplex C ℤ) (p n : ℤ) :
    hyperExtFiltration K M p n =
      imageSubobject ((zExtAbutmentFunctor.{u, v, w} M n).map
        (ιStupidTrunc K (embeddingUpIntGE p))) :=
  rfl

/-- **The abutment filtration of the hyper-Ext spectral sequence is natural in the complex.** A
morphism `φ : K ⟶ L` carries `Fil^p Ext^n(M, K)` into `Fil^p Ext^n(M, L)`: on the subobject
whose image the filtration step is, `φ` is the truncated map `σ^{≥p}φ`, by naturality of the
inclusion of a stupid truncation. -/
lemma exists_extComplexFiltration_le {K L : CochainComplex C ℤ} (φ : K ⟶ L) (M : C) (p n : ℤ) :
    (Subobject.«exists» ((zExtAbutmentFunctor.{u, v, w} M n).map φ)).obj
        (hyperExtFiltration K M p n) ≤ hyperExtFiltration L M p n := by
  rw [extComplexFiltration_eq_imageSubobject, extComplexFiltration_eq_imageSubobject,
    ← Subobject.imageSubobject_comp_eq_exists, ← Functor.map_comp,
    ← stupidTruncMap_ιStupidTrunc, Functor.map_comp]
  exact imageSubobject_comp_le _ _

/-- **The abutment filtration, with its ambient object written as the value of
`zExtAbutmentFunctor`.** This is `StacksDraft.ExtSpectralSequence.hyperExtFiltration`, and
nothing else; what the restatement buys is that the arrow cutting out a filtration step then
lands in the value of a *functor* of `K` on the nose, so that it can be composed with a natural
transformation out of that functor without the composite being type-correct only up to
unfolding. -/
def zExtAbutmentFiltration (M : C) (K : CochainComplex C ℤ) (p n : ℤ) :
    Subobject ((zExtAbutmentFunctor.{u, v, w} M n).obj K) :=
  hyperExtFiltration K M p n

/-- `StacksDraft.ExtSpectralSequence.hyperExtFiltration_antitone` at the ambient object of
`zExtAbutmentFiltration`. -/
lemma zExtAbutmentFiltration_antitone (M : C) (K : CochainComplex C ℤ) (n : ℤ) {p p' : ℤ}
    (h : p ≤ p') :
    zExtAbutmentFiltration.{u, v, w} M K p' n ≤ zExtAbutmentFiltration.{u, v, w} M K p n :=
  hyperExtFiltration_antitone K M n h

/-- `StacksDraft.ExtSpectralSequence.hyperExtFiltration_finite` at the ambient object of
`zExtAbutmentFiltration`. -/
lemma zExtAbutmentFiltration_finite (M : C) (K : CochainComplex C ℤ)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) (n : ℤ) :
    ∃ a b : ℤ, a ≤ b ∧ zExtAbutmentFiltration.{u, v, w} M K a n = ⊤ ∧
      zExtAbutmentFiltration.{u, v, w} M K b n = ⊥ :=
  hyperExtFiltration_finite K M hK n

/-- **The abutment filtration is natural in the complex**, at the ambient object of
`zExtAbutmentFiltration`: this is `exists_extComplexFiltration_le`. -/
lemma exists_zExtAbutmentFiltration_le {K L : CochainComplex C ℤ} (φ : K ⟶ L) (M : C) (p n : ℤ) :
    (Subobject.«exists» ((zExtAbutmentFunctor.{u, v, w} M n).map φ)).obj
        (zExtAbutmentFiltration.{u, v, w} M K p n) ≤
      zExtAbutmentFiltration.{u, v, w} M L p n :=
  exists_extComplexFiltration_le φ M p n

/-- **A late page of the functorial hyper-Ext spectral sequence is a graded piece of the
abutment filtration**: this is
`StacksDraft.ExtSpectralSequence.hyperExtSpectralSequencePageIsoFiltration`, read for the
spectral sequence `extComplexSpectralSequenceFunctor` produces — the same one, by
`extComplexSpectralSequenceFunctor_obj` — and at the ambient object of
`zExtAbutmentFiltration`. -/
def zExtAbutmentPageIsoFiltration (M : C) (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (p q r : ℤ) (hr : 1 ≤ r) (hhigh : q + 2 ≤ r) (hlow : p - a + 1 ≤ r) :
    (((extComplexSpectralSequenceFunctor.{u, v, w} M).obj K).page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE (zExtAbutmentFiltration.{u, v, w} M K (p + 1) (p + q))
        (zExtAbutmentFiltration.{u, v, w} M K p (p + q))
        (zExtAbutmentFiltration_antitone.{u, v, w} M K (p + q) (by omega))) :=
  hyperExtSpectralSequencePageIsoFiltration K M a p q r hr hhigh hlow

end StacksDraft.ExtSpectralSequenceFunctorial

end
