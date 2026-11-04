module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraizationDescentDatum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFinitenessFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfSheafTorsors
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent

/-!
# Gluing algebraizations of a formal space along a covering

Let `Y₀` be an algebraic space, `T ⊆ |Y₀|` closed and `g : W ⟶ Y₀_{/T}` a morphism of fppf
sheaves from a sheaf satisfying the set-theoretic condition of Stacks 0AIS. Let `{e i : X i ⟶ Y₀}`
be an fppf covering by locally Noetherian algebraic spaces, each `e i` locally of finite type,
and suppose that over each `X i` the base change `W ×_{Y₀/T} (X i)_{/T}` is the completion of a
morphism `M i ⟶ X i` locally of finite type which is an isomorphism over the complement of the
inverse image of `T`. This file proves that `W` is then itself the completion of a morphism
`X' ⟶ Y₀` locally of finite type which is an isomorphism over the complement of `T`.

This is the global step of the proof of Stacks 0ARB, which is run with the members `X i` of an
étale covering of `Y₀` by Noetherian affines and the algebraizations `M i` given by Stacks 0ARA.

* The algebraizations form a descent datum
  (`AlgebraicGeometry.Space.CompletionAlgebraization.descentData`), built from Stacks 0GDR.
* The descent datum is effective by
  `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_completionSheaf_iso`, the source's
  appeal to Stacks 0ADV, so the glued sheaf `X'` is an algebraic space.
* `X' ⟶ Y₀` is locally of finite type and an isomorphism over the complement of `T`, because its
  base changes to the members of the covering are the `M i`.
* The morphisms `(M i)_{/T} ⟶ W` glue to a morphism `X'_{/T} ⟶ W` over `Y₀_{/T}`, because they
  are compatible with the gluing isomorphisms; it is an isomorphism, because its base change to
  each `(X i)_{/T}` is the given identification of `(M i)_{/T}` with `W ×_{Y₀/T} (X i)_{/T}`.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp_of_jointlyLocallySurjective`: local
  finite type descends along a jointly surjective family of morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.Descent.descentInclusion_transport_move`: the canonical maps of the
  members of a descent datum into the sheaf it descends to identify a point with every point it
  is moved to.
* `AlgebraicGeometry.Space.CompletionAlgebraization.exists_completion_iso_of_cover`: the gluing
  step of Stacks 0ARB.
* `CompletionAlgebraization.mem_essImage_completionFiniteTypeModificationFunctor_of_cover`:
  the same, read as essential surjectivity of the functor of Stacks 0AR5 on the objects which are
  algebraizable over the members of an fppf covering.

## Implementation notes

Stacks 0GDR enters through `AlgebraicGeometry.Space.completionOverFunctor_map_bijective`, in the
construction of the descent datum. No attribute is placed in this file: the statement of Stacks
0ARB also needs Stacks 0ARA on the charts, which is not yet available in the form used here.

## References

* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory

/-- The move operation rebuilt from the gluing isomorphisms of a move operation is the original
one. -/
theorem familyTransportOfGluing_gluing_move {C : Type*} [Category C] [HasBinaryProducts C]
    {I : Type*} {A B : I → C} {p : ∀ i, A i ⟶ B i} (t : FamilyTransport A B p) {i j : I}
    {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) :
    (familyTransportOfGluing p t.gluing t.gluing_cocycle).move v y = t.move v y := by
  rw [familyTransportOfGluing_move, FamilyTransport.gluing_hom, prod.lift_snd, t.comp_move,
    prod.lift_fst, prod.lift_snd]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### Local finite type descends along a jointly surjective family -/

/-- **Stacks 06NR for a family.** Local finite type of the composites `f j ≫ g` descends to `g`
when the family `f j` is jointly surjective as a family of morphisms of fppf sheaves. -/
theorem isLocallyOfFiniteType_of_comp_of_jointlyLocallySurjective
    {J : Type v} {X : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : ∀ j, IsAlgebraicSpace B S hS (X j))
    (hY : IsAlgebraicSpace B S hS Y)
    (f : ∀ j, X j ⟶ Y) (g : Y ⟶ Z)
    (hfg : ∀ j, IsLocallyOfFiniteType B S hS (f j ≫ g))
    (hf : ∀ (U : BigFppfOver B S hS) (s : Y.obj (Opposite.op U)),
      (⨆ j, Presheaf.imageSieve (f j) s) ∈ BigFppfOver.topology B S hS U) :
    IsLocallyOfFiniteType B S hS g := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
  apply holdsOnEveryEtaleChart_of_comp_of_jointlyLocallySurjective B S hS
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ?_ hX hY f g hfg hf
  intro A B' C f' g' hcomp hcover
  let _ : LocallyOfFiniteType (f' ≫ g') := hcomp
  exact locallyOfFiniteType_of_comp_of_fppf_refinement f' g' hcover

/-! ### The canonical maps into a descended sheaf -/

namespace Descent

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ Y₀)
    (hcov : IsFppfCovering B S hS X f)
    (D : DescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace)

/-- **The canonical maps into a descended sheaf identify moved points.** For a descent datum `D`
relative to an fppf covering, a point `v` of `D.obj i` and its image under the move operation of
`D` to `D.obj j` have the same image in the sheaf `D` descends to. -/
theorem descentInclusion_transport_move {i j : ι} {Z : Over Y₀}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    (D.transport.move v y).left ≫ descentInclusion f hcov D j =
      v.left ≫ descentInclusion f hcov D i := by
  set E := (fppfDescentDataSheafEquivalence f hcov).inverse.obj D
  let φ : D ⟶ fibreDescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace E :=
    ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).inv
  have h1 := DescentData.move_naturality φ v y
  have h2 : (fibreDescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace
      E).transport.move (v ≫ (Over.map (f i)).map (φ.hom i)) y =
      fibreMove f E.obj (v ≫ (Over.map (f i)).map (φ.hom i)) y :=
    familyTransportOfGluing_gluing_move (fibreTransport f E.obj) _ y
  have h3 := congrArg (fun k => k.left ≫ pullback.fst E.obj.hom (f j)) h1
  simp only [Over.comp_left, Over.map_map_left, Category.assoc, h2, fibreMove_left_fst] at h3
  exact h3

/-- The canonical maps of the members of a descent datum relative to an fppf covering into the
sheaf it descends to are jointly surjective: every section of that sheaf lifts locally to one of
the members. -/
theorem iSup_imageSieve_descentInclusion_mem (U : BigFppfOver B S hS)
    (s : ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.left.obj (op U)) :
    (⨆ i, Presheaf.imageSieve (descentInclusion f hcov D i) s) ∈
      BigFppfOver.topology B S hS U := by
  obtain ⟨R, hR, hlift⟩ := exists_sieve_factorization_of_isFppfCovering B S hS X f hcov U
    (yonedaEquiv.symm s ≫ ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro W' k hk
  obtain ⟨i, η, hη⟩ := hlift k hk
  have hsq := isPullback_descentInclusion f hcov D i
  let ℓ := hsq.lift (yoneda.map k ≫ yonedaEquiv.symm s) η (by rw [Category.assoc, hη])
  simp only [iSup, Sieve.sSup_apply, Set.mem_range]
  refine ⟨_, ⟨i, rfl⟩, yonedaEquiv ℓ, ?_⟩
  have hℓ : ℓ ≫ descentInclusion f hcov D i = yoneda.map k ≫ yonedaEquiv.symm s :=
    hsq.lift_fst _ _ _
  rw [← yonedaEquiv_comp, hℓ, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simp

end Descent

/-! ### Sections of completions lift along a jointly surjective family -/

/-- Sections with equal images correspond to morphisms from representables with equal composites. -/
private theorem yonedaEquiv_symm_comp_eq {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) {V : BigFppfOver B S hS} (a : F.obj (op V)) (b : G.obj (op V))
    (h : f.app _ a = g.app _ b) : yonedaEquiv.symm a ≫ f = yonedaEquiv.symm b ≫ g := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  simpa using h

/-- If `η ≫ e = yoneda.map k ≫ x` then the section `η` of the source maps to the restriction
of `x` along `k`. -/
private theorem app_yonedaEquiv_eq_map {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ Y)
    {V W : BigFppfOver B S hS} (k : W ⟶ V) (x : Y.obj (op V)) (η : yoneda.obj W ⟶ X)
    (hη : η ≫ e = yoneda.map k ≫ yonedaEquiv.symm x) :
    e.app _ (yonedaEquiv η) = Y.map k.op x := by
  rw [← yonedaEquiv_comp, hη, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simp

/-- A section of `X` whose image under `a : X ⟶ Y` has point-set image in `T` has point-set image
in any set containing the preimage of `T`. -/
private theorem hasImageIn_of_hasImageIn_app
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ Y) {T : Set (points B S hS Y)}
    {TX : Set (points B S hS X)} (hTX : pointsMap B S hS X a ⁻¹' T ⊆ TX)
    {V : BigFppfOver B S hS} {t : X.obj (op V)} (hx : HasImageIn B S hS Y T V (a.app _ t)) :
    HasImageIn B S hS X TX V t := by
  rw [hasImageIn_iff_range_subset] at hx ⊢
  rintro _ ⟨w, rfl⟩
  apply hTX
  have := hx ⟨w, rfl⟩
  rwa [yonedaEquiv_symm_app_eq_comp, pointsMap_comp_apply] at this

/-- Sections of the completion subfunctor lift locally along a family of morphisms along which
sections lift locally. -/
private theorem familyImageSieve_completionSubfunctorMap_mem
    {ι : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : ∀ i, X i ⟶ Y) (T : Set (points B S hS Y)) (TX : ∀ i, Set (points B S hS (X i)))
    (hTX : ∀ i, pointsMap B S hS (X i) (a i) ⁻¹' T ⊆ TX i)
    (ha : ∀ i, pointsMap B S hS (X i) (a i) '' TX i ⊆ T)
    (hlift : ∀ (U : BigFppfOver B S hS) (s : Y.obj (op U)),
      (⨆ i, Presheaf.imageSieve (a i) s) ∈ BigFppfOver.topology B S hS U)
    (V : BigFppfOver B S hS) (x : (completionSubfunctor B S hS Y T).toFunctor.obj (op V)) :
    familyImageSieve (fun i => completionSubfunctorMap B S hS (a i) (TX i) T (ha i)) x ∈
      BigFppfOver.topology B S hS V := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_ (hlift V x.1.down)
  intro W' k hk
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hk
  obtain ⟨_, ⟨i, rfl⟩, t, ht⟩ := hk
  have hx : HasImageIn B S hS Y T W' (Y.map k.op x.1.down) :=
    ((completionSubfunctor B S hS Y T).toFunctor.map k.op x).2
  refine ⟨i, ⟨ULift.up t, hasImageIn_of_hasImageIn_app (a i) (hTX i) (ht ▸ hx)⟩, ?_⟩
  apply Subtype.ext
  apply ULift.ext
  exact ht

/-- For an fppf covering `e` of `Y₀` and a subfunctor `U` of `Y₀`, the restrictions
`U.fromPreimage (e i)` are jointly locally surjective. -/
private theorem familyImageSieve_fromPreimage_mem
    {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀} (hcov : IsFppfCovering B S hS X e)
    (U : Subfunctor Y₀) (V : BigFppfOver B S hS) (x : U.toFunctor.obj (op V)) :
    familyImageSieve (fun i => U.fromPreimage (e i)) x ∈ BigFppfOver.topology B S hS V := by
  obtain ⟨R, hR, hlift⟩ := exists_sieve_factorization_of_isFppfCovering B S hS X e hcov V
    (yonedaEquiv.symm x.1)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro W' k hk
  obtain ⟨i, η, hη⟩ := hlift k hk
  have h1 := app_yonedaEquiv_eq_map (e i) k x.1 η hη
  have hmem : yonedaEquiv η ∈ (U.preimage (e i)).obj (op W') := by
    show (e i).app _ (yonedaEquiv η) ∈ U.obj (op W')
    rw [h1]
    exact U.map k.op x.2
  exact ⟨i, ⟨yonedaEquiv η, hmem⟩, Subtype.ext h1⟩

/-! ### The gluing step -/

namespace CompletionAlgebraization

open _root_.AlgebraicGeometry.Space.Descent

variable {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Set (points B S hS Y₀)}
  {W : FormalSpace.FppfSheaf B S hS} (g : W ⟶ completionSheaf B S hS Y₀ T)
  (hT : IsClosed T)
  (hY₀ : IsAlgebraicSpace B S hS Y₀)
  {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀}
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
  (hXnoeth : ∀ i, HasEtaleLocalProperty B S hS (X i)
    (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
  (he : ∀ i, IsLocallyOfFiniteType B S hS (e i))
  {M : ∀ i, Over (X i)}
  (hM : ∀ i, IsFiniteTypeModification B S hS
    (openSubspaceOfPoints B S hS (X i) (pointsMap B S hS (X i) (e i) ⁻¹' T)ᶜ) (M i))
  (γ : ∀ i, completionSheaf B S hS (M i).left
    (pointsMap B S hS (M i).left (M i).hom ⁻¹' (pointsMap B S hS (X i) (e i) ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS (e i) T))
  (hγ : ∀ i, (γ i).hom ≫ pullback.snd g (completionSheafMap B S hS (e i) T) =
    completionSheafMap B S hS (M i).hom (pointsMap B S hS (X i) (e i) ⁻¹' T))
  (hcov : IsFppfCovering B S hS X e)

/-- The space over `Y₀` glued from the algebraizations. -/
abbrev glued : Over Y₀ :=
  ((fppfDescentDataSheafEquivalence e hcov).inverse.obj
    (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov)).obj

/-- The canonical map of the algebraization over `X i` into the glued space, over `Y₀`. -/
def gluedInclusion (i : ι) :
    (Over.map (e i)).obj (M i) ⟶ glued g hT hY₀ hX hXnoeth he hM γ hγ hcov :=
  Over.homMk (descentInclusion e hcov (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov) i)
    (isPullback_descentInclusion e hcov
      (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov) i).w

/-- The square formed by `gluedInclusion i`, the structure maps of `M i` and of the glued space,
and `e i` is a pullback: the algebraization over `X i` is the base change of the glued space. -/
theorem isPullback_gluedInclusion (i : ι) :
    IsPullback (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left (M i).hom
      (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).hom (e i) :=
  isPullback_descentInclusion e hcov (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov) i

/-- The glued space is an algebraic space: the descent datum is effective. -/
theorem isAlgebraicSpace_glued (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W) :
    IsAlgebraicSpace B S hS (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).left :=
  (isAlgebraicSpace_inverse_iff_isEffective e hcov _).2
    (DescentData.isEffective_of_completionSheaf_iso _ hcov T hW g (fun i => (hM i).2)
      (fun i => (hM i).1.2) γ hγ)

/-- The glued space is locally of finite type over `Y₀`. -/
theorem isLocallyOfFiniteType_glued (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W) :
    IsLocallyOfFiniteType B S hS (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).hom := by
  refine isLocallyOfFiniteType_of_comp_of_jointlyLocallySurjective (fun i => (hM i).1.1)
    (isAlgebraicSpace_glued g hT hY₀ hX hXnoeth he hM γ hγ hcov hW)
    (fun i => (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left) _
    (fun i => ?_) (iSup_imageSieve_descentInclusion_mem e hcov _)
  rw [(isPullback_gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).w]
  exact isLocallyOfFiniteType_comp B S hS (hM i).1.1 (hX i) hY₀ (M i).hom (e i) (hM i).2 (he i)

/-- The glued space is an isomorphism over the complement of `T`: its base change to the open
subspace `U` with points `|Y₀| ∖ T` is checked on the covering `U ×_{Y₀} X i`, where it is the
base change of `M i`. -/
theorem isIso_glued (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W) :
    IsIso (pullback.snd (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).hom
      (openSubspaceOfPoints B S hS Y₀ Tᶜ).ι) := by
  set U := openSubspaceOfPoints B S hS Y₀ Tᶜ
  set F := glued g hT hY₀ hX hXnoeth he hM γ hγ hcov
  have hF := isAlgebraicSpace_glued g hT hY₀ hX hXnoeth he hM γ hγ hcov hW
  have hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS) U.toFunctor :=
    isSheaf_openSubspaceOfPoints B S hS hY₀.isSheaf _
  have hiso : ∀ i, IsIso (pullback.snd (M i).hom (U.preimage (e i)).ι) := fun i => by
    have := (hM i).1.2
    rwa [← preimage_openSubspaceOfPoints_compl] at this
  let ρ : ∀ i, (U.preimage (e i)).toFunctor ⟶ U.toFunctor := fun i => U.fromPreimage (e i)
  have hρ : ∀ i, ρ i ≫ U.ι = (U.preimage (e i)).ι ≫ e i := fun i => U.fromPreimage_ι (e i)
  let π : ∀ i, pullback (M i).hom (U.preimage (e i)).ι ⟶ pullback F.hom U.ι := fun i =>
    pullback.lift (pullback.fst _ _ ≫
        (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left)
      (pullback.snd _ _ ≫ ρ i) (by
        rw [Category.assoc, Category.assoc, hρ,
          (isPullback_gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).w,
          ← Category.assoc, pullback.condition, Category.assoc])
  have hπ : ∀ i, IsPullback (π i) (pullback.snd _ _) (pullback.snd F.hom U.ι) (ρ i) := by
    intro i
    have houter : IsPullback (π i ≫ pullback.fst F.hom U.ι) (pullback.snd _ _) F.hom
        (ρ i ≫ U.ι) := by
      rw [pullback.lift_fst, hρ]
      exact (IsPullback.of_hasPullback (M i).hom (U.preimage (e i)).ι).paste_horiz
        (isPullback_gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i)
    exact IsPullback.of_right houter (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback F.hom U.ι)
  exact SheafTorsors.isIso_of_covering_pullbacks (BigFppfOver.topology B S hS)
    (Presheaf.isSheaf_pullback _ F.hom U.ι hF.isSheaf hU hY₀.isSheaf) hU
    (pullback.snd F.hom U.ι) (𝟙 _) (pullback.snd F.hom U.ι) (Category.comp_id _) ρ π ρ
    (fun i => pullback.snd _ _) (fun _ => 𝟙 _) hπ (fun i => IsPullback.id_vert (ρ i))
    (familyImageSieve_fromPreimage_mem hcov U)
    (fun i => asIso (pullback.snd (M i).hom (U.preimage (e i)).ι))
    (fun i => pullback.lift_snd _ _ _) (fun i => Category.comp_id _)

/-! ### The morphisms to `W` on sections -/

/-- The morphism to `W` of the completion of the algebraization over `X i`, on the completion
subfunctor. -/
def label (i : ι) :
    (completionSubfunctor B S hS ((Over.map (e i)).obj (M i)).left
      (pointsMap B S hS ((Over.map (e i)).obj (M i)).left ((Over.map (e i)).obj (M i)).hom ⁻¹'
        T)).toFunctor ⟶ W.obj :=
  (completionSheafIsoSubfunctor B S hS (X := ((Over.map (e i)).obj (M i)).left)
    (hM i).1.1.isSheaf _).inv ≫ (toWHom g (e i) (M i) (γ i)).hom

/-- The morphism to `W` is natural for morphisms over `Y₀`. -/
theorem completionSubfunctorMap_comp_label {Z : Over Y₀}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z.left) (i : ι)
    (v : Z ⟶ (Over.map (e i)).obj (M i)) :
    completionSubfunctorMap B S hS v.left (pointsMap B S hS Z.left Z.hom ⁻¹' T) _
        (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w v) T) ≫ label g hM γ i =
      (completionSheafIsoSubfunctor B S hS hZ _).inv ≫
        (completionOverMap B S hS T v ≫ toWHom g (e i) (M i) (γ i)).hom := by
  have h := toSheafify_comp_completionOverMap (T := T) v
  simp only [label, completionSheafIsoSubfunctor, Iso.symm_inv,
    GrothendieckTopology.isoSheafify_hom, ObjectProperty.FullSubcategory.comp_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (toWHom g (e i) (M i) (γ i)).hom) h.symm).trans (Category.assoc _ _ _))

include hγ in
/-- The morphism to `W` lies over the completion of `Y₀`. -/
theorem label_comp (i : ι) :
    label g hM γ i ≫ g.hom ≫ (completionSheafIsoSubfunctor B S hS hY₀.isSheaf T).hom =
      completionMap B S hS ((Over.map (e i)).obj (M i)).hom T := by
  have h := toWHom_comp g (e i) (M i) (γ i) (hγ i)
  have h' : (toWHom g (e i) (M i) (γ i)).hom ≫ g.hom =
      (completionSheafMap B S hS ((Over.map (e i)).obj (M i)).hom T).hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, h]
  have hMi : IsAlgebraicSpace B S hS ((Over.map (e i)).obj (M i)).left := (hM i).1.1
  rw [label, Category.assoc, ← Category.assoc (toWHom g (e i) (M i) (γ i)).hom, h',
    completionSheafMap_hom_comp_completionSheafIsoSubfunctor_hom
      (X' := ((Over.map (e i)).obj (M i)).left) hMi.isSheaf hY₀.isSheaf,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

include hγ in
/-- **Sections of the completion of an algebraization are determined by their image in `W` and
their image in the chart.** -/
theorem label_injective (i : ι) {V : BigFppfOver B S hS}
    {x₁ x₂ : (completionSubfunctor B S hS ((Over.map (e i)).obj (M i)).left
      (pointsMap B S hS ((Over.map (e i)).obj (M i)).left ((Over.map (e i)).obj (M i)).hom ⁻¹'
        T)).toFunctor.obj (op V)}
    (h₁ : (label g hM γ i).app _ x₁ = (label g hM γ i).app _ x₂)
    (h₂ : (M i).hom.app _ x₁.1.down = (M i).hom.app _ x₂.1.down) : x₁ = x₂ := by
  set c := (completionSheafIsoSubfunctor B S hS (X := ((Over.map (e i)).obj (M i)).left)
    (hM i).1.1.isSheaf
    (pointsMap B S hS ((Over.map (e i)).obj (M i)).left ((Over.map (e i)).obj (M i)).hom ⁻¹'
      T)) with hc
  have hP := (isPullback_toW g (e i) (M i) (γ i) (hγ i)).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ⋙
      (evaluation _ _).obj (op V))
  have hs : c.inv ≫ (completionOverMap B S hS T (Descent.structureMap (e i) (M i))).hom =
      completionSubfunctorMap B S hS (Descent.structureMap (e i) (M i)).left _ _
        (image_preimage_subset_preimage_of_comp_eq B S hS
          (Over.w (Descent.structureMap (e i) (M i))) T) ≫
        (BigFppfOver.topology B S hS).toSheafify _ := by
    rw [hc]
    simp only [completionSheafIsoSubfunctor, Iso.symm_inv, GrothendieckTopology.isoSheafify_hom]
    exact toSheafify_comp_completionOverMap (T := T) (Descent.structureMap (e i) (M i))
  have hsub : (completionSubfunctorMap B S hS (Descent.structureMap (e i) (M i)).left _ _
      (image_preimage_subset_preimage_of_comp_eq B S hS
        (Over.w (Descent.structureMap (e i) (M i))) T)).app (op V) x₁ =
      (completionSubfunctorMap B S hS (Descent.structureMap (e i) (M i)).left _ _
      (image_preimage_subset_preimage_of_comp_eq B S hS
        (Over.w (Descent.structureMap (e i) (M i))) T)).app (op V) x₂ := by
    apply Subtype.ext
    apply ULift.ext
    exact h₂
  have hsnd : (c.inv ≫ (completionOverMap B S hS T (Descent.structureMap (e i) (M i))).hom).app
      (op V) x₁ =
      (c.inv ≫ (completionOverMap B S hS T (Descent.structureMap (e i) (M i))).hom).app
      (op V) x₂ := by
    rw [hs]
    exact congrArg (fun y => ((BigFppfOver.topology B S hS).toSheafify
      (completionSubfunctor B S hS (Over.mk (e i)).left
        (pointsMap B S hS (Over.mk (e i)).left (Over.mk (e i)).hom ⁻¹' T)).toFunctor).app
          (op V) y) hsub
  have : c.inv.app _ x₁ = c.inv.app _ x₂ := Types.ext_of_isPullback hP h₁ hsnd
  simpa using congrArg (c.hom.app (op V)) this

/-- The section of the completion subfunctor of a representable presheaf given by the identity,
when the structure morphism lands over `T`. -/
private theorem hasImageIn_one {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Y₀}
    {V : BigFppfOver B S hS} {a : Z.obj (op V)}
    (ha : HasImageIn B S hS Z (pointsMap B S hS Z z ⁻¹' T) V a) :
    HasImageIn B S hS (yoneda.obj V) (pointsMap B S hS _ (yonedaEquiv.symm a ≫ z) ⁻¹' T) V
      (𝟙 V) := by
  have h1 : (yonedaEquiv.symm a).app (op V) (𝟙 V) = a := by
    rw [← yonedaEquiv_apply, Equiv.apply_symm_apply]
  refine hasImageIn_of_comp_eq (g := z) (g' := yonedaEquiv.symm a ≫ z)
    (a := yonedaEquiv.symm a) (b := 𝟙 _) (Category.id_comp _).symm (op V) (𝟙 V) ?_
  rwa [h1]

include hγ in
/-- **Moving a section.** A section `a` of `M i` over a section `y` of `X j` with the same image
in `Y₀` is moved to a section `b` of `M j` over `y`, with the same image in the glued space and,
over `T`, the same image in `W`. -/
theorem exists_move_section {i j : ι} {V : BigFppfOver B S hS} (a : (M i).left.obj (op V))
    (y : (X j).obj (op V)) (h : (e i).app _ ((M i).hom.app _ a) = (e j).app _ y) :
    ∃ b : (M j).left.obj (op V), (M j).hom.app _ b = y ∧
      (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov j).left.app _ b =
        (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left.app _ a ∧
      ∀ ha hb, (label g hM γ j).app _ ⟨ULift.up b, hb⟩ =
        (label g hM γ i).app _ ⟨ULift.up a, ha⟩ := by
  set t := transport g hT hY₀ hX hXnoeth he hM γ hγ
  let ya : yoneda.obj V ⟶ (M i).left := yonedaEquiv.symm a
  let yy : yoneda.obj V ⟶ X j := yonedaEquiv.symm y
  have hw : ya ≫ (M i).hom ≫ e i = yy ≫ e j :=
    yonedaEquiv_symm_comp_eq ((M i).hom ≫ e i) (e j) a y h
  let Zo : Over Y₀ := Over.mk (ya ≫ (M i).hom ≫ e i)
  let v : Zo ⟶ (Over.map (e i)).obj (M i) := Over.homMk ya rfl
  let w : Zo ⟶ Over.mk (e j) := Over.homMk yy hw.symm
  let m := t.move v w
  have hm₁ : m.left ≫ (M j).hom = yy := congrArg CommaMorphism.left (t.move_base v w)
  have hm₂ : m.left ≫ (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov j).left =
      ya ≫ (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left := by
    have := descentInclusion_transport_move e hcov
      (descentData g hT hY₀ hX hXnoeth he hM γ hγ hcov) v w
    rwa [descentData_transport_move] at this
  refine ⟨yonedaEquiv m.left, ?_, ?_, fun ha hb => ?_⟩
  · rw [← yonedaEquiv_comp, hm₁]
    simp [yy]
  · rw [← yonedaEquiv_comp, hm₂, yonedaEquiv_comp]
    simp [ya]
  · have hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Zo.left :=
      (isAlgebraicSpace_yoneda B S hS V).isSheaf
    have key := (completionSubfunctorMap_comp_label g hM γ hZ j m).trans
      ((congrArg (fun φ => (completionSheafIsoSubfunctor B S hS hZ _).inv ≫ φ.hom)
        (completionOverMap_move_comp_toWHom g hT hY₀ hX hXnoeth he hM γ hγ v w)).trans
          (completionSubfunctorMap_comp_label g hM γ hZ i v).symm)
    have hσ : HasImageIn B S hS Zo.left (pointsMap B S hS Zo.left Zo.hom ⁻¹' T) V (𝟙 V) :=
      hasImageIn_one ha
    have key' := congrArg (fun φ => φ.app (op V) ⟨ULift.up (𝟙 V), hσ⟩) key
    have e1 : (label g hM γ j).app (op V) ⟨ULift.up (yonedaEquiv m.left), hb⟩ =
        (completionSubfunctorMap B S hS m.left (pointsMap B S hS Zo.left Zo.hom ⁻¹' T) _
          (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w m) T) ≫
            label g hM γ j).app (op V) ⟨ULift.up (𝟙 V), hσ⟩ := rfl
    have e2 : (label g hM γ i).app (op V) ⟨ULift.up a, ha⟩ =
        (completionSubfunctorMap B S hS v.left (pointsMap B S hS Zo.left Zo.hom ⁻¹' T) _
          (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w v) T) ≫
            label g hM γ i).app (op V) ⟨ULift.up (𝟙 V), hσ⟩ := by
      show _ = (label g hM γ i).app (op V) ⟨ULift.up (ya.app (op V) (𝟙 V)), _⟩
      exact congrArg ((label g hM γ i).app (op V))
        (Subtype.ext (congrArg ULift.up (by rw [← yonedaEquiv_apply, Equiv.apply_symm_apply])))
    exact (e1.trans key').trans e2.symm

/-- A section with the same image in `Y₀` as a section over `T` is over `T`. -/
private theorem hasImageIn_of_app_eq {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Y₀}
    {V : BigFppfOver B S hS} {b b' : Z.obj (op V)} (h : z.app _ b = z.app _ b')
    (hb' : HasImageIn B S hS Z (pointsMap B S hS Z z ⁻¹' T) V b') :
    HasImageIn B S hS Z (pointsMap B S hS Z z ⁻¹' T) V b := by
  have e := yonedaEquiv_symm_comp_eq z z b b' h
  rw [hasImageIn_iff_range_subset] at hb' ⊢
  rintro _ ⟨w, rfl⟩
  have := hb' ⟨w, rfl⟩
  simp only [Set.mem_preimage, ← pointsMap_comp_apply] at this ⊢
  rwa [e]

/-- The completion of the canonical map of the algebraization over `X i` into the glued space, on
completion subfunctors. -/
abbrev gluedProj (i : ι) :=
  completionSubfunctorMap B S hS (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left
    _ _ (image_preimage_subset_preimage_of_comp_eq B S hS
      (Over.w (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i)) T)

/-- A section of `(X i)` and its image in `Y₀`. -/
private theorem app_gluedInclusion_hom (i : ι) {V : BigFppfOver B S hS}
    (a : (M i).left.obj (op V)) :
    (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).hom.app _
      ((gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left.app _ a) =
      (e i).app _ ((M i).hom.app _ a) :=
  congrArg (fun φ => φ.app (op V) a)
    (Over.w (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i))

include hγ in
/-- Sections of the completions of the algebraizations with the same image in the glued space
have the same image in `W`. -/
theorem label_eq_of_gluedProj_eq {i j : ι} {V : BigFppfOver B S hS}
    (s : (completionSubfunctor B S hS ((Over.map (e i)).obj (M i)).left
      (pointsMap B S hS ((Over.map (e i)).obj (M i)).left ((Over.map (e i)).obj (M i)).hom ⁻¹'
        T)).toFunctor.obj (op V))
    (t : (completionSubfunctor B S hS ((Over.map (e j)).obj (M j)).left
      (pointsMap B S hS ((Over.map (e j)).obj (M j)).left ((Over.map (e j)).obj (M j)).hom ⁻¹'
        T)).toFunctor.obj (op V))
    (h : (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov i).app _ s =
      (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov j).app _ t) :
    (label g hM γ i).app _ s = (label g hM γ j).app _ t := by
  obtain ⟨⟨a⟩, ha⟩ := s
  obtain ⟨⟨b'⟩, hb'⟩ := t
  have hι : (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i).left.app _ a =
      (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov j).left.app _ b' :=
    congrArg (fun x => x.1.down) h
  have hY : (e i).app _ ((M i).hom.app _ a) = (e j).app _ ((M j).hom.app _ b') := by
    rw [← app_gluedInclusion_hom, ← app_gluedInclusion_hom, hι]
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_move_section g hT hY₀ hX hXnoeth he hM γ hγ hcov a
    ((M j).hom.app _ b') hY
  obtain rfl : b = b' := Types.ext_of_isPullback
    ((isPullback_gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov j).map
      ((evaluation _ _).obj (op V))) (hb₂.trans hι) hb₁
  exact (hb₃ ha hb').symm

include hγ in
/-- Sections of the completions of the algebraizations with the same image in `W` have the same
image in the glued space. -/
theorem gluedProj_eq_of_label_eq {i j : ι} {V : BigFppfOver B S hS}
    (s : (completionSubfunctor B S hS ((Over.map (e i)).obj (M i)).left
      (pointsMap B S hS ((Over.map (e i)).obj (M i)).left ((Over.map (e i)).obj (M i)).hom ⁻¹'
        T)).toFunctor.obj (op V))
    (t : (completionSubfunctor B S hS ((Over.map (e j)).obj (M j)).left
      (pointsMap B S hS ((Over.map (e j)).obj (M j)).left ((Over.map (e j)).obj (M j)).hom ⁻¹'
        T)).toFunctor.obj (op V))
    (h : (label g hM γ i).app _ s = (label g hM γ j).app _ t) :
    (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov i).app _ s =
      (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov j).app _ t := by
  have e1 := congrArg (fun φ => φ.app (op V) s) (label_comp g hY₀ hM γ hγ i)
  have e2 := congrArg (fun φ => φ.app (op V) t) (label_comp g hY₀ hM γ hγ j)
  have e3 := congrArg ((g.hom ≫ (completionSheafIsoSubfunctor B S hS hY₀.isSheaf T).hom).app
    (op V)) h
  have e4 := e1.symm.trans (e3.trans e2)
  obtain ⟨⟨a⟩, ha⟩ := s
  obtain ⟨⟨b'⟩, hb'⟩ := t
  have hY : (e i).app _ ((M i).hom.app _ a) = (e j).app _ ((M j).hom.app _ b') :=
    congrArg (fun x => x.1.down) e4
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_move_section g hT hY₀ hX hXnoeth he hM γ hγ hcov a
    ((M j).hom.app _ b') hY
  have hbT : HasImageIn B S hS ((Over.map (e j)).obj (M j)).left
      (pointsMap B S hS ((Over.map (e j)).obj (M j)).left ((Over.map (e j)).obj (M j)).hom ⁻¹' T)
      V b :=
    hasImageIn_of_app_eq (z := ((Over.map (e j)).obj (M j)).hom)
      (congrArg ((e j).app _) hb₁) hb'
  have hbb := label_injective g hM γ hγ j (x₁ := ⟨ULift.up b, hbT⟩) (x₂ := ⟨ULift.up b', hb'⟩)
    ((hb₃ ha hbT).trans h) hb₁
  obtain rfl : b = b' := congrArg (fun x => x.1.down) hbb
  exact Subtype.ext (congrArg ULift.up hb₂.symm)

/-- Sections of the completion of the glued space lift locally to the completions of the
algebraizations. -/
private theorem familyImageSieve_gluedProj_mem (V : BigFppfOver B S hS)
    (x : (completionSubfunctor B S hS (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).left
      (pointsMap B S hS _ (glued g hT hY₀ hX hXnoeth he hM γ hγ hcov).hom ⁻¹'
        T)).toFunctor.obj (op V)) :
    familyImageSieve (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov) x ∈
      BigFppfOver.topology B S hS V :=
  familyImageSieve_completionSubfunctorMap_mem _ _ _
    (fun i => (preimage_pointsMap_over B S hS T
      (gluedInclusion g hT hY₀ hX hXnoeth he hM γ hγ hcov i)).ge) _
    (iSup_imageSieve_descentInclusion_mem e hcov _) V x

include hγ hX hY₀ hcov in
/-- Sections of `W` lift locally to the completions of the algebraizations. -/
private theorem familyImageSieve_label_mem (V : BigFppfOver B S hS) (w : W.obj.obj (op V)) :
    familyImageSieve (label g hM γ) w ∈ BigFppfOver.topology B S hS V := by
  set cY := completionSheafIsoSubfunctor B S hS hY₀.isSheaf T
  set xh := (g.hom ≫ cY.hom).app (op V) w
  obtain ⟨R, hR, hlift⟩ := exists_sieve_factorization_of_isFppfCovering B S hS X e hcov V
    (yonedaEquiv.symm xh.1.down)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro W' k hk
  obtain ⟨i, η, hη⟩ := hlift k hk
  have hηY := app_yonedaEquiv_eq_map (e i) k xh.1.down η hη
  have hc₀ : HasImageIn B S hS (X i) (pointsMap B S hS (X i) (e i) ⁻¹' T) W' (yonedaEquiv η) :=
    hasImageIn_of_hasImageIn_app (e i) subset_rfl
      (hηY ▸ ((completionSubfunctor B S hS Y₀ T).toFunctor.map k.op xh).2)
  set cX := completionSheafIsoSubfunctor B S hS (hX i).isSheaf (pointsMap B S hS (X i) (e i) ⁻¹' T)
  let c := cX.inv.app (op W') ⟨ULift.up (yonedaEquiv η), hc₀⟩
  have hcond : g.hom.app (op W') (W.obj.map k.op w) =
      (completionSheafMap B S hS (e i) T).hom.app (op W') c := by
    apply (show Function.Injective (cY.hom.app (op W')) from fun a b hab => by
      simpa using congrArg (cY.inv.app (op W')) hab)
    have h1 : cY.hom.app (op W') (g.hom.app (op W') (W.obj.map k.op w)) =
        (completionSubfunctor B S hS Y₀ T).toFunctor.map k.op xh :=
      ((g.hom ≫ cY.hom).naturality_apply k.op w)
    have h2 := congrArg (fun φ => φ.app (op W') c)
      (completionSheafMap_hom_comp_completionSheafIsoSubfunctor_hom (hX i).isSheaf hY₀.isSheaf
        (e i) T)
    change ((completionSheafMap B S hS (e i) T).hom ≫ cY.hom).app (op W') c = _ at h2
    show _ = ((completionSheafMap B S hS (e i) T).hom ≫ cY.hom).app (op W') c
    rw [h1, h2]
    apply Subtype.ext
    apply ULift.ext
    show Y₀.map k.op xh.1.down = (e i).app _ (cX.hom.app (op W') c).1.down
    have h3 : cX.hom.app (op W') c = ⟨ULift.up (yonedaEquiv η), hc₀⟩ :=
      congrArg (fun φ => φ.app (op W') ⟨ULift.up (yonedaEquiv η), hc₀⟩) cX.inv_hom_id
    rw [h3]
    exact hηY.symm
  have hP := (isPullback_toW g (e i) (M i) (γ i) (hγ i)).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ⋙
      (evaluation _ _).obj (op W'))
  obtain ⟨m, hm₁, -⟩ := Types.exists_of_isPullback hP (W.obj.map k.op w) c hcond
  refine ⟨i, (completionSheafIsoSubfunctor B S hS (X := ((Over.map (e i)).obj (M i)).left)
    (hM i).1.1.isSheaf _).hom.app (op W') m, ?_⟩
  show (toWHom g (e i) (M i) (γ i)).hom.app (op W') (((completionSheafIsoSubfunctor B S hS
    (X := ((Over.map (e i)).obj (M i)).left) (hM i).1.1.isSheaf _).inv.app (op W'))
      (((completionSheafIsoSubfunctor B S hS (X := ((Over.map (e i)).obj (M i)).left)
        (hM i).1.1.isSheaf _).hom.app (op W')) m)) = _
  simp only [Iso.hom_inv_id_app_apply]
  exact hm₁

include hT hY₀ hX hXnoeth he hM γ hγ hcov in
/-- **The gluing step of Stacks 0ARB.** Let `Y₀` be an algebraic space, `T ⊆ |Y₀|` closed and
`g : W ⟶ Y₀_{/T}` a morphism from an fppf sheaf satisfying the set-theoretic condition of Stacks
0AIS. Let `{e i : X i ⟶ Y₀}` be an fppf covering, each `e i` locally of finite type with `X i` a
locally Noetherian algebraic space, and let `M i ⟶ X i` be morphisms locally of finite type which
are isomorphisms over the complement of the inverse image of `T`, with isomorphisms `γ i` over
`(X i)_{/T}` from their completions to `W ×_{Y₀/T} (X i)_{/T}`. Then there is a morphism
`X' ⟶ Y₀` locally of finite type which is an isomorphism over the complement of `T`, whose
completion along `T` is isomorphic to `g` over `Y₀_{/T}`.

The proof is the source's: the `M i` form a descent datum by full faithfulness of completion
(Stacks 0GDR), which is effective by the source's appeal to Stacks 0ADV, and the morphisms
`(M i)_{/T} ⟶ W` glue to an isomorphism `X'_{/T} ≅ W`. -/
theorem exists_completion_iso_of_cover
    (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W) :
    ∃ N : Over Y₀, IsFiniteTypeModification B S hS (openSubspaceOfPoints B S hS Y₀ Tᶜ) N ∧
      Nonempty ((completionOverFunctor B S hS T).obj N ≅ Over.mk g) := by
  set F := glued g hT hY₀ hX hXnoeth he hM γ hγ hcov
  have hF := isAlgebraicSpace_glued g hT hY₀ hX hXnoeth he hM γ hγ hcov hW
  have hPs := isSheaf_completionSubfunctor B S hS hF.isSheaf (pointsMap B S hS F.left F.hom ⁻¹' T)
  obtain ⟨ψ, hψ, -⟩ := exists_hom_of_familyImageSieve (BigFppfOver.topology B S hS) W.property
    (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov)
    (familyImageSieve_gluedProj_mem g hT hY₀ hX hXnoeth he hM γ hγ hcov) (label g hM γ)
    (fun _ _ _ s t h => label_eq_of_gluedProj_eq g hT hY₀ hX hXnoeth he hM γ hγ hcov s t h)
  obtain ⟨ψ', hψ', -⟩ := exists_hom_of_familyImageSieve (BigFppfOver.topology B S hS) hPs
    (label g hM γ) (familyImageSieve_label_mem g hY₀ hX hM γ hγ hcov)
    (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov)
    (fun _ _ _ s t h => gluedProj_eq_of_label_eq g hT hY₀ hX hXnoeth he hM γ hγ hcov s t h)
  have h₁ : ψ ≫ ψ' = 𝟙 _ := hom_ext_of_familyImageSieve (BigFppfOver.topology B S hS) hPs
    (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov)
    (familyImageSieve_gluedProj_mem g hT hY₀ hX hXnoeth he hM γ hγ hcov)
    (fun i => by rw [← Category.assoc, hψ, hψ', Category.comp_id])
  have h₂ : ψ' ≫ ψ = 𝟙 _ := hom_ext_of_familyImageSieve (BigFppfOver.topology B S hS) W.property
    (label g hM γ) (familyImageSieve_label_mem g hY₀ hX hM γ hγ hcov)
    (fun i => by rw [← Category.assoc, hψ', hψ, Category.comp_id])
  let e₀ : (completionSheaf B S hS F.left (pointsMap B S hS F.left F.hom ⁻¹' T)).obj ≅ W.obj :=
    completionSheafIsoSubfunctor B S hS hF.isSheaf _ ≪≫ ⟨ψ, ψ', h₁, h₂⟩
  let Φ : completionSheaf B S hS F.left (pointsMap B S hS F.left F.hom ⁻¹' T) ≅ W :=
    (fullyFaithfulSheafToPresheaf (BigFppfOver.topology B S hS) _).preimageIso e₀
  have hψg : ψ ≫ g.hom ≫ (completionSheafIsoSubfunctor B S hS hY₀.isSheaf T).hom =
      completionMap B S hS F.hom T := by
    refine hom_ext_of_familyImageSieve (BigFppfOver.topology B S hS)
      (isSheaf_completionSubfunctor B S hS hY₀.isSheaf T)
      (gluedProj g hT hY₀ hX hXnoeth he hM γ hγ hcov)
      (familyImageSieve_gluedProj_mem g hT hY₀ hX hXnoeth he hM γ hγ hcov) (fun i => ?_)
    rw [← Category.assoc, hψ, label_comp g hY₀ hM γ hγ i]
    ext V x
    apply Subtype.ext
    apply ULift.ext
    exact (app_gluedInclusion_hom g hT hY₀ hX hXnoeth he hM γ hγ hcov i x.1.down).symm
  have hΦ : Φ.hom ≫ g = completionSheafMap B S hS F.hom T := by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ← cancel_mono
      (completionSheafIsoSubfunctor B S hS hY₀.isSheaf T).hom, Category.assoc,
      completionSheafMap_hom_comp_completionSheafIsoSubfunctor_hom hF.isSheaf hY₀.isSheaf]
    show e₀.hom ≫ _ = _
    simp only [e₀, Iso.trans_hom, Category.assoc]
    show _ ≫ ψ ≫ _ = _
    rw [hψg]
  exact ⟨F, ⟨⟨hF, isIso_glued g hT hY₀ hX hXnoeth he hM γ hγ hcov hW⟩,
    isLocallyOfFiniteType_glued g hT hY₀ hX hXnoeth he hM γ hγ hcov hW⟩,
    ⟨Over.isoMk Φ hΦ⟩⟩

end CompletionAlgebraization

/-! ### Essential surjectivity of the functor of Stacks 0AR5, from charts -/

namespace CompletionAlgebraization

/-- **Essential surjectivity of the functor of Stacks 0AR5, from algebraizations over a
covering.** Let `Y₀` be a locally Noetherian algebraic space, `T ⊆ |Y₀|` closed and
`g : W ⟶ Y₀_{/T}` an object of the right-hand collection of Stacks 0AR5. If, over each member
`X i` of an fppf covering of `Y₀` by locally Noetherian algebraic spaces locally of finite type
over `Y₀`, the base change `W ×_{Y₀/T} (X i)_{/T}` is the completion of a finite-type
modification of `X i`, then `g` is in the essential image of the functor of Stacks 0AR5. This is
the global step of the proof of Stacks 0ARB, which applies it with the affine charts of an étale
covering and the algebraizations of Stacks 0ARA. -/
theorem mem_essImage_completionFiniteTypeModificationFunctor_of_cover
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS Y₀)) (hT : IsClosed T) (hY₀ : IsLocallyNoetherian B S hS Y₀)
    (h0AIZ : FormalSpace.IsFormalAlgebraicSpaceCompletionSheaf B S hS Y₀ T)
    (hnoeth : FormalSpace.IsLocallyNoetherianCompletionSheaf B S hS Y₀ T)
    (hred : FormalSpace.ChartSquareReducesToIsEtaleOutsideModifications T)
    (W : FormalSpace.RigEtaleOverCompletion B S hS Y₀ T)
    {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀}
    (hcov : IsFppfCovering B S hS X e)
    (hXnoeth : ∀ i, HasEtaleLocalProperty B S hS (X i)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (he : ∀ i, IsLocallyOfFiniteType B S hS (e i))
    (hloc : ∀ i, ∃ M : FiniteTypeModification B S hS
        (openSubspaceOfPoints B S hS (X i) (pointsMap B S hS (X i) (e i) ⁻¹' T)ᶜ),
      Nonempty ((completionOverFunctor B S hS (pointsMap B S hS (X i) (e i) ⁻¹' T)).obj M.obj ≅
        Over.mk (pullback.snd W.obj.hom (completionSheafMap B S hS (e i) T)))) :
    (FormalSpace.completionFiniteTypeModificationFunctor T hT hY₀ h0AIZ hnoeth hred).essImage
      W := by
  choose M hM using hloc
  let γ' := fun i => (hM i).some
  obtain ⟨N, hN, ⟨φ⟩⟩ := exists_completion_iso_of_cover W.obj.hom hT
    hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace hXnoeth he (M := fun i => (M i).obj)
    (fun i => (M i).property) (fun i => (Over.forget _).mapIso (γ' i)) (fun i => Over.w (γ' i).hom)
    hcov W.property.1.1
  exact ⟨⟨N, hN⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (φ ≪≫ Over.isoMk (Iso.refl _) (by simp))⟩⟩

end CompletionAlgebraization

end AlgebraicGeometry.Space

end
