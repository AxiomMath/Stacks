module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationInitial.Basic
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationCharacterization.Basic
public import StacksFrontier.AlgebraicGeometry.AffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Local

/-!
# Absolute weak normalization among universal homeomorphisms

For a universal homeomorphism `Y ⟶ X`, the canonical morphism from the absolute weak
normalization of `X` to `Y` is an isomorphism exactly when `Y` is absolutely weakly normal.

## Main results

* `AlgebraicGeometry.isIso_initialMap_iff_isAbsolutelyWeaklyNormal` characterizes when the
  initial universal homeomorphism maps isomorphically to another universal homeomorphism.

## Implementation notes

The absolute weak normalization is the chosen initial object of the category of universal
homeomorphisms over `X`.  Its canonical map to `Y` is the underlying scheme morphism of the
unique initial morphism to `Y` in that category.

The statement is reduced in three steps.  A map out of an initial object is an isomorphism
exactly when its target is also initial, and in the full subcategory of `Over X` that question
is the same as for the underlying scheme morphism.  Over an affine base the initial object is
the spectrum of the ring-level absolute weak normalization, by the terminality of
`AlgebraicGeometry.absoluteWeakNormalizationCategoryObject` transported along the
`Γ`-`Spec` adjunction for algebras, so there the characterization is the ring-level one,
`AlgebraicGeometry.isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing`.
A general base is covered by affine opens, over each of which the restriction of the chosen
initial object is again initial; both sides of the equivalence are local on that cover — the
left by Zariski-locality of being an isomorphism, the right by Tag 0EUP — so the affine case
suffices.

## Implementation notes on hypotheses

`[HasLocallyInitialUniversalHomeomorphismOver X]` is carried as an instance argument.  In the
statement of the tag it is supplied by the global instance that is Tag 0EUS's
`absolute_weak_normalization_initial` label, which carries no proof there, so making it
explicit states exactly the tag's hypothesis rather than adding one; this is also
what the companion label `absolute_weak_normalization_functorial` does
(`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial`).  Its restriction
clause, and not merely `CategoryTheory.Limits.HasInitial`, is what the affine-local step uses,
through `AlgebraicGeometry.isInitial_pullback_initial`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry



/-- Being a homeomorphism on underlying spaces contains the identities. -/
instance topologicallyIsHomeomorph_containsIdentities :
    (topologically @IsHomeomorph).ContainsIdentities where
  id_mem X := by
    change IsHomeomorph (fun x : X => x)
    exact ⟨continuous_id, IsOpenMap.id, Function.bijective_id⟩

/-- Being a homeomorphism on underlying spaces is stable under composition. -/
instance topologicallyIsHomeomorph_isStableUnderComposition :
    (topologically @IsHomeomorph).IsStableUnderComposition :=
  AlgebraicGeometry.topologically_isStableUnderComposition _ fun _ _ hf hg => hg.comp hf

/-- Being a universal homeomorphism is stable under composition. -/
instance universallyTopologicallyIsHomeomorph_isStableUnderComposition :
    (topologically @IsHomeomorph).universally.IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.universally _

/-- Being a universal homeomorphism contains the identities. -/
instance universallyTopologicallyIsHomeomorph_containsIdentities :
    (topologically @IsHomeomorph).universally.ContainsIdentities where
  id_mem X := by
    intro X' Y' i₁ i₂ f' h
    have : IsIso f' := h.isIso_fst_of_isIso
    exact MorphismProperty.of_isIso (topologically @IsHomeomorph) f'

private theorem universalHomeomorphism_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) : IsAffineHom f := by
  have hhomeo : IsHomeomorph f :=
    hf.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  exact isAffineHom_of_isInducing f hhomeo.isEmbedding.isInducing (by
    rw [Set.range_eq_univ.mpr hhomeo.bijective.2]
    exact isClosed_univ)

private theorem isIso_isInitial_to_iff
    {C : Type u} [Category C] {I : C} (hI : IsInitial I) (Y : C) :
    IsIso (hI.to Y) ↔ Nonempty (IsInitial Y) :=
  ⟨fun _ => ⟨hI.ofIso (asIso (hI.to Y))⟩, fun ⟨hY⟩ => isIso_of_isInitial hI hY _⟩

private theorem isIso_initialMap_iff_target_isInitial
    {X Y : Scheme.{u}} [HasLocallyInitialUniversalHomeomorphismOver X]
    (f : Y ⟶ X) (hf : UniversalHomeomorphism f) :
    IsIso ((initial.to (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver X)).hom.left) ↔
      Nonempty (IsInitial (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver X)) := by
  let Z : UniversalHomeomorphismOver X := ⟨Over.mk f, hf⟩
  calc
    IsIso ((initial.to Z).hom.left) ↔ IsIso ((initial.to Z).hom) :=
      isIso_iff_of_reflects_iso (initial.to Z).hom (Over.forget X)
    _ ↔ IsIso (initial.to Z) := ObjectProperty.isIso_hom_iff (initial.to Z)
    _ ↔ Nonempty (IsInitial Z) := isIso_isInitial_to_iff initialIsInitial Z

/-- An algebra whose `Spec` is isomorphic over `Spec A` to a universal homeomorphism is an
absolute weak normalization candidate. -/
private theorem isAbsoluteWeakNormalizationCandidate_of_iso
    {A : Type u} [CommRing A] (T : UniversalHomeomorphismOver (Spec (.of A))) {c : CommAlgCat A}
    (e : T.obj ≅ (AlgebraicGeometry.algSpec (.of A)).obj (Opposite.op c)) :
    IsAbsoluteWeakNormalizationCandidate A c := by
  change UniversalHomeomorphism ((AlgebraicGeometry.algSpec (.of A)).obj (Opposite.op c)).hom
  rw [← e.inv.w]
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  exact universalHomeomorphism_comp _ _ (universalHomeomorphism_of_isIso e.inv.left) T.property

/-- A universal homeomorphism over an affine `Spec A` is isomorphic over `Spec A` to the `Spec`
of its algebra of global sections. -/
private noncomputable def affineOver_iso_algSpec
    (A : Type u) [CommRing A] (T : UniversalHomeomorphismOver (Spec (.of A))) :
    T.obj ≅ (AlgebraicGeometry.algSpec (.of A)).obj
      (Opposite.op ((AlgebraicGeometry.algΓ (.of A)).obj T.obj).unop) :=
  have : IsAffineHom T.obj.hom := universalHomeomorphism_isAffineHom T.obj.hom T.property
  have hFF : (AlgebraicGeometry.algSpec (.of A)).FullyFaithful :=
    AlgebraicGeometry.algSpec.fullyFaithful
  have := hFF.full
  have := hFF.faithful
  have := (AlgebraicGeometry.algΓAlgSpecAdjunction (.of A)).isIso_unit_app_iff_mem_essImage.2
    (AlgebraicGeometry.essImage_algSpec.2 (isAffine_of_isAffineHom T.obj.hom))
  asIso ((AlgebraicGeometry.algΓAlgSpecAdjunction (.of A)).unit.app T.obj)

private noncomputable def absoluteWeakNormalization_initial_over_affineSpec
    (A : Type u) [CommRing A] :
    IsInitial (⟨(AlgebraicGeometry.algSpec (.of A)).obj
      (Opposite.op (CommAlgCat.of A
        (Algebra.AbsoluteWeakNormalization A))),
      absoluteWeakNormalization_universalHomeomorphism A⟩ :
        UniversalHomeomorphismOver (Spec (.of A))) := by
  let F := AlgebraicGeometry.algSpec (.of A)
  let G := AlgebraicGeometry.algΓ (.of A)
  let awnObj : CommAlgCat A := CommAlgCat.of A (Algebra.AbsoluteWeakNormalization A)
  have hFF : F.FullyFaithful := AlgebraicGeometry.algSpec.fullyFaithful
  refine IsInitial.ofUniqueHom (fun T => ?_) ?_
  · let c : CommAlgCat A := (G.obj T.obj).unop
    let eT : T.obj ≅ F.obj (Opposite.op c) := affineOver_iso_algSpec A T
    have hCand := isAbsoluteWeakNormalizationCandidate_of_iso T eT
    let r := (absoluteWeakNormalizationCategoryObject_isTerminal A).from ⟨c, hCand⟩
    exact ObjectProperty.homMk (F.map (Opposite.op r.hom) ≫ eT.inv)
  · intro T m
    let c : CommAlgCat A := (G.obj T.obj).unop
    let eT : T.obj ≅ F.obj (Opposite.op c) := affineOver_iso_algSpec A T
    have hCand := isAbsoluteWeakNormalizationCandidate_of_iso T eT
    let r := (absoluteWeakNormalizationCategoryObject_isTerminal A).from ⟨c, hCand⟩
    let q : Opposite.op awnObj ⟶ Opposite.op c := hFF.preimage (m.hom ≫ eT.hom)
    have hq : q = Opposite.op r.hom := Quiver.Hom.unop_inj <| congrArg (fun k => k.hom) <|
      (absoluteWeakNormalizationCategoryObject_isTerminal A).hom_ext
        (ObjectProperty.homMk q.unop) r
    have hmap : F.map q = m.hom ≫ eT.hom := hFF.map_preimage _
    apply ObjectProperty.hom_ext
    change m.hom = F.map (Opposite.op r.hom) ≫ eT.inv
    apply (cancel_mono eT.hom).1
    rw [← hmap, hq]
    simp [Category.assoc]
    rfl

private theorem isAbsolutelyWeaklyNormal_iff_isAbsolutelyWeaklyNormalRing_of_affine
    (Y : Scheme.{u}) [IsAffine Y] :
    IsAbsolutelyWeaklyNormal Y ↔
      IsAbsolutelyWeaklyNormalRing Γ(Y, ⊤) := by
  have H := isAbsolutelyWeaklyNormal_tfae Y
  have h12 : IsAbsolutelyWeaklyNormal Y ↔
      (∀ U : Y.affineOpens,
        IsAbsolutelyWeaklyNormalRing Γ(Y, U.val)) := H.out 1 2
  have h31 :
      (∃ (I : Type u) (U : I → Y.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧
          ∀ i, IsAbsolutelyWeaklyNormalRing Γ(Y, (U i).val)) ↔
        IsAbsolutelyWeaklyNormal Y := H.out 3 1
  exact ⟨fun hY => h12.mp hY ⟨⊤, isAffineOpen_top Y⟩,
    fun hR => h31.mp ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top Y⟩, by simp, fun _ => hR⟩⟩

private theorem nonempty_isInitial_iff_isAbsolutelyWeaklyNormal_affineSpec
    (A : Type u) [CommRing A] (Y : Scheme.{u}) [IsAffine Y]
    (f : Y ⟶ Spec (.of A)) (hf : UniversalHomeomorphism f) :
    Nonempty (IsInitial (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver (Spec (.of A)))) ↔
      IsAbsolutelyWeaklyNormal Y := by
  let F := AlgebraicGeometry.algSpec (.of A)
  let awnObj : CommAlgCat A := CommAlgCat.of A (Algebra.AbsoluteWeakNormalization A)
  let W : UniversalHomeomorphismOver (Spec (.of A)) :=
    ⟨F.obj (Opposite.op awnObj), absoluteWeakNormalization_universalHomeomorphism A⟩
  let T : UniversalHomeomorphismOver (Spec (.of A)) := ⟨Over.mk f, hf⟩
  let hW := absoluteWeakNormalization_initial_over_affineSpec A
  let c : CommAlgCat A := ((AlgebraicGeometry.algΓ (.of A)).obj T.obj).unop
  have hFF : F.FullyFaithful := AlgebraicGeometry.algSpec.fullyFaithful
  let eT : T.obj ≅ F.obj (Opposite.op c) := affineOver_iso_algSpec A T
  have hCand := isAbsoluteWeakNormalizationCandidate_of_iso T eT
  let cObj : AbsoluteWeakNormalizationCategory A := ⟨c, hCand⟩
  let r := (absoluteWeakNormalizationCategoryObject_isTerminal A).from cObj
  let q : Opposite.op awnObj ⟶ Opposite.op c := Opposite.op r.hom
  let m : W ⟶ T := ObjectProperty.homMk (F.map (Opposite.op r.hom) ≫ eT.inv)
  calc
    Nonempty (IsInitial T) ↔ IsIso m := by
      rw [← hW.hom_ext (hW.to T) m]
      exact (isIso_isInitial_to_iff hW T).symm
    _ ↔ IsIso m.hom := (ObjectProperty.isIso_hom_iff m).symm
    _ ↔ IsIso m.hom.left :=
      (isIso_iff_of_reflects_iso m.hom (Over.forget (Spec (.of A)))).symm
    _ ↔ IsIso (F.map q ≫ eT.inv) := by
      rw [show m.hom.left = (F.map q ≫ eT.inv).left by simp [m, q]]
      exact isIso_iff_of_reflects_iso (F.map q ≫ eT.inv) (Over.forget (Spec (.of A)))
    _ ↔ IsIso (F.map q) := by
      have : IsIso eT.inv.left := (Over.forget _).map_isIso eT.inv
      exact isIso_comp_right_iff _ _
    _ ↔ IsIso q := ⟨fun _ => hFF.isIso_of_isIso_map q, fun _ => Functor.map_isIso F q⟩
    _ ↔ IsIso r.hom := isIso_op_iff r.hom
    _ ↔ IsIso r := ObjectProperty.isIso_hom_iff r
    _ ↔ IsAbsolutelyWeaklyNormalRing (c : Type u) := by
      exact
        isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
          A (c : Type u) hCand
    _ ↔ IsAbsolutelyWeaklyNormal Y :=
      (isAbsolutelyWeaklyNormal_iff_isAbsolutelyWeaklyNormalRing_of_affine Y).symm

private theorem isIso_isInitialMap_iff_isAbsolutelyWeaklyNormal_affineSpec
    (A : Type u) [CommRing A] (I : UniversalHomeomorphismOver (Spec (.of A)))
    (hI : IsInitial I) (Y : Scheme.{u}) [IsAffine Y]
    (f : Y ⟶ Spec (.of A)) (hf : UniversalHomeomorphism f) :
    IsIso ((hI.to (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver (Spec (.of A)))).hom.left) ↔
      IsAbsolutelyWeaklyNormal Y := by
  let T : UniversalHomeomorphismOver (Spec (.of A)) := ⟨Over.mk f, hf⟩
  calc
    IsIso ((hI.to T).hom.left) ↔ IsIso (hI.to T).hom :=
      isIso_iff_of_reflects_iso (hI.to T).hom (Over.forget (Spec (.of A)))
    _ ↔ IsIso (hI.to T) := ObjectProperty.isIso_hom_iff (hI.to T)
    _ ↔ Nonempty (IsInitial T) := isIso_isInitial_to_iff hI T
    _ ↔ IsAbsolutelyWeaklyNormal Y :=
      nonempty_isInitial_iff_isAbsolutelyWeaklyNormal_affineSpec A Y f hf

private theorem isIso_initialMap_iff_isAbsolutelyWeaklyNormal_affineBase
    (B : Scheme.{u}) [IsAffine B]
    (I : UniversalHomeomorphismOver B) (hI : IsInitial I)
    (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ B)
    (hf : UniversalHomeomorphism f) :
    IsIso ((hI.to (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver B)).hom.left) ↔
      IsAbsolutelyWeaklyNormal Y := by
  let e := B.isoSpec
  let A := Γ(B, ⊤)
  let I' : UniversalHomeomorphismOver (Spec (.of A)) :=
    ⟨Over.mk (I.obj.hom ≫ e.hom),
      universalHomeomorphism_comp _ _ I.property (universalHomeomorphism_of_isIso _)⟩
  let T : UniversalHomeomorphismOver B := ⟨Over.mk f, hf⟩
  let T' : UniversalHomeomorphismOver (Spec (.of A)) :=
    ⟨Over.mk (f ≫ e.hom),
      universalHomeomorphism_comp _ _ hf (universalHomeomorphism_of_isIso _)⟩
  have hI' : IsInitial I' := by
    refine IsInitial.ofUniqueHom (fun V => ?_) ?_
    · let V₀ : UniversalHomeomorphismOver B :=
        ⟨Over.mk (V.obj.hom ≫ e.inv),
          universalHomeomorphism_comp _ _ V.property (universalHomeomorphism_of_isIso _)⟩
      let k := hI.to V₀
      exact ObjectProperty.homMk (Over.homMk k.hom.left (by
        calc
          k.hom.left ≫ V.obj.hom =
              (k.hom.left ≫ (V.obj.hom ≫ e.inv)) ≫ e.hom := by simp [Category.assoc]
          _ = I.obj.hom ≫ e.hom := congrArg (fun q => q ≫ e.hom) k.hom.w))
    · intro V m
      let V₀ : UniversalHomeomorphismOver B :=
        ⟨Over.mk (V.obj.hom ≫ e.inv),
          universalHomeomorphism_comp _ _ V.property (universalHomeomorphism_of_isIso _)⟩
      let m₀ : I ⟶ V₀ := ObjectProperty.homMk (Over.homMk m.hom.left (by
        calc
          m.hom.left ≫ (V.obj.hom ≫ e.inv) =
              (m.hom.left ≫ V.obj.hom) ≫ e.inv := by simp
          _ = (I.obj.hom ≫ e.hom) ≫ e.inv :=
            congrArg (fun q => q ≫ e.inv) m.hom.w
          _ = I.obj.hom := by simp [Category.assoc]))
      exact ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <|
        (congrArg (fun q => q.hom.left) (hI.hom_ext (hI.to V₀) m₀)).symm
  let m : I' ⟶ T' := ObjectProperty.homMk (Over.homMk (hI.to T).hom.left (by
    calc
      (hI.to T).hom.left ≫ T'.obj.hom =
          ((hI.to T).hom.left ≫ T.obj.hom) ≫ e.hom := by
            change (hI.to T).hom.left ≫ (T.obj.hom ≫ e.hom) = _
            exact (Category.assoc _ _ _).symm
      _ = I.obj.hom ≫ e.hom := congrArg (fun q => q ≫ e.hom) (hI.to T).hom.w))
  calc
    IsIso ((hI.to T).hom.left) ↔ IsIso ((hI'.to T').hom.left) := by
      rw [hI'.hom_ext (hI'.to T') m]
      simp [m]
    _ ↔ IsAbsolutelyWeaklyNormal Y :=
      isIso_isInitialMap_iff_isAbsolutelyWeaklyNormal_affineSpec A I' hI' Y
        (f ≫ e.hom) T'.property

private theorem isAbsolutelyWeaklyNormalRing_iff_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsAbsolutelyWeaklyNormalRing A ↔
      IsAbsolutelyWeaklyNormalRing B := by
  have aux {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
      (hR : IsAbsolutelyWeaklyNormalRing R) :
      IsAbsolutelyWeaklyNormalRing S := by
    let : Algebra R S := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=
      IsLocalization.away_of_isUnit_of_bijective (R := R) (S := S) isUnit_one e.bijective
    exact isAbsolutelyWeaklyNormalRing_propertyIsLocal
      |>.localizationAwayPreserves (f := 1) S hR
  exact ⟨aux e, aux e.symm⟩

private theorem isAbsolutelyWeaklyNormal_iff_of_affineIso
    {A B : Scheme.{u}} [IsAffine A] [IsAffine B] (e : A ≅ B) :
    IsAbsolutelyWeaklyNormal A ↔
      IsAbsolutelyWeaklyNormal B := by
  rw [isAbsolutelyWeaklyNormal_iff_isAbsolutelyWeaklyNormalRing_of_affine A,
    isAbsolutelyWeaklyNormal_iff_isAbsolutelyWeaklyNormalRing_of_affine B]
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  exact isAbsolutelyWeaklyNormalRing_iff_of_ringEquiv
    (asIso e.hom.appTop).commRingCatIsoToRingEquiv.symm

private theorem isIso_initialMap_iff_isAbsolutelyWeaklyNormal_main
    {X Y : Scheme.{u}} [HasLocallyInitialUniversalHomeomorphismOver X]
    (f : Y ⟶ X) (hf : UniversalHomeomorphism f) :
    IsIso ((initial.to (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver X)).hom.left) ↔
      IsAbsolutelyWeaklyNormal Y := by
  let T : UniversalHomeomorphismOver X := ⟨Over.mk f, hf⟩
  let P : UniversalHomeomorphismOver X := initial (UniversalHomeomorphismOver X)
  let g : P.obj.left ⟶ Y := (initial.to T).hom.left
  have hfac : g ≫ f = P.obj.hom := (initial.to T).hom.w
  let : IsAffineHom f := universalHomeomorphism_isAffineHom f hf
  let 𝒰 := X.affineCover
  let 𝒱 := 𝒰.pullback₁ f
  have hGlobal : IsIso g ↔ ∀ i, IsIso (pullback.snd g (𝒱.f i)) :=
    (MorphismProperty.isomorphisms Scheme).iff_of_zeroHypercover_target 𝒱
  have hAff : ∀ i, IsAffine (𝒱.X i) := fun i => by
    let hPull := CategoryTheory.Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover f 𝒰
    let hIdx := congrArg CategoryTheory.PreZeroHypercover.I₀ hPull
    let j : 𝒰.I₀ := cast
      (CategoryTheory.PreZeroHypercover.pullback₁_I₀ f 𝒰.toPreZeroHypercover) (cast hIdx i)
    have : IsAffine (𝒰.X j) := inferInstanceAs (IsAffine (Spec _))
    change IsAffine (pullback f (𝒰.f j))
    infer_instance
  have hAWNCover : IsAbsolutelyWeaklyNormal Y ↔
      ∀ i, IsAbsolutelyWeaklyNormal (𝒱.X i) := by
    have H := isAbsolutelyWeaklyNormal_tfae Y
    have h14 : IsAbsolutelyWeaklyNormal Y ↔
        (∃ (I : Type u) (U : I → Y.Opens),
          (⨆ i, U i) = ⊤ ∧
            ∀ i, IsAbsolutelyWeaklyNormal (U i).toScheme) := H.out 1 4
    constructor
    · intro hY i
      have := hAff i
      have : IsAffine ((𝒱.f i).opensRange.toScheme) := isAffineOpen_opensRange (𝒱.f i)
      exact (isAbsolutelyWeaklyNormal_iff_of_affineIso (𝒱.f i).isoOpensRange).2
        (isAbsolutelyWeaklyNormal_open hY (𝒱.f i).opensRange)
    · intro hCover
      apply h14.mpr
      let 𝒱' : Y.OpenCover := 𝒱
      refine ⟨𝒱.I₀, fun i => (𝒱.f i).opensRange, 𝒱'.iSup_opensRange, ?_⟩
      intro i
      have := hAff i
      have : IsAffine ((𝒱.f i).opensRange.toScheme) := isAffineOpen_opensRange (𝒱.f i)
      exact (isAbsolutelyWeaklyNormal_iff_of_affineIso (𝒱.f i).isoOpensRange).mp (hCover i)
  have hLocal : ∀ i, IsIso (pullback.snd g (𝒱.f i)) ↔
      IsAbsolutelyWeaklyNormal (𝒱.X i) := by
    intro i
    let hPull := CategoryTheory.Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover
      f 𝒰
    let hIdx := congrArg CategoryTheory.PreZeroHypercover.I₀ hPull
    cases hIdx
    let j : 𝒰.I₀ := cast
      (CategoryTheory.PreZeroHypercover.pullback₁_I₀ f 𝒰.toPreZeroHypercover) i
    let U := 𝒰.f j
    let : IsOpenImmersion U := 𝒰.map_prop j
    let : IsAffine (𝒰.X j) := inferInstanceAs (IsAffine (Spec _))
    let : HasPullback U P.obj.hom := inferInstance
    let : HasPullback U T.obj.hom := inferInstance
    let I : UniversalHomeomorphismOver (𝒰.X j) :=
      UniversalHomeomorphismOver.pullback U P
    let hI : IsInitial I := isInitial_pullback_initial U
    let T' : UniversalHomeomorphismOver (𝒰.X j) :=
      UniversalHomeomorphismOver.pullback U T
    let eI : I.obj.left ≅ pullback U P.obj.hom := pullback.congrHom rfl rfl
    let eT : T'.obj.left ≅ pullback U T.obj.hom := pullback.congrHom rfl rfl
    have hObj : 𝒱.X i = pullback f U := by
      change pullback f (𝒰.f i) = pullback f U
      congr 1
    let mBase : pullback U P.obj.hom ⟶ pullback U T.obj.hom :=
      pullback.lift (pullback.fst U P.obj.hom)
        (pullback.snd U P.obj.hom ≫ g) (by
          calc
            pullback.fst U P.obj.hom ≫ U = pullback.snd U P.obj.hom ≫ P.obj.hom :=
              pullback.condition
            _ = pullback.snd U P.obj.hom ≫ (g ≫ f) := by rw [hfac]
            _ = (pullback.snd U P.obj.hom ≫ g) ≫ T.obj.hom := by
              simp [T])
    let m : I.obj.left ⟶ T'.obj.left := eI.hom ≫ mBase ≫ eT.inv
    have hmBase : m ≫ T'.obj.hom = I.obj.hom := by
      simp [m, mBase, eI, eT, I, T', UniversalHomeomorphismOver.pullback,
        pullback.congrHom_hom]
    let mOver : I.obj ⟶ T'.obj := Over.homMk m hmBase
    let mArrow := ObjectProperty.homMk mOver
    have hmEq : (hI.to T').hom.left = m := by
      have hh := hI.hom_ext (hI.to T') mArrow
      exact congrArg (fun q => q.hom.left) hh
    have hAffine : IsAffine T'.obj.left := by
      change IsAffine (pullback U f)
      infer_instance
    have hChar : IsIso m ↔
        IsAbsolutelyWeaklyNormal T'.obj.left := by
      rw [← hmEq]
      exact isIso_initialMap_iff_isAbsolutelyWeaklyNormal_affineBase
        (𝒰.X j) I hI T'.obj.left T'.obj.hom T'.property
    let eObj : 𝒱.X i ≅ pullback f U := eqToIso hObj
    let eCod : 𝒱.X i ≅ pullback U f := eObj ≪≫ (pullbackSymmetry U f).symm
    let : IsAffine (𝒱.X i) := hAff i
    have hV : 𝒱.f i = eCod.hom ≫ pullback.snd U f := by
      have hV₀ : 𝒱.f i = pullback.fst f U := by
        change pullback.fst f (𝒰.f i) = pullback.fst f U
        congr 1
      have hObjIso : eObj = Iso.refl _ := by
        cases hObj
        rfl
      rw [hV₀]
      have hSym : pullback.fst f U =
          (pullbackSymmetry U f).inv ≫ pullback.snd U f :=
        (pullbackSymmetry_inv_comp_snd U f).symm
      have hCod : eCod.hom ≫ pullback.snd U f =
          (pullbackSymmetry U f).inv ≫ pullback.snd U f := by
        change (eObj ≪≫ (pullbackSymmetry U f).symm).hom ≫
          pullback.snd U f = _
        rw [hObjIso]
        change (pullbackSymmetry U f).inv ≫ pullback.snd U f = _
        rfl
      rw [hSym]
      exact hCod.symm
    let : IsIso eCod.hom := inferInstance
    let eMapHom := pullback.map g (𝒱.f i) g (pullback.snd U f)
      (𝟙 _) eCod.hom (𝟙 _) (by simp) hV
    have hIsoMap : IsIso eMapHom :=
      pullback.map_isIso g (𝒱.f i) g (pullback.snd U f) (𝟙 _) eCod.hom (𝟙 _) (by simp) hV
    let eMap : pullback g (𝒱.f i) ≅ pullback g (pullback.snd U f) := asIso eMapHom
    let eDomPB : pullback g (𝒱.f i) ≅ pullback U P.obj.hom :=
      eMap ≪≫ pullbackSymmetry g (pullback.snd U f) ≪≫
        pullbackLeftPullbackSndIso U f g ≪≫ pullback.congrHom rfl hfac
    let eDom : pullback g (𝒱.f i) ≅ I.obj.left := eDomPB ≪≫ eI.symm
    have hCongFst : (pullback.congrHom rfl hfac).hom ≫ pullback.fst U P.obj.hom =
        pullback.fst U (g ≫ f) :=
      pullback.lift_fst _ _ _
    have hCongSnd : (pullback.congrHom rfl hfac).hom ≫ pullback.snd U P.obj.hom =
        pullback.snd U (g ≫ f) :=
      pullback.lift_snd _ _ _
    have hMapFst : eMap.hom ≫ pullback.fst g (pullback.snd U f) =
        pullback.fst g (𝒱.f i) := by
      simp [eMap, eMapHom, pullback.map]
    have hMapSnd : eMap.hom ≫ pullback.snd g (pullback.snd U f) =
        pullback.snd g (𝒱.f i) ≫ eCod.hom := by
      simp [eMap, eMapHom, pullback.map]
    have hDomFstPB : eDomPB.hom ≫ pullback.fst U P.obj.hom =
        pullback.snd g (𝒱.f i) ≫ eCod.hom ≫ pullback.fst U f := by
      calc
        eDomPB.hom ≫ pullback.fst U P.obj.hom =
            eMap.hom ≫ (pullbackSymmetry g (pullback.snd U f)).hom ≫
              (pullbackLeftPullbackSndIso U f g).hom ≫ pullback.fst U (g ≫ f) := by
                dsimp [eDomPB]
                simp only [Category.assoc]
                rw [hCongFst]
        _ = pullback.snd g (𝒱.f i) ≫ eCod.hom ≫ pullback.fst U f := by
          simp only [pullbackLeftPullbackSndIso_hom_fst, pullbackSymmetry_hom_comp_fst_assoc,
            reassoc_of% hMapSnd]
    have hDomSndPB : eDomPB.hom ≫ pullback.snd U P.obj.hom =
        pullback.fst g (𝒱.f i) := by
      calc
        eDomPB.hom ≫ pullback.snd U P.obj.hom =
            eMap.hom ≫ (pullbackSymmetry g (pullback.snd U f)).hom ≫
              (pullbackLeftPullbackSndIso U f g).hom ≫ pullback.snd U (g ≫ f) := by
                dsimp [eDomPB]
                simp only [Category.assoc]
                rw [hCongSnd]
        _ = pullback.fst g (𝒱.f i) := by
          simp only [pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd, hMapFst]
    have hePB : eDomPB.hom ≫ mBase = pullback.snd g (𝒱.f i) ≫ eCod.hom := by
      apply pullback.hom_ext
      · calc
          (eDomPB.hom ≫ mBase) ≫ pullback.fst U T.obj.hom =
              eDomPB.hom ≫ pullback.fst U P.obj.hom := by
                simp only [Category.assoc, mBase, pullback.lift_fst]
          _ = pullback.snd g (𝒱.f i) ≫ eCod.hom ≫ pullback.fst U T.obj.hom := by
            simpa [T] using hDomFstPB
      · calc
          (eDomPB.hom ≫ mBase) ≫ pullback.snd U T.obj.hom =
              eDomPB.hom ≫ pullback.snd U P.obj.hom ≫ g := by
                simp only [Category.assoc, mBase, pullback.lift_snd]
          _ = pullback.fst g (𝒱.f i) ≫ g := by rw [reassoc_of% hDomSndPB]
          _ = pullback.snd g (𝒱.f i) ≫ (𝒱.f i) := pullback.condition
          _ = pullback.snd g (𝒱.f i) ≫ eCod.hom ≫ pullback.snd U T.obj.hom := by
            rw [hV]
            simp [T]
    let eCodT : 𝒱.X i ≅ T'.obj.left := eCod ≪≫ eT.symm
    have he : eDom.hom ≫ m = pullback.snd g (𝒱.f i) ≫ eCodT.hom := by
      apply (cancel_mono eT.hom).1
      calc
        (eDom.hom ≫ m) ≫ eT.hom =
            (eDomPB.hom ≫ mBase) ≫ eT.inv ≫ eT.hom := by
              simp [eDom, m, Category.assoc]
        _ = (pullback.snd g (𝒱.f i) ≫ eCod.hom) ≫ eT.inv ≫ eT.hom := by
          rw [hePB]
        _ = (pullback.snd g (𝒱.f i) ≫ eCodT.hom) ≫ eT.hom := by
          simp [eCodT, Category.assoc]
    exact (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme)
      (Arrow.isoMk eDom eCodT he)).trans
        (hChar.trans (isAbsolutelyWeaklyNormal_iff_of_affineIso eCod).symm)
  exact hGlobal.trans ((forall_congr' hLocal).trans hAWNCover.symm)

/-- **Stacks Project, Tag 0EUS.** The canonical map from the absolute weak
normalization of `X` to a universal homeomorphism `Y ⟶ X` is an isomorphism
if and only if `Y` is absolutely weakly normal. -/
@[stacks 0EUS "absolute_weak_normalization_iso_iff"]
public theorem isIso_initialMap_iff_isAbsolutelyWeaklyNormal
    {X Y : Scheme.{u}} [HasLocallyInitialUniversalHomeomorphismOver X]
    (f : Y ⟶ X) (hf : UniversalHomeomorphism f) :
    IsIso ((initial.to (⟨Over.mk f, hf⟩ : UniversalHomeomorphismOver X)).hom.left) ↔
      IsAbsolutelyWeaklyNormal Y :=
  isIso_initialMap_iff_isAbsolutelyWeaklyNormal_main f hf

end AlgebraicGeometry

end
