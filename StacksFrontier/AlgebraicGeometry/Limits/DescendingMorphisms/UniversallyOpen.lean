module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UniversallyOpenLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.UniversallyOpenFinite

/-!
# Descending local quasi-finiteness together with universal openness

Let `S` be the limit of a cofiltered inverse system of schemes `S i` with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of schemes over one stage `S i₀` with `S i₀`, `X₀`
and `Y₀` quasi-compact and quasi-separated, and let `f i` and `f` be the base changes of `f₀` to
`S i` and to `S`. If `f₀` is locally of finite presentation and `f` is locally quasi-finite and
universally open, then `f i` is locally quasi-finite and universally open for some `i`.

## Main results

* `AlgebraicGeometry.exists_universallyOpen_baseChange_of_locallyQuasiFinite`: universal openness
  of a locally quasi-finite, locally finitely presented morphism with quasi-compact source
  descends from the limit to a stage.
* `AlgebraicGeometry.exists_locallyQuasiFinite_universallyOpen_baseChange_of_limitBaseChange`:
  local quasi-finiteness and universal openness descend together.

## Implementation notes

A scheme over a stage is an object of `CategoryTheory.Over`, and base change is
`CategoryTheory.Over.pullback`. Both conclusions hold at the same stage, so they appear in a single
existential, and local quasi-finiteness is stated as local finite type together with Mathlib's
`LocallyQuasiFinite`.

## References

* [Stacks Project, Tag 0F33](https://stacks.math.columbia.edu/tag/0F33)
* [Stacks Project, Tag 0F34](https://stacks.math.columbia.edu/tag/0F34)
* [Stacks Project, Tag 094M](https://stacks.math.columbia.edu/tag/094M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Topology

universe u

namespace AlgebraicGeometry


private lemma polynomial_isPushout {R S : Type u} [CommRing R] [CommRing S]
    (hom : R →+* S) (count : ℕ) :
    IsPushout (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin count) R))
      (CommRingCat.ofHom hom)
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) hom))
      (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial (Fin count) S)) := by
  let : Algebra R S := hom.toAlgebra
  let : Algebra (MvPolynomial (Fin count) R) (MvPolynomial (Fin count) S) :=
    MvPolynomial.algebraMvPolynomial
  exact CommRingCat.isPushout_of_isPushout R (MvPolynomial (Fin count) R)
    S (MvPolynomial (Fin count) S)

private noncomputable def polynomialDiagram {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (count : ℕ) : I ⥤ Scheme.{u} where
  obj index := Spec (.of (MvPolynomial (Fin count) Γ(D.obj index, ⊤)))
  map arrow := Spec.map (CommRingCat.ofHom (MvPolynomial.map (D.map arrow).appTop.hom))
  map_id index := by
    simp only [D.map_id, Scheme.Hom.id_appTop, CommRingCat.hom_id]
    rw [← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext MvPolynomial.map_id
  map_comp first second := by
    simp only [D.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun polynomial => (MvPolynomial.map_map _ _ polynomial).symm

private noncomputable def polynomialCone {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (count : ℕ) : Cone (polynomialDiagram D count) where
  pt := Spec (.of (MvPolynomial (Fin count) Γ(c.pt, ⊤)))
  π.app index := Spec.map (CommRingCat.ofHom (MvPolynomial.map (c.π.app index).appTop.hom))
  π.naturality first second arrow := by
    dsimp [polynomialDiagram]
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hmaps : (c.π.app first).appTop.hom.comp (D.map arrow).appTop.hom =
        (c.π.app second).appTop.hom := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, c.w]
    congr 2
    apply RingHom.ext
    intro polynomial
    change MvPolynomial.map _ polynomial = MvPolynomial.map _ (MvPolynomial.map _ polynomial)
    rw [MvPolynomial.map_map, hmaps]

private lemma polynomial_specMap_isPullback {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (hom : X ⟶ Y) (count : ℕ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) hom.appTop.hom)))
      (Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ X.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ Y.isoSpec.inv) hom :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (polynomial_isPushout hom.appTop.hom count)).paste_vert
    (IsPullback.of_vert_isIso ⟨Scheme.isoSpec_inv_naturality hom⟩)

private lemma polynomialCone_isPullback {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (count : ℕ)
    [∀ index, IsAffine (D.obj index)] [IsAffine c.pt] (index : I) :
    IsPullback ((polynomialCone D c count).π.app index)
      (Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ c.pt.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ (D.obj index).isoSpec.inv)
      (c.π.app index) := by
  have : IsAffine (((Functor.const I).obj c.pt).obj index) := ‹IsAffine c.pt›
  exact polynomial_specMap_isPullback (c.π.app index) count

private noncomputable def polynomialCone_isLimit
    {I : Type u} [Category.{u} I] [IsConnected I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (count : ℕ)
    [∀ index, IsAffine (D.obj index)] [IsAffine c.pt] :
    IsLimit (polynomialCone D c count) := by
  let transformation : polynomialDiagram D count ⟶ D :=
    { app := fun index => Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
        (D.obj index).isoSpec.inv
      naturality := by
        intro first second arrow
        dsimp [polynomialDiagram]
        rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, MvPolynomial.map_comp_C,
          CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
        simp [Scheme.isoSpec_inv_naturality] }
  apply isLimitOfIsPullbackOfIsConnected transformation _ _
    (show (Cone.postcompose transformation).obj (polynomialCone D c count) ⟶ c from
      { hom := Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ c.pt.isoSpec.inv
        w := by
          intro index
          exact (polynomialCone_isPullback D c count index).w.symm }) _ hc
  exact polynomialCone_isPullback D c count

private lemma polynomialMap_isPushout
    {R A B C : CommRingCat.{u}} {first : R ⟶ A} {second : R ⟶ B}
    {left : A ⟶ C} {right : B ⟶ C}
    (square : IsPushout first second left right) (count : ℕ) :
    IsPushout (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) first.hom))
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) second.hom))
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) left.hom))
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) right.hom)) := by
  have hcomm :
      CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) first.hom) ≫
        CommRingCat.ofHom (MvPolynomial.map left.hom) =
      CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) second.hom) ≫
        CommRingCat.ofHom (MvPolynomial.map right.hom) := by
    ext1
    exact RingHom.ext fun polynomial => by
      simp [MvPolynomial.map_map, ← CommRingCat.hom_comp, square.w]
  let coefficientLeft := fun cocone : PushoutCocone
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) first.hom))
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) second.hom)) =>
    CommRingCat.ofHom (cocone.inl.hom.comp MvPolynomial.C)
  let coefficientRight := fun cocone : PushoutCocone
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) first.hom))
      (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) second.hom)) =>
    CommRingCat.ofHom (cocone.inr.hom.comp MvPolynomial.C)
  have hcoeff cocone : first ≫ coefficientLeft cocone = second ≫ coefficientRight cocone := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro element
    simpa [coefficientLeft, coefficientRight] using
      congrArg (fun hom => hom.hom (MvPolynomial.C element)) cocone.condition
  let descend := fun cocone => CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (square.desc (coefficientLeft cocone) (coefficientRight cocone) (hcoeff cocone)).hom
    (fun index => cocone.inl.hom (MvPolynomial.X index)))
  apply IsPushout.of_isColimit' ⟨hcomm⟩
  apply PushoutCocone.IsColimit.mk hcomm descend
  · intro cocone
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro element
      simpa only [descend, coefficientLeft, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C] using
        congrArg (fun hom => hom.hom element)
        (square.inl_desc (coefficientLeft cocone) (coefficientRight cocone) (hcoeff cocone))
    · intro index
      simp [descend]
  · intro cocone
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro element
      simpa only [descend, coefficientRight, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C] using
        congrArg (fun hom => hom.hom element)
        (square.inr_desc (coefficientLeft cocone) (coefficientRight cocone) (hcoeff cocone))
    · intro index
      simpa [descend] using
        congrArg (fun hom => hom.hom (MvPolynomial.X index)) cocone.condition
  · intro cocone hom hleft hright
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro element
      have hcoeffeq : CommRingCat.ofHom (hom.hom.comp MvPolynomial.C) =
          square.desc (coefficientLeft cocone) (coefficientRight cocone) (hcoeff cocone) := by
        apply square.hom_ext
        · apply CommRingCat.hom_ext
          apply RingHom.ext
          intro element
          simpa [coefficientLeft] using
            congrArg (fun hom => hom.hom (MvPolynomial.C element)) hleft
        · apply CommRingCat.hom_ext
          apply RingHom.ext
          intro element
          simpa [coefficientRight] using
            congrArg (fun hom => hom.hom (MvPolynomial.C element)) hright
      simpa [descend] using congrArg (fun hom => hom.hom element) hcoeffeq
    · intro index
      simpa [descend] using congrArg (fun hom => hom.hom (MvPolynomial.X index)) hleft
private lemma span_algebraMap_eq_top_of_isPushout
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R A B C]
    (count : ℕ) (generators : Fin count → B)
    (hgenerators : Submodule.span R (Set.range generators) = ⊤) :
    Submodule.span A (Set.range fun index => algebraMap B C (generators index)) = ⊤ := by
  classical
  apply top_unique
  intro element _
  apply (Algebra.IsPushout.out (R := R) (S := A) (R' := B) (S' := C)).inductionOn
    element (motive := fun element => element ∈ Submodule.span A
      (Set.range fun index => algebraMap B C (generators index)))
  · intro element
    have helement : element ∈ Submodule.span R (Set.range generators) := by
      rw [hgenerators]
      exact Submodule.mem_top
    induction helement using Submodule.span_induction with
    | mem element helement =>
      obtain ⟨index, rfl⟩ := helement
      exact Submodule.subset_span ⟨index, rfl⟩
    | zero =>
      simp
    | add first second hfirst hsecond hfirst' hsecond' =>
      simpa using Submodule.add_mem _ hfirst' hsecond'
    | smul scalar element helement helement' =>
      simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R A C,
        ← IsScalarTower.algebraMap_apply R B C] using
        Submodule.smul_mem (Submodule.span A
          (Set.range fun index => algebraMap B C (generators index)))
          (algebraMap R A scalar) helement'
  · intro scalar element helement
    exact Submodule.smul_mem _ scalar helement
  · intro first second hfirst hsecond
    exact Submodule.add_mem _ hfirst hsecond

private lemma exists_empty_preimage_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) [CompactSpace (D.obj i)]
    (E : Set (D.obj i)) (hE : IsConstructible E)
    (hempty : c.π.app i ⁻¹' E = ∅) :
    ∃ (j : I) (g : j ⟶ i), D.map g ⁻¹' E = ∅ := by
  classical
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun U hU V hV => ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV => ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    have hle : c.π.app i ⁻¹ᵁ (⟨U, hU.1⟩ : (D.obj i).Opens) ≤
        c.π.app i ⁻¹ᵁ (⟨V, hV.1⟩ : (D.obj i).Opens) := by
      show c.π.app i ⁻¹' U ⊆ c.π.app i ⁻¹' V
      rwa [← Set.sdiff_eq_empty, ← Set.preimage_sdiff]
    obtain ⟨j, g, hg⟩ := exists_map_preimage_le_map_preimage D c hc hU.2.isCompact hle
    exact ⟨j, g, by rwa [Set.preimage_sdiff, Set.sdiff_eq_empty]⟩
  | sup U hU V hV hU' hV' =>
    have hUV : c.π.app i ⁻¹' U ∪ c.π.app i ⁻¹' V = ∅ := by
      simpa only [Set.sup_eq_union, Set.preimage_union] using hempty
    obtain ⟨j, gj, hj⟩ := hU' (Set.eq_empty_of_subset_empty
      (hUV ▸ Set.subset_union_left))
    obtain ⟨k, gk, hk⟩ := hV' (Set.eq_empty_of_subset_empty
      (hUV ▸ Set.subset_union_right))
    obtain ⟨m, mj, mk, hm⟩ := IsCofiltered.cospan gj gk
    refine ⟨m, mj ≫ gj, ?_⟩
    show D.map (mj ≫ gj) ⁻¹' (U ∪ V) = ∅
    rw [Set.preimage_union]
    have hj' : D.map (mj ≫ gj) ⁻¹' U = ∅ := by
      rw [D.map_comp]
      show D.map mj ⁻¹' (D.map gj ⁻¹' U) = ∅
      rw [hj, Set.preimage_empty]
    have hk' : D.map (mj ≫ gj) ⁻¹' V = ∅ := by
      rw [hm, D.map_comp]
      show D.map mk ⁻¹' (D.map gk ⁻¹' V) = ∅
      rw [hk, Set.preimage_empty]
    rw [hj', hk', Set.union_empty]

private lemma exists_isOpen_preimage_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (E : Set (D.obj i)) (hE : IsConstructible E)
    (hopen : IsOpen (c.π.app i ⁻¹' E))
    (hcompact : IsCompact (c.π.app i ⁻¹' E)) :
    ∃ (j : I) (g : j ⟶ i), IsOpen (D.map g ⁻¹' E) := by
  classical
  obtain ⟨j, V, hV, heq⟩ := exists_preimage_eq D c hc
    (⟨c.π.app i ⁻¹' E, hopen⟩ : c.pt.Opens) hcompact
  let k := IsCofiltered.min i j
  let ki := IsCofiltered.minToLeft i j
  let kj := IsCofiltered.minToRight i j
  let E' : Set (D.obj k) := D.map ki ⁻¹' E
  let V' : (D.obj k).Opens := D.map kj ⁻¹ᵁ V
  have : CompactSpace (D.obj k) :=
    QuasiCompact.compactSpace_of_compactSpace (D.map ki)
  have : QuasiSeparatedSpace (D.obj k) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map ki)
  have hV' : IsCompact (V' : Set (D.obj k)) :=
    QuasiCompact.isCompact_preimage (f := D.map kj) V V.isOpen hV
  have hE' : IsConstructible E' := (D.map ki).isConstructible_preimage hE
  have hsym : IsConstructible ((E' \ V') ∪ ((V' : Set (D.obj k)) \ E')) :=
    (hE'.sdiff (hV'.isConstructible V'.isOpen)).union
      ((hV'.isConstructible V'.isOpen).sdiff hE')
  have heq' : c.π.app k ⁻¹' E' = c.π.app k ⁻¹' (V' : Set (D.obj k)) := by
    have hleft : c.π.app k ⁻¹' E' = c.π.app i ⁻¹' E := by
      show (c.π.app k ≫ D.map ki) ⁻¹' E = _
      rw [c.w]
    have hright : c.π.app k ⁻¹' (V' : Set (D.obj k)) = c.π.app j ⁻¹' (V : Set (D.obj j)) := by
      show (c.π.app k ≫ D.map kj) ⁻¹' (V : Set (D.obj j)) = _
      rw [c.w]
    rw [hleft, hright]
    exact congrArg (fun W : c.pt.Opens => (W : Set c.pt)) heq.symm
  have hempty : c.π.app k ⁻¹' ((E' \ V') ∪ ((V' : Set (D.obj k)) \ E')) = ∅ := by
    rw [Set.preimage_union, Set.preimage_sdiff, Set.preimage_sdiff, heq']
    simp
  obtain ⟨m, mk, hm⟩ := exists_empty_preimage_of_isConstructible D c hc k _ hsym hempty
  have heqstage : D.map mk ⁻¹' E' = D.map mk ⁻¹' (V' : Set (D.obj k)) := by
    rw [Set.preimage_union, Set.preimage_sdiff, Set.preimage_sdiff] at hm
    exact Set.Subset.antisymm
      (Set.sdiff_eq_empty.mp (Set.eq_empty_of_subset_empty (hm ▸ Set.subset_union_left)))
      (Set.sdiff_eq_empty.mp (Set.eq_empty_of_subset_empty (hm ▸ Set.subset_union_right)))
  refine ⟨m, mk ≫ ki, ?_⟩
  rw [D.map_comp]
  show IsOpen (D.map mk ⁻¹' E')
  rw [heqstage]
  exact V'.isOpen.preimage (D.map mk).continuous

private lemma universallyOpen_of_etale_local_cover
    {ι : Type u} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : ι → Scheme.{u}) (a : ∀ i, U i ⟶ X) (b : ∀ i, V i ⟶ Y)
    (q : ∀ i, U i ⟶ V i)
    (ha : ∀ i, Etale (a i)) (hb : ∀ i, Etale (b i))
    (hsq : ∀ i, q i ≫ b i = a i ≫ f)
    (hq : ∀ i, UniversallyOpen (q i))
    (hcover : ∀ x : X, ∃ (i : ι) (u : U i), a i u = x) :
    UniversallyOpen f := by
  apply (UniversallyOpen.isEtaleLocalOnSourceAndTarget
    ).iff_forall_exists_etale_neighborhood f |>.2
  intro x
  obtain ⟨i, u, hu⟩ := hcover x
  exact ⟨U i, V i, a i, b i, q i, u, ha i, hb i, hu, hsq i, hq i⟩

private lemma universallyOpen_of_pullback_stage
    {I : Type u} [Category.{u} I] {S : I ⥤ Scheme.{u}}
    (c : Cone S) (i₀ : I) (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    {i : I} (g : i ⟶ i₀)
    [UniversallyOpen ((Over.pullback (c.π.app i₀)).map f₀).left] :
    UniversallyOpen
      ((Over.pullback (c.π.app i)).map ((Over.pullback (S.map g)).map f₀)).left := by
  refine (overPullback_map_comp_iff (@UniversallyOpen) (S.map g) (c.π.app i) f₀).mp ?_
  rw [c.w g]
  infer_instance

private lemma universallyOpen_specMap_appTop_iff {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (hom : X ⟶ Y) :
    UniversallyOpen (Spec.map hom.appTop) ↔ UniversallyOpen hom :=
  MorphismProperty.arrow_mk_iso_iff (@UniversallyOpen)
    (Arrow.isoMk X.isoSpec.symm Y.isoSpec.symm
      (Scheme.isoSpec_inv_naturality hom).symm)

private lemma finite_affine_generators_baseChange
    {X Y T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
    (hom : X ⟶ Y) (base : T ⟶ Y) (count : ℕ)
    (generators : Fin count → Γ(X, ⊤))
    (hgenerators : letI := hom.appTop.hom.toAlgebra;
      Submodule.span Γ(Y, ⊤) (Set.range generators) = ⊤) :
    letI := (pullback.snd hom base).appTop.hom.toAlgebra;
    Submodule.span Γ(T, ⊤)
      (Set.range fun index => (pullback.fst hom base).appTop.hom (generators index)) = ⊤ := by
  let := hom.appTop.hom.toAlgebra
  let := base.appTop.hom.toAlgebra
  let := (pullback.fst hom base).appTop.hom.toAlgebra
  let := (pullback.snd hom base).appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(pullback hom base, ⊤) :=
    ((pullback.fst hom base ≫ hom).appTop.hom).toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(pullback hom base, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, ⊤) Γ(T, ⊤) Γ(pullback hom base, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (pullback.fst hom base ≫ hom).appTop.hom =
        (pullback.snd hom base).appTop.hom.comp base.appTop.hom
      rw [pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
  have : Algebra.IsPushout Γ(Y, ⊤) Γ(T, ⊤) Γ(X, ⊤) Γ(pullback hom base, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback hom base)).flip
  exact span_algebraMap_eq_top_of_isPushout _ _ _ _ count generators hgenerators

private lemma polynomial_image_baseChange
    {X Y T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
    (hom : X ⟶ Y) (base : T ⟶ Y) (count : ℕ)
    (polynomial : MvPolynomial (Fin count) Γ(X, ⊤)) :
    PrimeSpectrum.comap (MvPolynomial.map base.appTop.hom) ⁻¹'
      (PrimeSpectrum.comap (MvPolynomial.map hom.appTop.hom) ''
        (PrimeSpectrum.basicOpen polynomial : Set _)) =
    PrimeSpectrum.comap (MvPolynomial.map (pullback.snd hom base).appTop.hom) ''
      (PrimeSpectrum.basicOpen
        (MvPolynomial.map (pullback.fst hom base).appTop.hom polynomial) :
          Set (PrimeSpectrum (MvPolynomial (Fin count) Γ(pullback hom base, ⊤)))) := by
  have square := isPullback_SpecMap_of_isPushout _ _ _ _
    (polynomialMap_isPushout
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback hom base)) count)
  have equality := Scheme.image_preimage_eq_of_isPullback square
    ((PrimeSpectrum.basicOpen polynomial).carrier : Set (Spec
      (.of (MvPolynomial (Fin count) Γ(X, ⊤)))))
  change PrimeSpectrum.comap (MvPolynomial.map (pullback.snd hom base).appTop.hom) ''
    (PrimeSpectrum.comap (MvPolynomial.map (pullback.fst hom base).appTop.hom) ⁻¹'
      ((PrimeSpectrum.basicOpen polynomial).carrier :
        Set (PrimeSpectrum (MvPolynomial (Fin count) Γ(X, ⊤))))) = _ at equality
  have hbasic : PrimeSpectrum.comap
      (MvPolynomial.map (pullback.fst hom base).appTop.hom) ⁻¹'
      (PrimeSpectrum.basicOpen polynomial).carrier =
      (PrimeSpectrum.basicOpen
        (MvPolynomial.map (pullback.fst hom base).appTop.hom polynomial)).carrier :=
    congrArg TopologicalSpace.Opens.carrier
      (PrimeSpectrum.comap_basicOpen
        (MvPolynomial.map (pullback.fst hom base).appTop.hom) polynomial)
  rw [hbasic] at equality
  exact equality.symm

private lemma exists_universallyOpen_finite_affine_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (arrow : i ⟶ j), IsAffineHom (D.map arrow)]
    [∀ index, IsAffine (D.obj index)] (initial : I)
    (X : Scheme.{u}) (hom : X ⟶ D.obj initial)
    [IsFinite hom] [LocallyOfFinitePresentation hom]
    [UniversallyOpen (pullback.snd hom (c.π.app initial))] :
    ∃ (index : I) (arrow : index ⟶ initial),
      UniversallyOpen (pullback.snd hom (D.map arrow)) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine (((Functor.const I).obj c.pt).obj initial) := ‹IsAffine c.pt›
  have : IsAffine (pullback hom (c.π.app initial)) := inferInstance
  have : IsAffine X := isAffine_of_isAffineHom hom
  let := hom.appTop.hom.toAlgebra
  have : Module.Finite Γ(D.obj initial, ⊤) Γ(X, ⊤) := hom.finite_appTop
  obtain ⟨count, generators, hgenerators⟩ :=
    Module.Finite.exists_fin (R := Γ(D.obj initial, ⊤)) (M := Γ(X, ⊤))
  let polynomial := ∑ index : Fin count,
    MvPolynomial.C (generators index) * MvPolynomial.X index
  let E : Set ((polynomialDiagram D count).obj initial) :=
    PrimeSpectrum.comap (MvPolynomial.map hom.appTop.hom) ''
      (PrimeSpectrum.basicOpen polynomial : Set _)
  let polynomialHom := Spec.map
    (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) hom.appTop.hom))
  have : LocallyOfFinitePresentation polynomialHom :=
    MorphismProperty.of_isPullback (polynomial_specMap_isPullback hom count).flip inferInstance
  have : QuasiCompact polynomialHom :=
    quasiCompact_of_compactSpace polynomialHom
  have hE : IsConstructible E := polynomialHom.isConstructible_image
    ((PrimeSpectrum.isCompact_basicOpen polynomial).isConstructible
      PrimeSpectrum.isOpen_basicOpen)
  let homLimit := pullback.snd hom (c.π.app initial)
  let polynomialLimit := Spec.map
    (CommRingCat.ofHom (MvPolynomial.map (σ := Fin count) homLimit.appTop.hom))
  have : UniversallyOpen polynomialLimit :=
    MorphismProperty.of_isPullback (polynomial_specMap_isPullback homLimit count).flip
      inferInstance
  have heq := polynomial_image_baseChange hom (c.π.app initial) count polynomial
  have hopen : IsOpen ((polynomialCone D c count).π.app initial ⁻¹' E) := by
    rw [show (polynomialCone D c count).π.app initial ⁻¹' E = _ from heq]
    exact polynomialLimit.isOpenMap _ PrimeSpectrum.isOpen_basicOpen
  have hcompact : IsCompact ((polynomialCone D c count).π.app initial ⁻¹' E) := by
    rw [show (polynomialCone D c count).π.app initial ⁻¹' E = _ from heq]
    exact (PrimeSpectrum.isCompact_basicOpen _).image polynomialLimit.continuous
  have : ∀ {i j : I} (arrow : i ⟶ j),
      IsAffineHom ((polynomialDiagram D count).map arrow) := by
    intro i j arrow
    dsimp [polynomialDiagram]
    infer_instance
  have : IsAffine ((polynomialDiagram D count).obj initial) := by
    dsimp [polynomialDiagram]
    infer_instance
  have : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨index, arrow, hopenStage⟩ := exists_isOpen_preimage_of_isConstructible
    (polynomialDiagram D count) (polynomialCone D c count)
    (polynomialCone_isLimit D c hc count) initial E hE hopen hcompact
  refine ⟨index, arrow, ?_⟩
  let homStage := pullback.snd hom (D.map arrow)
  let := homStage.appTop.hom.toAlgebra
  apply (universallyOpen_specMap_appTop_iff homStage).mp
  apply (AlgebraicGeometry.universallyOpen_iff_isOpen_image_basicOpen_linearCombination
    Γ(D.obj index, ⊤) Γ(pullback hom (D.map arrow), ⊤) count
    (fun index => (pullback.fst hom (D.map arrow)).appTop.hom (generators index))
    (finite_affine_generators_baseChange hom (D.map arrow) count generators hgenerators)).mpr
  have heqStage := polynomial_image_baseChange hom (D.map arrow) count polynomial
  have hpoly : MvPolynomial.map (pullback.fst hom (D.map arrow)).appTop.hom polynomial =
      ∑ index : Fin count,
        MvPolynomial.C ((pullback.fst hom (D.map arrow)).appTop.hom (generators index)) *
          MvPolynomial.X index := by
    simp [polynomial]
  rw [hpoly] at heqStage
  exact heqStage ▸ hopenStage

private lemma stageProperty_comp
    {I : Type u} [Category.{u} I]
    (S : I ⥤ Scheme.{u})
    (i₀ : I) (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    {i : I} (g : i ⟶ i₀)
    (hP : P ((Over.pullback (S.map g)).map f₀).left)
    {j : I} (e : j ⟶ i) :
    P ((Over.pullback (S.map (e ≫ g))).map f₀).left := by
  rw [S.map_comp]
  exact overPullback_map_comp P (S.map g) (S.map e) f₀ hP

private lemma property_overPullback_iff {B T : Scheme.{u}} (base : T ⟶ B)
    {X Y : Over B} (hom : X ⟶ Y) (P : MorphismProperty Scheme)
    [P.RespectsIso] :
    P ((Over.pullback base).map hom).left ↔
      P (pullback.snd hom.left (pullback.fst Y.hom base)) := by
  let square := overPullback_isPullback base _ _ hom
  exact MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk square.isoPullback (Iso.refl _) (by simp))

private lemma universallyOpen_of_etale_postcomp {X Y Z : Scheme.{u}}
    (hom : X ⟶ Y) (base : Y ⟶ Z) [Etale base]
    (hopen : UniversallyOpen (hom ≫ base)) : UniversallyOpen hom := by
  have : MorphismProperty.HasOfPostcompProperty (@UniversallyOpen) (@Etale) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    intro X Y hom hetale
    have : Etale hom := hetale
    show UniversallyOpen (pullback.diagonal hom)
    infer_instance
  exact MorphismProperty.of_postcomp (@UniversallyOpen) (W' := @Etale)
    hom base inferInstance hopen

private lemma exists_affine_finite_etale_cover
    {X Y : Scheme.{u}} (hom : X ⟶ Y)
    [LocallyOfFinitePresentation hom] [LocallyQuasiFinite hom] [CompactSpace X] :
    ∃ (indices : Finset X) (source target : indices → Scheme.{u})
      (sourceMap : ∀ index, source index ⟶ X)
      (targetMap : ∀ index, target index ⟶ Y)
      (finiteMap : ∀ index, source index ⟶ target index),
      (∀ index, IsAffine (source index)) ∧
      (∀ index, IsAffine (target index)) ∧
      (∀ index, Etale (sourceMap index)) ∧
      (∀ index, Etale (targetMap index)) ∧
      (∀ index, IsFinite (finiteMap index)) ∧
      (∀ index, LocallyOfFinitePresentation (finiteMap index)) ∧
      (∀ index, finiteMap index ≫ targetMap index = sourceMap index ≫ hom) ∧
      (∀ point : X, ∃ (index : indices) (lift : source index), sourceMap index lift = point) := by
  classical
  have localCover (point : X) :
      ∃ (source target : Scheme.{u}) (sourceMap : source ⟶ X)
        (targetMap : target ⟶ Y) (finiteMap : source ⟶ target) (lift : source),
        IsAffine source ∧ IsAffine target ∧ Etale sourceMap ∧ Etale targetMap ∧
        IsFinite finiteMap ∧ LocallyOfFinitePresentation finiteMap ∧
        finiteMap ≫ targetMap = sourceMap ≫ hom ∧ sourceMap lift = point := by
    let neighborhood := Stacks.Flatness.finiteNeighborhoodAt hom point
      ((hom.quasiFiniteAt_iff_isOpen_singleton_asFiber).mp (hom.quasiFiniteAt point))
    let toSource := neighborhood.openSubscheme.ι ≫
      pullback.fst hom neighborhood.neighborhood.toBase
    let toTarget := neighborhood.openSubscheme.ι ≫
      pullback.snd hom neighborhood.neighborhood.toBase
    have : IsFinite toTarget := neighborhood.spec.1
    have : LocallyOfFinitePresentation toTarget := by dsimp [toTarget]; infer_instance
    have : Etale toSource := by dsimp [toSource]; infer_instance
    obtain ⟨originalPoint, originalPoint_eq, -⟩ := neighborhood.spec.2.1
    let affineIndex := neighborhood.neighborhood.scheme.affineCover.idx
      neighborhood.neighborhood.point
    obtain ⟨affinePoint, affinePoint_eq⟩ :=
      neighborhood.neighborhood.scheme.affineCover.covers
        neighborhood.neighborhood.point
    let affineMap := neighborhood.neighborhood.scheme.affineCover.f affineIndex
    have : IsAffine (neighborhood.neighborhood.scheme.affineCover.X affineIndex) :=
      inferInstanceAs (IsAffine (Spec _))
    obtain ⟨lift, lift_fst, lift_snd⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := toTarget) (g := affineMap) originalPoint affinePoint
      (originalPoint_eq.trans affinePoint_eq.symm)
    refine ⟨pullback toTarget affineMap,
      neighborhood.neighborhood.scheme.affineCover.X affineIndex,
      pullback.fst toTarget affineMap ≫ toSource,
      affineMap ≫ neighborhood.neighborhood.toBase,
      pullback.snd toTarget affineMap, lift, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · rw [← Category.assoc, ← pullback.condition, Category.assoc]
      have hcomm : toTarget ≫ neighborhood.neighborhood.toBase = toSource ≫ hom := by
        dsimp [toTarget, toSource]
        rw [Category.assoc, Category.assoc, pullback.condition]
      rw [hcomm]
      exact (Category.assoc _ _ _).symm
    · simp only [Scheme.Hom.comp_apply, lift_fst]
      exact (neighborhood.spec.2.2 originalPoint originalPoint_eq).1
  choose source target sourceMap targetMap finiteMap lift hsource htarget
    hsourceMap htargetMap hfiniteMap hfinitePresentation hcomm hlift using localCover
  have hopen (point : X) : IsOpen (Set.range (sourceMap point)) := by
    have := hsourceMap point
    simpa using (sourceMap point).isOpenMap Set.univ isOpen_univ
  have hcover : Set.univ ⊆ ⋃ point : X, Set.range (sourceMap point) := by
    intro point _
    exact Set.mem_iUnion.mpr ⟨point, lift point, hlift point⟩
  obtain ⟨indices, hindices⟩ := isCompact_univ.elim_finite_subcover
    (fun point => Set.range (sourceMap point)) hopen hcover
  refine ⟨indices, (fun index => source index.val), (fun index => target index.val),
    (fun index => sourceMap index.val), (fun index => targetMap index.val),
    (fun index => finiteMap index.val), (fun index => hsource index.val),
    (fun index => htarget index.val), (fun index => hsourceMap index.val),
    (fun index => htargetMap index.val), (fun index => hfiniteMap index.val),
    (fun index => hfinitePresentation index.val), (fun index => hcomm index.val), ?_⟩
  intro point
  obtain ⟨index, hindex, lift, hlift⟩ := Set.mem_iUnion₂.mp (hindices (Set.mem_univ point))
  exact ⟨⟨index, hindex⟩, lift, hlift⟩

/-- Universal openness of a base change of `pullback.snd hom proj` along `t` is the same as that
of the base change of `hom` along `t ≫ proj`. -/
private lemma universallyOpen_snd_pullback_snd_iff {X Y Z T : Scheme.{u}}
    (hom : X ⟶ Z) (proj : Y ⟶ Z) (t : T ⟶ Y) (q : T ⟶ Z) (h : t ≫ proj = q) :
    UniversallyOpen (pullback.snd (pullback.snd hom proj) t) ↔
      UniversallyOpen (pullback.snd hom q) := by
  subst h
  have square := (IsPullback.of_hasPullback (pullback.snd hom proj) t).paste_horiz
    (IsPullback.of_hasPullback hom proj)
  exact MorphismProperty.arrow_mk_iso_iff (@UniversallyOpen)
    (Arrow.isoMk square.isoPullback (Iso.refl _) square.isoPullback_hom_snd)

private lemma exists_universallyOpen_finite_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (diagram : I ⥤ Scheme.{u}) (cone : Cone diagram) (limit : IsLimit cone)
    [∀ {first second : I} (arrow : first ⟶ second), IsAffineHom (diagram.map arrow)]
    (initial : I) {source target : Scheme.{u}} [IsAffine target]
    (hom : source ⟶ target) (structureMap : target ⟶ diagram.obj initial)
    [IsFinite hom] [LocallyOfFinitePresentation hom]
    (hopen : UniversallyOpen (pullback.snd hom
      (pullback.snd (cone.π.app initial) structureMap))) :
    ∃ (index : I) (arrow : index ⟶ initial),
      UniversallyOpen (pullback.snd hom (pullback.snd (diagram.map arrow) structureMap)) := by
  let stages := baseChangeDiagram diagram initial (Over.mk structureMap)
  let limitCone := baseChangeCone diagram cone initial (Over.mk structureMap)
  have limitProof := baseChangeConeIsLimit diagram limit initial (Over.mk structureMap)
  have : ∀ {first second : Over initial} (arrow : first ⟶ second),
      IsAffineHom (stages.map arrow) := fun arrow =>
    isAffineHom_baseChangeDiagram_map diagram initial (Over.mk structureMap) arrow
  have : IsAffine (Over.mk structureMap).left := ‹IsAffine target›
  have : ∀ index : Over initial, IsAffine (stages.obj index) := fun index =>
    isAffine_baseChangeDiagram_obj diagram initial (Over.mk structureMap) index
  let initialIndex : Over initial := Over.mk (𝟙 initial)
  let initialProjection := pullback.snd (diagram.map initialIndex.hom) structureMap
  let initialHom := pullback.snd hom initialProjection
  have projection_eq (index : Over initial) :
      limitCone.π.app index ≫ pullback.snd (diagram.map index.hom) structureMap =
        pullback.snd (cone.π.app initial) structureMap :=
    baseChangeTransition_snd (diagram.map index.hom) (cone.π.app initial)
      (cone.π.app index.left) (by simp) (Over.mk structureMap)
  have transition_eq {first second : Over initial} (arrow : first ⟶ second) :
      stages.map arrow ≫ pullback.snd (diagram.map second.hom) structureMap =
        pullback.snd (diagram.map first.hom) structureMap :=
    baseChangeTransition_snd (diagram.map second.hom) (diagram.map first.hom)
      (diagram.map arrow.left) (by rw [← diagram.map_comp, arrow.w]) (Over.mk structureMap)
  have hfinite : IsFinite initialHom := inferInstance
  have hpresentation : LocallyOfFinitePresentation initialHom := inferInstance
  have hlimitOpen :
      UniversallyOpen (pullback.snd initialHom (limitCone.π.app initialIndex)) := by
    exact (universallyOpen_snd_pullback_snd_iff hom initialProjection _ _
      (projection_eq initialIndex)).mpr hopen
  obtain ⟨index, arrow, hopenStage⟩ :=
    @exists_universallyOpen_finite_affine_baseChange (Over initial) _ _ stages limitCone
      limitProof _ _ initialIndex (pullback hom initialProjection) initialHom hfinite
      hpresentation hlimitOpen
  refine ⟨index.left, index.hom, ?_⟩
  exact (universallyOpen_snd_pullback_snd_iff hom initialProjection _ _
    (transition_eq arrow)).mp hopenStage

private lemma property_overPullback_snd_iff {baseScheme stage : Scheme.{u}}
    (base : stage ⟶ baseScheme) {source target : Over baseScheme} (hom : source ⟶ target)
    (property : MorphismProperty Scheme) [property.RespectsIso] :
    property ((Over.pullback base).map hom).left ↔
      property (pullback.snd hom.left (pullback.snd base target.hom)) := by
  rw [property_overPullback_iff base hom property]
  let symmetry := pullbackSymmetry target.hom base
  let comparison := pullback.map hom.left (pullback.fst target.hom base)
    hom.left (pullback.snd base target.hom) (𝟙 source.left) symmetry.hom (𝟙 target.left)
    (by simp) (by simp [symmetry])
  have : IsIso comparison := by dsimp [comparison]; infer_instance
  exact property.arrow_mk_iso_iff
    (Arrow.isoMk (asIso comparison) symmetry (by
      dsimp only [comparison, pullback.map]
      exact pullback.lift_snd _ _ _))

private lemma exists_universallyOpen_finite_over_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (diagram : I ⥤ Scheme.{u}) (cone : Cone diagram) (limit : IsLimit cone)
    [∀ {first second : I} (arrow : first ⟶ second), IsAffineHom (diagram.map arrow)]
    (initial : I) (source target : Over (diagram.obj initial)) (hom : source ⟶ target)
    [IsAffine target.left] [IsFinite hom.left] [LocallyOfFinitePresentation hom.left]
    (hopen : UniversallyOpen ((Over.pullback (cone.π.app initial)).map hom).left) :
    ∃ (index : I) (arrow : index ⟶ initial),
      UniversallyOpen ((Over.pullback (diagram.map arrow)).map hom).left := by
  obtain ⟨index, arrow, hopenStage⟩ := exists_universallyOpen_finite_baseChange
    diagram cone limit initial hom.left target.hom
    ((property_overPullback_snd_iff (cone.π.app initial) hom (@UniversallyOpen)).mp hopen)
  exact ⟨index, arrow,
    (property_overPullback_snd_iff (diagram.map arrow) hom (@UniversallyOpen)).mpr hopenStage⟩

/-- Universal openness descends from the limit to a stage, for a locally quasi-finite, locally
finitely presented morphism of schemes over a stage whose source is quasi-compact. -/
theorem exists_universallyOpen_baseChange_of_locallyQuasiFinite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (diagram : I ⥤ Scheme.{u}) (cone : Cone diagram) (limit : IsLimit cone)
    [∀ {first second : I} (arrow : first ⟶ second), IsAffineHom (diagram.map arrow)]
    (initial : I) (source target : Over (diagram.obj initial)) (hom : source ⟶ target)
    [CompactSpace source.left] [LocallyOfFinitePresentation hom.left]
    [LocallyQuasiFinite hom.left]
    [UniversallyOpen ((Over.pullback (cone.π.app initial)).map hom).left] :
    ∃ (index : I) (arrow : index ⟶ initial),
      UniversallyOpen ((Over.pullback (diagram.map arrow)).map hom).left := by
  classical
  obtain ⟨indices, coverSource, coverTarget, sourceMap, targetMap, finiteMap,
    hsource, htarget, hsourceMap, htargetMap, hfinite, hfinitePresentation,
    hcomm, hcover⟩ := exists_affine_finite_etale_cover hom.left
  let sources (index : indices) : Over (diagram.obj initial) :=
    Over.mk (sourceMap index ≫ source.hom)
  let targets (index : indices) : Over (diagram.obj initial) :=
    Over.mk (targetMap index ≫ target.hom)
  let toSource (index : indices) : sources index ⟶ source := Over.homMk (sourceMap index)
  let toTarget (index : indices) : targets index ⟶ target := Over.homMk (targetMap index)
  let finiteHom (index : indices) : sources index ⟶ targets index :=
    Over.homMk (finiteMap index) (by
      dsimp [sources, targets]
      rw [← Category.assoc, hcomm, Category.assoc, hom.w])
  have comm_over (index : indices) : finiteHom index ≫ toTarget index =
      toSource index ≫ hom := by ext; exact hcomm index
  have eventually_open (index : indices) :
      ∃ (stage : I) (arrow : stage ⟶ initial),
        UniversallyOpen ((Over.pullback (diagram.map arrow)).map (finiteHom index)).left := by
    have : IsAffine (targets index).left := htarget index
    have : IsFinite (finiteHom index).left := hfinite index
    have : LocallyOfFinitePresentation (finiteHom index).left := hfinitePresentation index
    apply exists_universallyOpen_finite_over_baseChange diagram cone limit initial
      (sources index) (targets index) (finiteHom index)
    let baseChange := Over.pullback (cone.π.app initial)
    have : Etale (baseChange.map (toSource index)).left :=
      MorphismProperty.overPullbackMap _ _ (hsourceMap index)
    have : Etale (baseChange.map (toTarget index)).left :=
      MorphismProperty.overPullbackMap _ _ (htargetMap index)
    apply universallyOpen_of_etale_postcomp (baseChange.map (finiteHom index)).left
      (baseChange.map (toTarget index)).left
    have equality : (baseChange.map (finiteHom index)).left ≫
        (baseChange.map (toTarget index)).left =
        (baseChange.map (toSource index)).left ≫ (baseChange.map hom).left := by
      simpa only [Functor.map_comp, Over.comp_left] using
        congrArg (fun arrow => (baseChange.map arrow).left) (comm_over index)
    rw [equality]
    infer_instance
  choose stages arrows hstages using eventually_open
  let overStages (index : indices) : Over initial := Over.mk (arrows index)
  obtain ⟨common, hcommon⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image overStages)
  have edges (index : indices) : Nonempty (common ⟶ overStages index) :=
    hcommon (Finset.mem_image_of_mem overStages (Finset.mem_univ index))
  let edge (index : indices) := Classical.choice (edges index)
  have hopen (index : indices) :
      UniversallyOpen ((Over.pullback (diagram.map common.hom)).map (finiteHom index)).left := by
    have stageOpen := stageProperty_comp diagram initial (sources index) (targets index)
      (finiteHom index) (@UniversallyOpen) (arrows index) (hstages index) (edge index).left
    have equality : (edge index).left ≫ arrows index = common.hom := (edge index).w
    rwa [equality] at stageOpen
  refine ⟨common.left, common.hom, ?_⟩
  let baseChange := Over.pullback (diagram.map common.hom)
  apply universallyOpen_of_etale_local_cover (baseChange.map hom).left
    (fun index => (baseChange.obj (sources index)).left)
    (fun index => (baseChange.obj (targets index)).left)
    (fun index => (baseChange.map (toSource index)).left)
    (fun index => (baseChange.map (toTarget index)).left)
    (fun index => (baseChange.map (finiteHom index)).left)
  · intro index
    exact MorphismProperty.overPullbackMap _ _ (hsourceMap index)
  · intro index
    exact MorphismProperty.overPullbackMap _ _ (htargetMap index)
  · intro index
    simpa only [Functor.map_comp, Over.comp_left] using
      congrArg (fun arrow => (baseChange.map arrow).left) (comm_over index)
  · exact hopen
  · intro point
    obtain ⟨index, originalPoint, originalPoint_eq⟩ := hcover
      ((pullback.fst source.hom (diagram.map common.hom)) point)
    obtain ⟨lift, _, lift_eq⟩ := Scheme.exists_preimage_of_isPullback
      (overPullback_isPullback (diagram.map common.hom) _ _ (toSource index))
      originalPoint point originalPoint_eq
    exact ⟨index, lift, lift_eq⟩

private lemma exists_locallyQuasiFinite_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [LocallyOfFiniteType ((Over.pullback (c.π.app i₀)).map f₀).left]
    [LocallyQuasiFinite ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      (LocallyOfFiniteType ((Over.pullback (S.map g)).map f₀).left ∧
        QuasiCompact ((Over.pullback (S.map g)).map f₀).left) ∧
          LocallyQuasiFinite ((Over.pullback (S.map g)).map f₀).left := by
  have : QuasiCompact f₀.left := quasiCompact_of_compactSpace f₀.left
  have : QuasiCompact ((Over.pullback (c.π.app i₀)).map f₀).left :=
    MorphismProperty.overPullbackMap (c.π.app i₀) f₀ inferInstance
  exact exists_quasiFinite_baseChange_of_quasiFinite_limitBaseChange
    S c hc i₀ X₀ Y₀ f₀

/-- Let `S` be the limit of a cofiltered system of schemes with affine transition morphisms and
`f₀ : X₀ ⟶ Y₀` a locally finitely presented morphism over a quasi-compact quasi-separated stage
`S i₀`, with `X₀`, `Y₀` quasi-compact and quasi-separated. If the base change of `f₀` to the limit
is locally of finite type, locally quasi-finite and universally open, then so is its base change
to some stage `S i`. -/
@[stacks 0F34]
public theorem exists_locallyQuasiFinite_universallyOpen_baseChange_of_limitBaseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [LocallyOfFiniteType ((Over.pullback (c.π.app i₀)).map f₀).left]
    [LocallyQuasiFinite ((Over.pullback (c.π.app i₀)).map f₀).left]
    [UniversallyOpen ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      (LocallyOfFiniteType ((Over.pullback (S.map g)).map f₀).left ∧
        LocallyQuasiFinite ((Over.pullback (S.map g)).map f₀).left) ∧
          UniversallyOpen ((Over.pullback (S.map g)).map f₀).left := by
  obtain ⟨i, gi, ⟨⟨hft, _⟩, hqf⟩⟩ :=
    exists_locallyQuasiFinite_baseChange S c hc i₀ X₀ Y₀ f₀
  have hUOStage : ∃ (j : I) (gj : j ⟶ i),
      UniversallyOpen ((Over.pullback (S.map (gj ≫ gi))).map f₀).left := by
    let sourceStage := (Over.pullback (S.map gi)).obj X₀
    let targetStage := (Over.pullback (S.map gi)).obj Y₀
    let homStage := (Over.pullback (S.map gi)).map f₀
    have : QuasiCompact X₀.hom := quasiCompact_of_compactSpace X₀.hom
    have : CompactSpace (S.obj i) :=
      QuasiCompact.compactSpace_of_compactSpace (S.map gi)
    have : QuasiCompact (pullback.snd X₀.hom (S.map gi)) :=
      quasiCompact_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback X₀.hom (S.map gi)) inferInstance
    have : CompactSpace sourceStage.left :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd X₀.hom (S.map gi))
    have : LocallyOfFinitePresentation homStage.left :=
      MorphismProperty.overPullbackMap _ _ inferInstance
    have : LocallyQuasiFinite homStage.left := hqf
    have : UniversallyOpen ((Over.pullback (c.π.app i)).map homStage).left :=
      universallyOpen_of_pullback_stage c i₀ X₀ Y₀ f₀ gi
    obtain ⟨j, gj, hj⟩ := exists_universallyOpen_baseChange_of_locallyQuasiFinite
      S c hc i sourceStage targetStage homStage
    refine ⟨j, gj, ?_⟩
    rw [S.map_comp]
    exact (overPullback_map_comp_iff (@UniversallyOpen) (S.map gi) (S.map gj) f₀).mpr hj
  obtain ⟨j, gj, hj⟩ := hUOStage
  exact ⟨j, gj ≫ gi,
    ⟨stageProperty_comp S i₀ X₀ Y₀ f₀ (@LocallyOfFiniteType) gi hft gj,
      stageProperty_comp S i₀ X₀ Y₀ f₀ (@LocallyQuasiFinite) gi hqf gj⟩, hj⟩

end AlgebraicGeometry

end
