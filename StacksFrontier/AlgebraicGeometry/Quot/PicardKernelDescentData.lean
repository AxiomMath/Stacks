module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardPushforwardUnitIso
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalExcision

/-!
# The descent datum of a locally trivial invertible module on a base change

In Situation 0D25 let `T` be a test scheme over the base and `L` an invertible module on
`X_T` which becomes trivial on the base changes `X_{U i}` of an fpqc covering family
`{U i ⟶ T}` of test schemes.  The second half of the proof of Stacks 0D27 descends `L` to `T`:
the two trivializations of `L` on `X_{U i ×_T U j}` differ by a unit which, by the hypothesis
`𝒪_T ≅ f_{T, *}𝒪_{X_T}`, is a unit on `U i ×_T U j`, and these units form a descent datum on the
structure sheaves of the `U i`.  This file constructs that descent datum.

The units are not formed explicitly.  The transition isomorphism `τ i j` of the two inverse
images of the structure sheaves to `U i ×_T U j` is the unique isomorphism whose inverse image to
`X_{U i ×_T U j}` is the ratio `ρ` of the two trivializations: under the hypothesis of
Stacks 0D27 the inverse image along `X_{U i ×_T U j} ⟶ U i ×_T U j` is bijective on morphisms
into invertible modules (`AlgebraicGeometry.Space.modulePushforwardUnitIso`), and that bijectivity
survives the identification of `U i ×_T U j` with the fibre product of the represented spaces.
The cocycle condition is then checked after pullback to the base change `Z ×_T X_T` of an
arbitrary test space `Z`, where each transition isomorphism is a ratio of two trivializations of
one module; pullback to that base change is faithful on morphisms into invertible modules, which
is checked on an étale scheme atlas of `Z`.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization`: a covering family of test
  schemes with trivializations of `L` on the base changes of its members.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.ρ`: the ratio of two
  trivializations read on a space mapping to two members over the same morphism to `X_T`.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.τ`: the transition isomorphisms.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.descentDatum`: **the descent
  datum** of Stacks 04W3 on the family `{U i ⟶ T}`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.modulePullback_bcFst_map_injective`: pullback to
  `Z ×_T X_T` is faithful on morphisms into invertible modules.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.transitionOn_τ`: the transition
  isomorphisms read on a test space are ratios of trivializations.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.τ_cocycle`: the cocycle condition.

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open QuasiCoherentDescent

/-! ### Bijectivity of a functor on a hom set -/

/-- An isomorphism `A ≅ B` with prescribed image under a functor that is bijective on the four
hom sets between `A` and `B`. -/
def _root_.CategoryTheory.Functor.isoOfMapBijective {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C}
    (hAB : Function.Bijective (fun φ : A ⟶ B ↦ F.map φ))
    (hBA : Function.Bijective (fun φ : B ⟶ A ↦ F.map φ))
    (hAA : Function.Injective (fun φ : A ⟶ A ↦ F.map φ))
    (hBB : Function.Injective (fun φ : B ⟶ B ↦ F.map φ)) (σ : F.obj A ≅ F.obj B) : A ≅ B where
  hom := Function.surjInv hAB.2 σ.hom
  inv := Function.surjInv hBA.2 σ.inv
  hom_inv_id := hAA (by
    simp only [Functor.map_comp]
    rw [Function.surjInv_eq hAB.2, Function.surjInv_eq hBA.2, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id])
  inv_hom_id := hBB (by
    simp only [Functor.map_comp]
    rw [Function.surjInv_eq hAB.2, Function.surjInv_eq hBA.2, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id])

/-- The image under `F` of the isomorphism `F.isoOfMapBijective … σ` is `σ`. -/
theorem _root_.CategoryTheory.Functor.mapIso_isoOfMapBijective {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {A B : C}
    (hAB : Function.Bijective (fun φ : A ⟶ B ↦ F.map φ))
    (hBA : Function.Bijective (fun φ : B ⟶ A ↦ F.map φ))
    (hAA : Function.Injective (fun φ : A ⟶ A ↦ F.map φ))
    (hBB : Function.Injective (fun φ : B ⟶ B ↦ F.map φ)) (σ : F.obj A ≅ F.obj B) :
    F.mapIso (F.isoOfMapBijective hAB hBA hAA hBB σ) = σ :=
  Iso.ext (Function.surjInv_eq hAB.2 σ.hom)

/-- Two isomorphisms that agree after conjugation by isomorphisms agree. -/
theorem _root_.CategoryTheory.Iso.eq_of_conj {C : Type*} [Category C] {X Y X' Y' : C}
    (a : X ≅ X') (b : Y ≅ Y') {e e' : X' ≅ Y'} (h : a ≪≫ e ≪≫ b.symm = a ≪≫ e' ≪≫ b.symm) :
    e = e' := by
  ext
  have := congrArg (fun f : X ≅ Y ↦ a.inv ≫ f.hom ≫ b.hom) h
  simpa using this

/-! ### Pullback along an isomorphism of algebraic spaces -/

/-- The inverse image along an isomorphism of algebraic spaces is an equivalence of the
categories of modules, with quasi-inverse the inverse image along the inverse. -/
def modulePullbackEquivalenceOfIso {A A' : AlgebraicSpaces B S hS} (e : A ≅ A') :
    Modules.{u, u} B S hS A'.1 A'.2 ≌ Modules.{u, u} B S hS A.1 A.2 :=
  CategoryTheory.Equivalence.mk (modulePullback B S hS e.hom) (modulePullback B S hS e.inv)
    ((modulePullbackCompIso B S hS e.inv e.hom ≪≫
      eqToIso (congrArg (modulePullback B S hS) e.inv_hom_id) ≪≫
        modulePullbackIdIso B S hS A').symm)
    (modulePullbackCompIso B S hS e.hom e.inv ≪≫
      eqToIso (congrArg (modulePullback B S hS) e.hom_inv_id) ≪≫ modulePullbackIdIso B S hS A)

/-- Bijectivity of the inverse image on morphisms into invertible modules survives
postcomposition with an isomorphism of algebraic spaces. -/
theorem bijective_modulePullback_map_comp_iso {W A A' : AlgebraicSpaces B S hS} (q : W ⟶ A)
    (e : A ≅ A')
    (hq : ∀ (P N : Modules.{u, u} B S hS A.1 A.2), IsInvertibleModule A N →
      Function.Bijective (fun φ : P ⟶ N ↦ (modulePullback B S hS q).map φ))
    (P N : Modules.{u, u} B S hS A'.1 A'.2) (hN : IsInvertibleModule A' N) :
    Function.Bijective (fun φ : P ⟶ N ↦ (modulePullback B S hS (q ≫ e.hom)).map φ) := by
  refine Functor.bijective_map_of_natIso (modulePullbackCompIso B S hS q e.hom) ?_
  exact (hq _ _ (modulePullbackInvertible e.hom N hN)).comp
    ((modulePullbackEquivalenceOfIso e).fullyFaithfulFunctor.map_bijective P N)

/-- Two morphisms have equal inverse images along a composite exactly when their iterated inverse
images agree. -/
theorem modulePullback_comp_map_eq_iff {X Y W : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ W)
    {M N : Modules.{u, u} B S hS W.1 W.2} (φ ψ : M ⟶ N) :
    (modulePullback B S hS (f ≫ g)).map φ = (modulePullback B S hS (f ≫ g)).map ψ ↔
      (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) =
        (modulePullback B S hS f).map ((modulePullback B S hS g).map ψ) := by
  have hφ := (modulePullbackCompIso B S hS f g).hom.naturality φ
  have hψ := (modulePullbackCompIso B S hS f g).hom.naturality ψ
  simp only [Functor.comp_map] at hφ hψ
  constructor
  · intro h
    rw [← Iso.cancel_iso_hom_right _ _ ((modulePullbackCompIso B S hS f g).app N)]
    show _ ≫ (modulePullbackCompIso B S hS f g).hom.app N =
      _ ≫ (modulePullbackCompIso B S hS f g).hom.app N
    rw [hφ, hψ, h]
  · intro h
    rw [← Iso.cancel_iso_hom_left ((modulePullbackCompIso B S hS f g).app M)]
    show (modulePullbackCompIso B S hS f g).hom.app M ≫ _ =
      (modulePullbackCompIso B S hS f g).hom.app M ≫ _
    rw [← hφ, ← hψ, h]

/-! ### A trivialization of an invertible module along a covering family of test schemes -/

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-! ### Faithfulness of pullback to the base change along `X_T ⟶ T` -/

variable {s} in
/-- The base change `Z ×_T X_T` of `X_T ⟶ T` along a morphism `z : Z ⟶ T`. -/
abbrev bcSpace {T : s.SchemesOver} {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS z (baseChangeInclusion s.f T)

variable {s} in
/-- The projection `Z ×_T X_T ⟶ Z`. -/
abbrev bcFst {T : s.SchemesOver} {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) :
    bcSpace z ⟶ Z :=
  ObjectProperty.homMk (pullback.fst z.hom (baseChangeInclusion s.f T).hom)

variable {s} in
/-- The projection `Z ×_T X_T ⟶ X_T`. -/
abbrev bcSnd {T : s.SchemesOver} {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) :
    bcSpace z ⟶ s.baseChange T :=
  ObjectProperty.homMk (pullback.snd z.hom (baseChangeInclusion s.f T).hom)

variable {s} in
/-- The square `Z ×_T X_T ⟶ X_T ⟶ T`, `Z ×_T X_T ⟶ Z ⟶ T` commutes. -/
theorem bc_condition {T : s.SchemesOver} {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) :
    bcFst z ≫ z = bcSnd z ≫ baseChangeInclusion s.f T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS z (baseChangeInclusion s.f T)).w

/-- Faithfulness of pullback to the base change, read on a morphism from a represented scheme
lying over a test scheme over `T`. -/
theorem modulePullback_map_eq_of_bcFst (h : s.StructureSheafMapIso) {T : s.SchemesOver}
    {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (hN : IsInvertibleModule Z N) (φ ψ : M ⟶ N)
    (hφψ : (modulePullback B S hS (bcFst z)).map φ = (modulePullback B S hS (bcFst z)).map ψ)
    {U' : s.SchemesOver} (g' : U' ⟶ T) (a : (schemeSpaceFunctor B S hS).obj U'.left ⟶ Z)
    (ha : (schemeSpaceFunctor B S hS).map g'.left = a ≫ z) :
    (modulePullback B S hS a).map φ = (modulePullback B S hS a).map ψ := by
  have hm : (baseChangeInclusion s.f U' ≫ a) ≫ z =
      baseChangeMap s.f g' ≫ baseChangeInclusion s.f T := by
    rw [baseChangeMap_comp_inclusion, Category.assoc, ha]
  obtain ⟨m, hmq⟩ : ∃ m : baseChangeSpace s.f U' ⟶
      AlgebraicSpaces.fiberProduct B S hS z (baseChangeInclusion s.f T),
      m ≫ (bcFst z) = baseChangeInclusion s.f U' ≫ a :=
    ⟨_, (AlgebraicSpaces.isPullback_fiberProduct B S hS z (baseChangeInclusion s.f T)).lift_fst
      _ _ hm⟩
  have h₁ : (modulePullback B S hS (m ≫ (bcFst z))).map φ =
      (modulePullback B S hS (m ≫ (bcFst z))).map ψ :=
    (modulePullback_comp_map_eq_iff _ _ φ ψ).2 (by rw [hφψ])
  rw [hmq, modulePullback_comp_map_eq_iff] at h₁
  have hb := bijective_modulePullback_map_of_isInvertibleModule (baseChangeInclusion s.f U') (h U')
    ((modulePullback B S hS a).obj M) (modulePullbackInvertible a N hN)
  exact hb.1 h₁

/-- Faithfulness of pullback to the base change, given an étale scheme atlas lying over a test
scheme over `T`. -/
theorem modulePullback_bcFst_map_injective_of_atlas (h : s.StructureSheafMapIso) {T : s.SchemesOver}
    {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (hN : IsInvertibleModule Z N) (φ ψ : M ⟶ N)
    (hφψ : (modulePullback B S hS (bcFst z)).map φ = (modulePullback B S hS (bcFst z)).map ψ)
    {U' : s.SchemesOver} (g' : U' ⟶ T) (a₀ : yoneda.obj U'.left ⟶ Z.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a₀)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a₀)
    (ha : (schemeSpaceFunctor B S hS).map g'.left =
      (ObjectProperty.homMk a₀ : (schemeSpaceFunctor B S hS).obj U'.left ⟶ Z) ≫ z) :
    φ = ψ := by
  have hEtale : IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U'.left) (fun _ => a₀) := by
    refine ⟨Z.property, fun _ => isAlgebraicSpace_yoneda B S hS U'.left,
      fun _ => (isEtale_iff_presheaf_of_yoneda B S hS a₀).2 hetale, ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS Z.1 Z.2 U'.left a₀).1 hsurj
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : Unit => (schemeSpaceFunctor B S hS).obj U'.left)
    (fun _ => (ObjectProperty.homMk a₀ : (schemeSpaceFunctor B S hS).obj U'.left ⟶ Z)) hEtale φ ψ
    (fun _ => ?_)
  exact s.modulePullback_map_eq_of_bcFst h z hN φ ψ hφψ g' _ ha

/-- **Pullback to the base change along `X_T ⟶ T` is faithful on morphisms into invertible
modules**, for every algebraic space `Z` over a test scheme `T`, under the hypothesis of
Stacks 0D27.  Faithfulness is checked on an étale scheme atlas of `Z`, over which it is the
hypothesis at a test scheme. -/
theorem modulePullback_bcFst_map_injective (h : s.StructureSheafMapIso) {T : s.SchemesOver}
    {Z : AlgebraicSpaces B S hS} (z : Z ⟶ s.baseSpaceAt T) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (hN : IsInvertibleModule Z N) (φ ψ : M ⟶ N)
    (hφψ : (modulePullback B S hS (bcFst z)).map φ = (modulePullback B S hS (bcFst z)).map ψ) :
    φ = ψ := by
  obtain ⟨U, a₀, hsurj, hetale⟩ := Z.property.exists_atlas
  set g := Yoneda.fullyFaithful.preimage
    ((ObjectProperty.homMk a₀ : (schemeSpaceFunctor B S hS).obj U ⟶ Z) ≫ z).hom
  exact s.modulePullback_bcFst_map_injective_of_atlas h z hN φ ψ hφψ
    (U' := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom))
    (CostructuredArrow.homMk g rfl) a₀ hsurj hetale
    (ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _))

/-- A family of test schemes over `T` together with trivializations of an `𝒪_{X_T}`-module `L`
after pullback to the base changes of its members. -/
structure LocalTrivialization (T : s.SchemesOver)
    (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2) where
  /-- The index type of the family. -/
  I : Type (u + 1)
  /-- The members of the family. -/
  U : I → s.SchemesOver
  /-- The morphisms of the family. -/
  g : ∀ i, U i ⟶ T
  /-- The trivializations of `L` on the base changes of the members. -/
  triv : ∀ i, (modulePullback B S hS (baseChangeMap s.f (g i))).obj L ≅
    structureModule (s.baseChange (U i))

namespace LocalTrivialization

variable {s} {T : s.SchemesOver}
  {L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2}
  (t : s.LocalTrivialization T L)

/-- The member `U i`, as an algebraic space. -/
abbrev Y (i : t.I) : AlgebraicSpaces B S hS := s.baseSpaceAt (t.U i)

/-- The morphism `U i ⟶ T`, as a morphism of algebraic spaces. -/
abbrev fY (i : t.I) : t.Y i ⟶ s.baseSpaceAt T := (schemeSpaceFunctor B S hS).map (t.g i).left

/-- The base change `X_{U i}`. -/
abbrev Y' (i : t.I) : AlgebraicSpaces B S hS := s.baseChange (t.U i)

/-- The morphism `X_{U i} ⟶ X_T`. -/
abbrev f' (i : t.I) : t.Y' i ⟶ s.baseChange T := baseChangeMap s.f (t.g i)

/-- The projection `X_{U i} ⟶ U i`. -/
abbrev hh (i : t.I) : t.Y' i ⟶ t.Y i := baseChangeInclusion s.f (t.U i)

/-- The square `X_{U i} ⟶ X_T ⟶ T`, `X_{U i} ⟶ U i ⟶ T` commutes. -/
theorem f'_comp_inclusion (i : t.I) :
    t.f' i ≫ baseChangeInclusion s.f T = t.hh i ≫ t.fY i :=
  baseChangeMap_comp_inclusion s.f (t.g i)

attribute [local instance] BigFppfSite.hasPullbacks_schemes in
/-- Fibre products of the schemes of the big fppf site over `S`. -/
instance hasPullbacks_bigFppfOver : HasPullbacks (BigFppfOver B S hS) := inferInstance

/-- The overlap `U i ×_T U j`, as a test scheme over the base. -/
abbrev pairTest (i j : t.I) : s.SchemesOver :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
    (pullback.fst (t.g i).left (t.g j).left) ≫ (t.U i).hom)

/-- The first projection of the overlap. -/
def pairTestFst (i j : t.I) : t.pairTest i j ⟶ t.U i :=
  CostructuredArrow.homMk (pullback.fst (t.g i).left (t.g j).left) rfl

/-- The second projection of the overlap. -/
def pairTestSnd (i j : t.I) : t.pairTest i j ⟶ t.U j :=
  CostructuredArrow.homMk (pullback.snd (t.g i).left (t.g j).left) (by
    change _ = (schemeSpaceFunctor B S hS).map (pullback.fst (t.g i).left (t.g j).left) ≫
      (t.U i).hom
    rw [← CostructuredArrow.w (t.g j), ← CostructuredArrow.w (t.g i), ← Category.assoc,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- The two projections of the overlap `U i ×_T U j` agree after composition to `T`. -/
theorem pairTestFst_comp (i j : t.I) : t.pairTestFst i j ≫ t.g i = t.pairTestSnd i j ≫ t.g j :=
  CostructuredArrow.hom_ext _ _ (by
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left]
    exact pullback.condition)

/-- The overlap of the represented spaces is represented by the overlap test scheme. -/
def pairIso (i j : t.I) : s.baseSpaceAt (t.pairTest i j) ≅ pair B S hS t.Y t.fY i j :=
  (HomSituation.isPullback_schemeSpaceFunctor (t.g i).left (t.g j).left).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (t.fY i) (t.fY j))

/-- The identification of the overlaps is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem pairIso_hom_fst (i j : t.I) :
    (t.pairIso i j).hom ≫ pairFst B S hS t.Y t.fY i j =
      (schemeSpaceFunctor B S hS).map (t.pairTestFst i j).left :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification of the overlaps is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem pairIso_hom_snd (i j : t.I) :
    (t.pairIso i j).hom ≫ pairSnd B S hS t.Y t.fY i j =
      (schemeSpaceFunctor B S hS).map (t.pairTestSnd i j).left :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The base change of the overlap. -/
abbrev pairX (i j : t.I) : AlgebraicSpaces B S hS := s.baseChange (t.pairTest i j)

/-- The base change of the first projection of the overlap. -/
abbrev pairXFst (i j : t.I) : t.pairX i j ⟶ t.Y' i := baseChangeMap s.f (t.pairTestFst i j)

/-- The base change of the second projection of the overlap. -/
abbrev pairXSnd (i j : t.I) : t.pairX i j ⟶ t.Y' j := baseChangeMap s.f (t.pairTestSnd i j)

/-- The morphism `X_{U i ×_T U j} ⟶ U i ×_T U j` followed by the first projection is the base
change of the first projection followed by `X_{U i} ⟶ U i`. -/
theorem pairG_fst (i j : t.I) :
    (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫ pairFst B S hS t.Y t.fY i j =
      t.pairXFst i j ≫ t.hh i := by
  rw [Category.assoc, pairIso_hom_fst]
  exact (baseChangeMap_comp_inclusion s.f (t.pairTestFst i j)).symm

/-- The morphism `X_{U i ×_T U j} ⟶ U i ×_T U j` followed by the second projection is the base
change of the second projection followed by `X_{U j} ⟶ U j`. -/
theorem pairG_snd (i j : t.I) :
    (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫ pairSnd B S hS t.Y t.fY i j =
      t.pairXSnd i j ≫ t.hh j := by
  rw [Category.assoc, pairIso_hom_snd]
  exact (baseChangeMap_comp_inclusion s.f (t.pairTestSnd i j)).symm

/-- The base changes of the two projections of the overlap agree after composition to
`X_T`. -/
theorem pairXFst_comp (i j : t.I) : t.pairXFst i j ≫ t.f' i = t.pairXSnd i j ≫ t.f' j := by
  rw [← baseChangeMap_comp, ← baseChangeMap_comp, t.pairTestFst_comp]

/-- The inverse image along `X_{U i ×_T U j} ⟶ U i ×_T U j`, for the overlap as a test scheme,
is bijective on morphisms into invertible modules, under the hypothesis of Stacks 0D27. -/
theorem bijective_baseChangeInclusion_pairTest (h : s.StructureSheafMapIso) (i j : t.I)
    (P N : Modules.{u, u} B S hS (s.baseSpaceAt (t.pairTest i j)).1
      (s.baseSpaceAt (t.pairTest i j)).2)
    (hN : IsInvertibleModule (s.baseSpaceAt (t.pairTest i j)) N) :
    Function.Bijective (fun φ : P ⟶ N ↦
        (modulePullback B S hS (baseChangeInclusion s.f (t.pairTest i j))).map φ) :=
  bijective_modulePullback_map_of_isInvertibleModule
      (baseChangeInclusion s.f (t.pairTest i j)) (h (t.pairTest i j)) P hN

/-- **The inverse image along `X_{U i ×_T U j} ⟶ U i ×_T U j` is bijective on morphisms into
invertible modules**, under the hypothesis of Stacks 0D27. -/
theorem bijective_pairG (h : s.StructureSheafMapIso) (i j : t.I)
    (P N : Modules.{u, u} B S hS (pair B S hS t.Y t.fY i j).1 (pair B S hS t.Y t.fY i j).2)
    (hN : IsInvertibleModule (pair B S hS t.Y t.fY i j) N) :
    Function.Bijective (fun φ : P ⟶ N ↦ (modulePullback B S hS
      (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)).map φ) :=
  bijective_modulePullback_map_comp_iso (baseChangeInclusion s.f (t.pairTest i j))
    (t.pairIso i j) (t.bijective_baseChangeInclusion_pairTest h i j) P N hN

/-! ### The transition isomorphisms -/

/-- The trivialization of `L` on `X_{U i}`, read as an identification of the inverse image of
the structure sheaf of `U i` with the inverse image of `L`. -/
def β (i : t.I) : (modulePullback B S hS (t.hh i)).obj (structureModule (t.Y i)) ≅
    (modulePullback B S hS (t.f' i)).obj L :=
  modulePullbackUnitIso B S hS (t.hh i) ≪≫ (t.triv i).symm

/-- The ratio of two trivializations of `L` read on an algebraic space mapping to two members of
the base-changed family over the same morphism to `X_T`. -/
def ρ {Z : AlgebraicSpaces B S hS} {i j : t.I} (ai : Z ⟶ t.Y' i) (aj : Z ⟶ t.Y' j)
    (hk : ai ≫ t.f' i = aj ≫ t.f' j) :
    (modulePullback B S hS ai).obj
        ((modulePullback B S hS (t.hh i)).obj (structureModule (t.Y i))) ≅
      (modulePullback B S hS aj).obj
        ((modulePullback B S hS (t.hh j)).obj (structureModule (t.Y j))) :=
  (modulePullback B S hS ai).mapIso (t.β i) ≪≫
    canonicalComparison ai aj (t.f' i) (t.f' j) hk L ≪≫
    ((modulePullback B S hS aj).mapIso (t.β j)).symm

/-- The ratio of two trivializations is compatible with further pullback. -/
theorem modulePullback_mapIso_ρ {Z Z' : AlgebraicSpaces B S hS} {i j : t.I} (ai : Z ⟶ t.Y' i)
    (aj : Z ⟶ t.Y' j) (hk : ai ≫ t.f' i = aj ≫ t.f' j) (r : Z' ⟶ Z) :
    (modulePullback B S hS r).mapIso (t.ρ ai aj hk) =
      (pullbackComparison B S hS r ai (r ≫ ai) rfl _).symm ≪≫
        t.ρ (r ≫ ai) (r ≫ aj) ((Category.assoc _ _ _).trans
          ((congrArg (r ≫ ·) hk).trans (Category.assoc _ _ _).symm)) ≪≫
        pullbackComparison B S hS r aj (r ≫ aj) rfl _ := by
  simp only [ρ, Functor.mapIso_trans, Functor.mapIso_symm]
  rw [modulePullback_mapIso_mapIso B S hS r ai (r ≫ ai) rfl (t.β i),
    modulePullback_mapIso_mapIso B S hS r aj (r ≫ aj) rfl (t.β j),
    modulePullback_mapIso_canonicalComparison B S hS r ai aj (t.f' i) (t.f' j) hk (r ≫ ai)
      (r ≫ aj) rfl rfl (by simp [hk]) L]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc]

/-- Two ratios compose to the ratio of the outer trivializations. -/
theorem ρ_trans {Z : AlgebraicSpaces B S hS} {i j k : t.I} (ai : Z ⟶ t.Y' i) (aj : Z ⟶ t.Y' j)
    (ak : Z ⟶ t.Y' k) (hij : ai ≫ t.f' i = aj ≫ t.f' j) (hjk : aj ≫ t.f' j = ak ≫ t.f' k) :
    t.ρ ai aj hij ≪≫ t.ρ aj ak hjk = t.ρ ai ak (hij.trans hjk) := by
  simp only [ρ, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc (canonicalComparison ai aj _ _ hij L), canonicalComparison_trans]

/-- Two ratios compose to the ratio of the outer trivializations, followed by an arbitrary
isomorphism. -/
theorem ρ_trans_assoc {Z : AlgebraicSpaces B S hS} {i j k : t.I} (ai : Z ⟶ t.Y' i)
    (aj : Z ⟶ t.Y' j) (ak : Z ⟶ t.Y' k) (hij : ai ≫ t.f' i = aj ≫ t.f' j)
    (hjk : aj ≫ t.f' j = ak ≫ t.f' k) {M : Modules.{u, u} B S hS Z.1 Z.2}
    (e : (modulePullback B S hS ak).obj
      ((modulePullback B S hS (t.hh k)).obj (structureModule (t.Y k))) ≅ M) :
    t.ρ ai aj hij ≪≫ t.ρ aj ak hjk ≪≫ e = t.ρ ai ak (hij.trans hjk) ≪≫ e := by
  rw [← Iso.trans_assoc, ρ_trans]

/-- The pairwise isomorphism on the base change of the overlap: the ratio of the two
trivializations, read through the comparisons of iterated inverse images. -/
def σ (i j : t.I) :
    (modulePullback B S hS (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)).obj
        ((modulePullback B S hS (pairFst B S hS t.Y t.fY i j)).obj (structureModule (t.Y i))) ≅
      (modulePullback B S hS (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)).obj
        ((modulePullback B S hS (pairSnd B S hS t.Y t.fY i j)).obj (structureModule (t.Y j))) :=
  (pullbackComparison B S hS _ (pairFst B S hS t.Y t.fY i j) _ rfl _).symm ≪≫
    pullbackComparison B S hS (t.pairXFst i j) (t.hh i) _ (t.pairG_fst i j).symm _ ≪≫
    t.ρ (t.pairXFst i j) (t.pairXSnd i j) (t.pairXFst_comp i j) ≪≫
    (pullbackComparison B S hS (t.pairXSnd i j) (t.hh j) _ (t.pairG_snd i j).symm _).symm ≪≫
    pullbackComparison B S hS _ (pairSnd B S hS t.Y t.fY i j) _ rfl _

/-- The inverse image of the structure sheaf of `U i` along the first projection of the overlap
is invertible. -/
theorem isInvertibleModule_pairFst (i j : t.I) :
    IsInvertibleModule (pair B S hS t.Y t.fY i j)
      ((modulePullback B S hS (pairFst B S hS t.Y t.fY i j)).obj (structureModule (t.Y i))) :=
  modulePullbackInvertible _ _ (isInvertibleModule_structureModule _)

/-- The inverse image of the structure sheaf of `U j` along the second projection of the overlap
is invertible. -/
theorem isInvertibleModule_pairSnd (i j : t.I) :
    IsInvertibleModule (pair B S hS t.Y t.fY i j)
      ((modulePullback B S hS (pairSnd B S hS t.Y t.fY i j)).obj (structureModule (t.Y j))) :=
  modulePullbackInvertible _ _ (isInvertibleModule_structureModule _)

/-- **The transition isomorphism of the descent datum on the test scheme**: the unique
isomorphism of the two inverse images of the structure sheaves to `U i ×_T U j` whose inverse
image to the base change of the overlap is the ratio of the two trivializations. -/
def τ (h : s.StructureSheafMapIso) (i j : t.I) :
    (modulePullback B S hS (pairFst B S hS t.Y t.fY i j)).obj (structureModule (t.Y i)) ≅
      (modulePullback B S hS (pairSnd B S hS t.Y t.fY i j)).obj (structureModule (t.Y j)) :=
  (modulePullback B S hS
      (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)).isoOfMapBijective
    (t.bijective_pairG h i j _ _ (t.isInvertibleModule_pairSnd i j))
    (t.bijective_pairG h i j _ _ (t.isInvertibleModule_pairFst i j))
    (t.bijective_pairG h i j _ _ (t.isInvertibleModule_pairFst i j)).1
    (t.bijective_pairG h i j _ _ (t.isInvertibleModule_pairSnd i j)).1 (t.σ i j)

/-- The inverse image of the transition isomorphism to the base change of the overlap is the
pairwise isomorphism `σ`. -/
theorem mapIso_τ (h : s.StructureSheafMapIso) (i j : t.I) :
    (modulePullback B S hS
        (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)).mapIso (t.τ h i j) =
      t.σ i j :=
  Functor.mapIso_isoOfMapBijective _ _ _ _ _ _

/-! ### Reading the transition isomorphisms on a test space -/

/-- The family of structure sheaves of the members of the family. -/
abbrev O : ∀ i, Modules.{u, u} B S hS (t.Y i).1 (t.Y i).2 := fun i ↦ structureModule (t.Y i)

/-- The transition isomorphism read on the base change of the overlap is the ratio of the two
trivializations. -/
theorem transitionOn_τ_pairX (h : s.StructureSheafMapIso) (i j : t.I) :
    transitionOn B S hS t.Y t.fY t.O (t.τ h) i j
        (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)
        ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
          pairFst B S hS t.Y t.fY i j)
        ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
          pairSnd B S hS t.Y t.fY i j)
        rfl rfl =
      pullbackComparison B S hS (t.pairXFst i j) (t.hh i) _ (t.pairG_fst i j).symm _ ≪≫
        t.ρ (t.pairXFst i j) (t.pairXSnd i j) (t.pairXFst_comp i j) ≪≫
        (pullbackComparison B S hS (t.pairXSnd i j) (t.hh j) _ (t.pairG_snd i j).symm _).symm := by
  rw [transitionOn, mapIso_τ, σ]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- The transition isomorphism read on a test space mapping to the base change of the overlap is
the ratio of the two trivializations read there. -/
theorem transitionOn_τ_comp (h : s.StructureSheafMapIso) {Z : AlgebraicSpaces B S hS}
    (i j : t.I) (r : Z ⟶ t.pairX i j) :
    transitionOn B S hS t.Y t.fY t.O (t.τ h) i j
        (r ≫ (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom))
        (r ≫ ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
          pairFst B S hS t.Y t.fY i j))
        (r ≫ ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
          pairSnd B S hS t.Y t.fY i j))
        (Category.assoc _ _ _) (Category.assoc _ _ _) =
      pullbackComparison B S hS (r ≫ t.pairXFst i j) (t.hh i) _
          (by rw [Category.assoc, ← t.pairG_fst i j]) _ ≪≫
        t.ρ (r ≫ t.pairXFst i j) (r ≫ t.pairXSnd i j)
          ((Category.assoc _ _ _).trans
            ((congrArg (r ≫ ·) (t.pairXFst_comp i j)).trans (Category.assoc _ _ _).symm)) ≪≫
        (pullbackComparison B S hS (r ≫ t.pairXSnd i j) (t.hh j) _
          (by rw [Category.assoc, ← t.pairG_snd i j]) _).symm := by
  have hc := transitionOn_comp B S hS t.Y t.fY t.O (t.τ h) r i j
    (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom)
    ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫ pairFst B S hS t.Y t.fY i j)
    ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
      pairSnd B S hS t.Y t.fY i j) rfl rfl
  rw [transitionOn_τ_pairX] at hc
  simp only [Functor.mapIso_trans, Functor.mapIso_symm] at hc
  rw [modulePullback_mapIso_pullbackComparison B S hS r (t.pairXFst i j) (t.hh i) _
      (t.pairG_fst i j).symm (r ≫ t.pairXFst i j) rfl _
      (by rw [Category.assoc, ← t.pairG_fst i j]) rfl,
    modulePullback_mapIso_pullbackComparison B S hS r (t.pairXSnd i j) (t.hh j) _
      (t.pairG_snd i j).symm (r ≫ t.pairXSnd i j) rfl _
      (by rw [Category.assoc, ← t.pairG_snd i j]) rfl,
    modulePullback_mapIso_ρ] at hc
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc] at hc
  rw [pullbackComparison_rfl, pullbackComparison_rfl] at hc
  simp only [Iso.symm_symm_eq] at hc
  apply Iso.eq_of_conj ((modulePullbackCompIso B S hS r
      ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
        pairFst B S hS t.Y t.fY i j)).app (t.O i))
    ((modulePullbackCompIso B S hS r
      ((baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) ≫
        pairSnd B S hS t.Y t.fY i j)).app (t.O j))
  simp only [Iso.trans_assoc]
  exact hc.symm

/-- The inverse of the identification of the overlaps is compatible with the first
projections. -/
@[reassoc (attr := simp)]
theorem pairIso_inv_fst (i j : t.I) :
    (t.pairIso i j).inv ≫ (schemeSpaceFunctor B S hS).map (t.pairTestFst i j).left =
      pairFst B S hS t.Y t.fY i j := by
  rw [← pairIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The inverse of the identification of the overlaps is compatible with the second
projections. -/
@[reassoc (attr := simp)]
theorem pairIso_inv_snd (i j : t.I) :
    (t.pairIso i j).inv ≫ (schemeSpaceFunctor B S hS).map (t.pairTestSnd i j).left =
      pairSnd B S hS t.Y t.fY i j := by
  rw [← pairIso_hom_snd, Iso.inv_hom_id_assoc]

/-- A morphism to the overlap of the represented spaces, together with lifts of its two legs to
the base changes over a common morphism to `X_T`, lifts to the base change of the overlap. -/
theorem exists_lift_pairX {Z : AlgebraicSpaces B S hS} {i j : t.I} (ai : Z ⟶ t.Y' i)
    (aj : Z ⟶ t.Y' j) (hk : ai ≫ t.f' i = aj ≫ t.f' j) (v : Z ⟶ pair B S hS t.Y t.fY i j)
    (hai : ai ≫ t.hh i = v ≫ pairFst B S hS t.Y t.fY i j)
    (haj : aj ≫ t.hh j = v ≫ pairSnd B S hS t.Y t.fY i j) :
    ∃ r : Z ⟶ t.pairX i j, r ≫ t.pairXFst i j = ai ∧ r ≫ t.pairXSnd i j = aj ∧
      r ≫ (baseChangeInclusion s.f (t.pairTest i j) ≫ (t.pairIso i j).hom) = v := by
  have hsq := isPullback_baseChangeMap s.f (t.pairTestFst i j ≫ t.g i)
  have hw : (ai ≫ t.f' i) ≫ baseChangeInclusion s.f T =
      (v ≫ (t.pairIso i j).inv) ≫
        (schemeSpaceFunctor B S hS).map (t.pairTestFst i j ≫ t.g i).left := by
    rw [Category.assoc, t.f'_comp_inclusion, ← Category.assoc, hai, CostructuredArrow.comp_left,
      Functor.map_comp]
    simp only [Category.assoc, pairIso_inv_fst_assoc]
  refine ⟨hsq.lift _ _ hw, ?_, ?_, ?_⟩
  · refine baseChange_hom_ext s.f ?_ ?_
    · rw [Category.assoc, baseChangeMap_comp_projection, ← baseChangeMap_comp_projection s.f
        (t.pairTestFst i j ≫ t.g i), ← Category.assoc, hsq.lift_fst, Category.assoc,
        baseChangeMap_comp_projection]
    · rw [Category.assoc, baseChangeMap_comp_inclusion, ← Category.assoc, hsq.lift_snd,
        Category.assoc, pairIso_inv_fst, hai]
  · refine baseChange_hom_ext s.f ?_ ?_
    · rw [Category.assoc, baseChangeMap_comp_projection, ← baseChangeMap_comp_projection s.f
        (t.pairTestFst i j ≫ t.g i), ← Category.assoc, hsq.lift_fst, hk, Category.assoc,
        baseChangeMap_comp_projection]
    · rw [Category.assoc, baseChangeMap_comp_inclusion, ← Category.assoc, hsq.lift_snd,
        Category.assoc, pairIso_inv_snd, haj]
  · rw [← Category.assoc, hsq.lift_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The transition isomorphism read on any test space** carrying lifts of its two legs to the
base changes over a common morphism to `X_T` is the ratio of the two trivializations read
there. -/
theorem transitionOn_τ (h : s.StructureSheafMapIso) {Z : AlgebraicSpaces B S hS} {i j : t.I}
    (ai : Z ⟶ t.Y' i) (aj : Z ⟶ t.Y' j) (hk : ai ≫ t.f' i = aj ≫ t.f' j)
    (v : Z ⟶ pair B S hS t.Y t.fY i j) (vi : Z ⟶ t.Y i) (vj : Z ⟶ t.Y j)
    (hvi : v ≫ pairFst B S hS t.Y t.fY i j = vi) (hvj : v ≫ pairSnd B S hS t.Y t.fY i j = vj)
    (hai : ai ≫ t.hh i = vi) (haj : aj ≫ t.hh j = vj) :
    transitionOn B S hS t.Y t.fY t.O (t.τ h) i j v vi vj hvi hvj =
      pullbackComparison B S hS ai (t.hh i) vi hai _ ≪≫ t.ρ ai aj hk ≪≫
        (pullbackComparison B S hS aj (t.hh j) vj haj _).symm := by
  obtain ⟨r, hr₁, hr₂, hr⟩ := t.exists_lift_pairX ai aj hk v (hai.trans hvi.symm)
    (haj.trans hvj.symm)
  subst hr₁ hr₂ hr
  rw [Category.assoc] at hvi hvj
  subst hvi hvj
  exact t.transitionOn_τ_comp h i j r

/-! ### The descent datum -/

/-- **The cocycle condition for the transition isomorphisms.**  After pullback to the base change
along `X_T ⟶ T` each transition isomorphism is a ratio of two trivializations of the same
module, so the cocycle condition holds there; and that pullback is faithful on morphisms into
invertible modules. -/
theorem τ_cocycle (h : s.StructureSheafMapIso) (i j k : t.I) (Z : AlgebraicSpaces B S hS)
    (vi : Z ⟶ t.Y i) (vj : Z ⟶ t.Y j) (vk : Z ⟶ t.Y k)
    (vij : Z ⟶ pair B S hS t.Y t.fY i j) (vjk : Z ⟶ pair B S hS t.Y t.fY j k)
    (vik : Z ⟶ pair B S hS t.Y t.fY i k)
    (hij₀ : vij ≫ pairFst B S hS t.Y t.fY i j = vi)
    (hij₁ : vij ≫ pairSnd B S hS t.Y t.fY i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS t.Y t.fY j k = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS t.Y t.fY j k = vk)
    (hik₀ : vik ≫ pairFst B S hS t.Y t.fY i k = vi)
    (hik₁ : vik ≫ pairSnd B S hS t.Y t.fY i k = vk) :
    transitionOn B S hS t.Y t.fY t.O (t.τ h) i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS t.Y t.fY t.O (t.τ h) j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS t.Y t.fY t.O (t.τ h) i k vik vi vk hik₀ hik₁ := by
  have hzj : vj ≫ t.fY j = vi ≫ t.fY i := by
    rw [← hij₀, ← hij₁, Category.assoc, Category.assoc, pair_condition]
  have hzk : vk ≫ t.fY k = vi ≫ t.fY i := by
    rw [← hzj, ← hjk₀, ← hjk₁, Category.assoc, Category.assoc, pair_condition]
  have hlift : ∀ (l : t.I) (vl : Z ⟶ t.Y l), vl ≫ t.fY l = vi ≫ t.fY i →
      ∃ r : bcSpace (vi ≫ t.fY i) ⟶ t.Y' l, r ≫ t.f' l = bcSnd (vi ≫ t.fY i) ∧
        r ≫ t.hh l = bcFst (vi ≫ t.fY i) ≫ vl := fun l vl hl ↦
    ⟨(isPullback_baseChangeMap s.f (t.g l)).lift (bcSnd (vi ≫ t.fY i)) (bcFst (vi ≫ t.fY i) ≫ vl)
      (by rw [Category.assoc, hl, bc_condition]),
      (isPullback_baseChangeMap s.f (t.g l)).lift_fst _ _ _,
      (isPullback_baseChangeMap s.f (t.g l)).lift_snd _ _ _⟩
  obtain ⟨ri, hri₁, hri₂⟩ := hlift i vi rfl
  obtain ⟨rj, hrj₁, hrj₂⟩ := hlift j vj hzj
  obtain ⟨rk, hrk₁, hrk₂⟩ := hlift k vk hzk
  apply Iso.ext
  refine s.modulePullback_bcFst_map_injective h (vi ≫ t.fY i)
    (modulePullbackInvertible vk _ (isInvertibleModule_structureModule _)) _ _ ?_
  have key : (modulePullback B S hS (bcFst (vi ≫ t.fY i))).mapIso
      (transitionOn B S hS t.Y t.fY t.O (t.τ h) i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS t.Y t.fY t.O (t.τ h) j k vjk vj vk hjk₀ hjk₁) =
      (modulePullback B S hS (bcFst (vi ≫ t.fY i))).mapIso
        (transitionOn B S hS t.Y t.fY t.O (t.τ h) i k vik vi vk hik₀ hik₁) := by
    rw [Functor.mapIso_trans, transitionOn_comp, transitionOn_comp, transitionOn_comp,
      t.transitionOn_τ h ri rj (hri₁.trans hrj₁.symm) _ _ _ _ _ hri₂ hrj₂,
      t.transitionOn_τ h rj rk (hrj₁.trans hrk₁.symm) _ _ _ _ _ hrj₂ hrk₂,
      t.transitionOn_τ h ri rk (hri₁.trans hrk₁.symm) _ _ _ _ _ hri₂ hrk₂]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
    rw [ρ_trans_assoc]
  exact congrArg Iso.hom key

/-- **The descent datum on the test scheme** attached to a trivialization of `L` along a
covering family: the structure sheaves of the members, glued by the transition
isomorphisms `τ`. -/
abbrev descentDatum (h : s.StructureSheafMapIso) : DescentDatum B S hS t.Y t.fY where
  F := t.O
  quasicoherent _ := isQuasicoherentOnSite_of_isInvertibleModule _ _
    (isInvertibleModule_structureModule _)
  transition := t.τ h
  cocycle := t.τ_cocycle h

end LocalTrivialization

end PicardSituation

end AlgebraicGeometry.Space

end
