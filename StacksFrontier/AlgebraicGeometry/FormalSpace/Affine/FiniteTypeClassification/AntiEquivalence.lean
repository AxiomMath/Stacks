module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.ColimitFunctor
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The anti-equivalence of Stacks 0AL1

This file defines the category of finite type morphisms to a McQuillan affine formal algebraic
space from affine formal algebraic spaces, reindexes a finite type algebra system along a small
ideal basis, and assembles **Stacks 0AL1**, the anti-equivalence of that category with the
category of finite type algebra systems. It is part of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open CartesianColimit

universe u v w

/-- **The category (2) of Stacks 0AL1.** The category of finite type morphisms to `X` from
affine formal algebraic spaces: the full subcategory of the slice category over `X` on those
objects whose source is an affine formal algebraic space and whose structure morphism is of
finite type. Morphisms are the morphisms over `X`. -/
abbrev AffineFiniteTypeOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))) :=
  ObjectProperty.FullSubcategory (fun Y : Over X =>
    _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y.left ∧
      IsFiniteType B S hS Y.hom)

/-- Two fully faithful functors into a common category with the same essential image induce an
equivalence of their sources. -/
private noncomputable def equivalenceOfEssImage
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (G : D ⥤ E) [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    (hF : ∀ c, G.essImage (F.obj c)) (hG : ∀ d, F.essImage (G.obj d)) : C ≌ D := by
  let H := Functor.essImage.liftFunctor F G hF
  let e : H ⋙ G ≅ F := Functor.essImage.liftFunctorCompIso F G hF
  have : (H ⋙ G).Full := Functor.Full.of_iso e.symm
  have : (H ⋙ G).Faithful := Functor.Faithful.of_iso e.symm
  have : H.Full := Functor.Full.of_comp_faithful H G
  have : H.Faithful := Functor.Faithful.of_comp H G
  have : H.EssSurj := by
    constructor
    intro d
    obtain ⟨c, ⟨ec⟩⟩ := hG d
    exact ⟨c, ⟨G.preimageIso (e.app c ≪≫ ec)⟩⟩
  letI : H.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact H.asEquivalence

/-- **Stacks 0AL1** for an ideal basis whose index already lies in the universe in which the
colimit of fppf sheaves is taken. -/
private noncomputable def affineFiniteTypeOverEquivalenceSmall
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I) :
    (FiniteTypeAlgebraSystem A I J)ᵒᵖ ≌ AffineFiniteTypeOver B S hS X := by
  let F := FiniteTypeAlgebraSystem.systemColimitFunctor B S hS A J P
  let T : AffineFiniteTypeOver B S hS X ⥤ Over X := ObjectProperty.ι _
  have : F.Full := FiniteTypeAlgebraSystem.systemColimitFunctor_full B S hS A J P
  have : F.Faithful := FiniteTypeAlgebraSystem.systemColimitFunctor_faithful B S hS A J P
  have : T.Full := (ObjectProperty.fullyFaithfulι _).full
  have : T.Faithful := (ObjectProperty.fullyFaithfulι _).faithful
  apply equivalenceOfEssImage F T
  · intro Q
    let Y := (F.obj Q).left
    let f := (F.obj Q).hom
    have hrel : (MorphismProperty.inverseImage
        ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f := by
      have : FunctorToTypes.Small.{u} Y.obj :=
        FiniteTypeAlgebraSystem.systemColimit_small B S hS A hX Q.unop P
      exact FiniteTypeAlgebraSystem.affineFiniteType_relative_of_affineBaseChanges B S hS f
        (FiniteTypeAlgebraSystem.systemColimitMap_affineBaseChange B S hS A Q.unop P)
    have ha := AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine B S hS f hX
      (MorphismProperty.relative_monotone (fun _ _ _ h => h.1) _ hrel)
    let Q' : AffineFiniteTypeOver B S hS X := ⟨Over.mk f, ha,
      FiniteTypeAlgebraSystem.formalFiniteType_of_relative B S hS f hrel⟩
    exact ⟨Q', ⟨Iso.refl _⟩⟩
  · intro Y
    exact FiniteTypeAlgebraSystem.systemColimitFunctor_essImage B S hS A Y.obj.hom hX
      Y.property.1
      (FiniteTypeAlgebraSystem.isLocallyOfFiniteType_of_isFiniteType B S hS Y.property.2) J P

namespace FiniteTypeAlgebraSystem

private abbrev transition
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : i ≤ j) :
    P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i) :=
  (P.B.map (homOfLE h).op).hom

private lemma transition_comp
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (transition P hij).comp (transition P hjk) = transition P (hij.trans hjk) := by
  change (P.B.map (homOfLE hjk).op ≫ P.B.map (homOfLE hij).op).hom = _
  rw [← P.B.map_comp]
  rfl

private lemma descent_comp_transition
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j l : I}
    (t : P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i))
    (hil : i ≤ l) (hjl : j ≤ l)
    (ht : t.comp (transition P hjl) = transition P hil)
    (k : I) (hik : i ≤ k) (hjk : j ≤ k) :
    t.comp (transition P hjk) = transition P hik := by
  obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
  have hm : (t.comp (transition P hjk)).comp (transition P hkm) =
      (transition P hik).comp (transition P hkm) := by
    rw [RingHom.comp_assoc, transition_comp]
    rw [← transition_comp P hjl hlm, ← RingHom.comp_assoc, ht,
      transition_comp, transition_comp]
  exact (RingHom.cancel_right (P.transition_surjective hkm)).1 hm

private lemma exists_extendedTransition
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i) :
    ∃ t : P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i),
      ∀ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        t.comp (transition P hjk) = transition P hik := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk : RingHom.ker (transition P hjk) ≤ RingHom.ker (transition P hik) := by
    rw [P.transition_ker hjk, P.transition_ker hik]
    exact Ideal.map_mono h
  let t := (transition P hjk).liftOfSurjective (P.transition_surjective hjk)
    ⟨transition P hik, hk⟩
  have ht : t.comp (transition P hjk) = transition P hik :=
    RingHom.liftOfSurjective_comp _ _ _
  exact ⟨t, descent_comp_transition P t hik hjk ht⟩

private noncomputable def extendedTransition
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i) :
    P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i) :=
  (exists_extendedTransition P h).choose

private lemma extendedTransition_spec
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i)
    (k : I) (hik : i ≤ k) (hjk : j ≤ k) :
    (extendedTransition P h).comp (transition P hjk) = transition P hik :=
  (exists_extendedTransition P h).choose_spec k hik hjk

private lemma extendedTransition_unique
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i)
    (t : P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (ht : t.comp (transition P hjk) = transition P hik) : t = extendedTransition P h := by
  exact (RingHom.cancel_right (P.transition_surjective hjk)).1
    (ht.trans (extendedTransition_spec P h k hik hjk).symm)

private lemma extendedTransition_of_le
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : i ≤ j) :
    extendedTransition P (J.antitone h) = transition P h := by
  symm
  apply extendedTransition_unique P _ _ j h le_rfl
  exact transition_comp P h le_rfl

private lemma extendedTransition_comp
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j k : I}
    (hij : J.ideal j ≤ J.ideal i) (hjk : J.ideal k ≤ J.ideal j) :
    (extendedTransition P hij).comp (extendedTransition P hjk) =
      extendedTransition P (hjk.trans hij) := by
  obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
  obtain ⟨m, hlm, hkm⟩ := exists_ge_ge l k
  apply extendedTransition_unique P _ _ m (hil.trans hlm) hkm
  rw [RingHom.comp_assoc, extendedTransition_spec P hjk m (hjl.trans hlm) hkm,
    extendedTransition_spec]

private abbrev rootMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) (i : I) : A →+* P.B.obj (Opposite.op i) :=
  (P.algebraMap i).comp (Ideal.Quotient.mk (J.ideal i))

private lemma transition_rootMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : i ≤ j) :
    (transition P h).comp (rootMap P j) = rootMap P i := by
  rw [rootMap, ← RingHom.comp_assoc, P.compatible]
  ext x
  rfl

private lemma extendedTransition_rootMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i) :
    (extendedTransition P h).comp (rootMap P j) = rootMap P i := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [← transition_rootMap P hjk, ← RingHom.comp_assoc, extendedTransition_spec P h k hik hjk,
    transition_rootMap]

private lemma extendedTransition_surjective
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i) :
    Function.Surjective (extendedTransition P h) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  intro x
  obtain ⟨y, rfl⟩ := P.transition_surjective hik x
  exact ⟨transition P hjk y,
    congrArg (fun r : P.B.obj (Opposite.op k) →+* P.B.obj (Opposite.op i) => r y)
      (extendedTransition_spec P h k hik hjk)⟩

private lemma extendedTransition_ker
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) {i j : I} (h : J.ideal j ≤ J.ideal i) :
    RingHom.ker (extendedTransition P h) = (J.ideal i).map (rootMap P j) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [← Ideal.map_comap_of_surjective (transition P hjk) (P.transition_surjective hjk)
    (RingHom.ker (extendedTransition P h)), RingHom.comap_ker,
    extendedTransition_spec P h k hik hjk,
    P.transition_ker, Ideal.map_map, transition_rootMap]

private lemma extendedTransition_id
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) (i : I) :
    extendedTransition P (i := i) le_rfl = RingHom.id _ := by
  rw [extendedTransition_of_le P (le_refl i)]
  change (P.B.map (𝟙 (Opposite.op i))).hom = _
  rw [P.B.map_id]
  rfl

private noncomputable def reindexSystem
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {K : Type w} [Preorder K] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k)) :
    FiniteTypeAlgebraSystem A K J' where
  B :=
    { obj k := P.B.obj (Opposite.op (r k.unop))
      map f := CommRingCat.ofHom (extendedTransition P
        ((hr _).ge.trans <| (J'.antitone f.unop.le).trans (hr _).le))
      map_id k := CommRingCat.hom_ext (extendedTransition_id P _)
      map_comp f g := by
        apply CommRingCat.hom_ext
        rw [CommRingCat.hom_comp]
        exact (extendedTransition_comp P
          ((hr _).ge.trans <| (J'.antitone g.unop.le).trans (hr _).le)
          ((hr _).ge.trans <| (J'.antitone f.unop.le).trans (hr _).le)).symm }
  algebraMap k := (P.algebraMap (r k)).comp (Ideal.Quotient.factor (hr k).le)
  finiteType k := (P.finiteType (r k)).comp
    (RingHom.FiniteType.of_surjective _ (Ideal.Quotient.factor_surjective (hr k).le))
  compatible {i j} h := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with | h x =>
    exact congrArg (fun f : A →+* P.B.obj (Opposite.op (r i)) => f x)
      (extendedTransition_rootMap P ((hr _).ge.trans <| (J'.antitone h).trans (hr _).le))
  transition_surjective {i j} h := extendedTransition_surjective P
    ((hr _).ge.trans <| (J'.antitone h).trans (hr _).le)
  transition_ker {i j} h := by
    change RingHom.ker (extendedTransition P
      ((hr _).ge.trans <| (J'.antitone h).trans (hr _).le)) =
      (J'.ideal i).map (rootMap P (r j))
    rw [extendedTransition_ker, hr i]

private lemma hom_extendedTransition
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    {P Q : FiniteTypeAlgebraSystem A I J} (f : P ⟶ Q) {i j : I}
    (h : J.ideal j ≤ J.ideal i) :
    (f.nat.app (Opposite.op i)).hom.comp (extendedTransition P h) =
      (extendedTransition Q h).comp (f.nat.app (Opposite.op j)).hom := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hn (a : I) (hak : a ≤ k) :
      (f.nat.app (Opposite.op a)).hom.comp (transition P hak) =
        (transition Q hak).comp (f.nat.app (Opposite.op k)).hom :=
    congrArg CommRingCat.Hom.hom (f.nat.naturality (homOfLE hak).op)
  have he : ((f.nat.app (Opposite.op i)).hom.comp (extendedTransition P h)).comp
      (transition P hjk) =
      ((extendedTransition Q h).comp (f.nat.app (Opposite.op j)).hom).comp
        (transition P hjk) := by
    rw [RingHom.comp_assoc, extendedTransition_spec P h k hik hjk,
      RingHom.comp_assoc, hn j hjk, ← RingHom.comp_assoc,
      extendedTransition_spec Q h k hik hjk, hn i hik]
  exact (RingHom.cancel_right (P.transition_surjective hjk)).1 he

private noncomputable def reindexFunctor
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    {K : Type w} [Preorder K] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k)) :
    FiniteTypeAlgebraSystem A I J ⥤ FiniteTypeAlgebraSystem A K J' where
  obj P := reindexSystem P J' r hr
  map {P Q} f :=
    { nat :=
        { app k := by
            change P.B.obj (Opposite.op (r k.unop)) ⟶ Q.B.obj (Opposite.op (r k.unop))
            exact f.nat.app (Opposite.op (r k.unop))
          naturality i j g := by
            apply CommRingCat.hom_ext
            have hg : J.ideal (r i.unop) ≤ J.ideal (r j.unop) :=
              (hr _).ge.trans <| (J'.antitone g.unop.le).trans (hr _).le
            change (f.nat.app _).hom.comp (extendedTransition P hg) =
              (extendedTransition Q hg).comp (f.nat.app _).hom
            exact hom_extendedTransition f hg }
      base k := by
        dsimp [reindexSystem]
        exact (RingHom.comp_assoc _ _ _).symm.trans
          (congrArg (fun φ => φ.comp (Ideal.Quotient.factor (hr k).le)) (f.base (r k))) }

private lemma extendedTransition_reindex
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {K : Type w} [Preorder K] [IsDirected K (· ≤ ·)] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k))
    {i j : K} (h : J'.ideal j ≤ J'.ideal i) :
    extendedTransition (reindexSystem P J' r hr) h =
      extendedTransition P (by rw [← hr, ← hr]; exact h) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  symm
  apply extendedTransition_unique (reindexSystem P J' r hr) h _ k hik hjk
  exact extendedTransition_comp P
    ((hr _).ge.trans <| h.trans (hr _).le)
    ((hr _).ge.trans <| (J'.antitone hjk).trans (hr _).le)

private lemma reindexSystem_rootMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {K : Type w} [Preorder K] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k)) (i : K) :
    rootMap (reindexSystem P J' r hr) i = rootMap P (r i) := by
  ext x
  rfl

private noncomputable def doubleReindexHom
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    {K : Type w} [Preorder K] [IsDirected K (· ≤ ·)] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k))
    (t : I → K) (ht : ∀ i, J.ideal i = J'.ideal (t i))
    (P : FiniteTypeAlgebraSystem A I J) :
    reindexSystem (reindexSystem P J' r hr) J t ht ⟶ P where
  nat :=
    { app i := CommRingCat.ofHom
        (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge)
      naturality i j g := by
        apply CommRingCat.hom_ext
        have hg : J'.ideal (t i.unop) ≤ J'.ideal (t j.unop) :=
          (ht _).ge.trans <| (J.antitone g.unop.le).trans (ht _).le
        have hg' : J.ideal (r (t i.unop)) ≤ J.ideal (r (t j.unop)) :=
          (hr _).ge.trans <| hg.trans (hr _).le
        have key : (extendedTransition P ((ht j.unop).trans (hr (t j.unop))).ge).comp
            (extendedTransition P hg') =
            (transition P g.unop.le).comp
              (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge) := by
          rw [← extendedTransition_of_le, extendedTransition_comp, extendedTransition_comp]
        change (extendedTransition P ((ht j.unop).trans (hr (t j.unop))).ge).comp
          (extendedTransition (reindexSystem P J' r hr) hg) =
          (transition P g.unop.le).comp
            (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge)
        exact (congrArg (fun φ => (extendedTransition P
            ((ht j.unop).trans (hr (t j.unop))).ge).comp φ)
          (extendedTransition_reindex P J' r hr hg)).trans key }
  base i := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with | h x =>
    have h := extendedTransition_rootMap P ((ht i).trans (hr (t i))).ge
    exact congrArg (fun f : A →+* P.B.obj (Opposite.op i) => f x) h

private noncomputable def doubleReindexInv
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    {K : Type w} [Preorder K] [IsDirected K (· ≤ ·)] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k))
    (t : I → K) (ht : ∀ i, J.ideal i = J'.ideal (t i))
    (P : FiniteTypeAlgebraSystem A I J) :
    P ⟶ reindexSystem (reindexSystem P J' r hr) J t ht where
  nat :=
    { app i := CommRingCat.ofHom
        (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).le)
      naturality i j g := by
        apply CommRingCat.hom_ext
        have hg : J'.ideal (t i.unop) ≤ J'.ideal (t j.unop) :=
          (ht _).ge.trans <| (J.antitone g.unop.le).trans (ht _).le
        have hg' : J.ideal (r (t i.unop)) ≤ J.ideal (r (t j.unop)) :=
          (hr _).ge.trans <| hg.trans (hr _).le
        have key : (extendedTransition P ((ht j.unop).trans (hr (t j.unop))).le).comp
            (transition P g.unop.le) =
            (extendedTransition P hg').comp
              (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).le) := by
          rw [← extendedTransition_of_le, extendedTransition_comp, extendedTransition_comp]
        change (extendedTransition P ((ht j.unop).trans (hr (t j.unop))).le).comp
          (transition P g.unop.le) =
          (extendedTransition (reindexSystem P J' r hr) hg).comp
            (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).le)
        exact key.trans (congrArg (fun φ => φ.comp (extendedTransition P
            ((ht i.unop).trans (hr (t i.unop))).le))
          (extendedTransition_reindex P J' r hr hg).symm) }
  base i := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with | h x =>
    have h := extendedTransition_rootMap P ((ht i).trans (hr (t i))).le
    exact congrArg (fun f : A →+* P.B.obj (Opposite.op (r (t i))) => f x) h

private noncomputable def doubleReindexIso
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    {K : Type w} [Preorder K] [IsDirected K (· ≤ ·)] (J' : IdealBasis A K)
    (r : K → I) (hr : ∀ k, J'.ideal k = J.ideal (r k))
    (t : I → K) (ht : ∀ i, J.ideal i = J'.ideal (t i)) :
    reindexFunctor J J' r hr ⋙ reindexFunctor J' J t ht ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun P =>
    { hom := doubleReindexHom J J' r hr t ht P
      inv := doubleReindexInv J J' r hr t ht P
      hom_inv_id := by
        apply algebraSystemHom_ext
        apply NatTrans.ext
        funext i
        apply CommRingCat.hom_ext
        change (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).le).comp
          (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge) = RingHom.id _
        rw [extendedTransition_comp, extendedTransition_id]
      inv_hom_id := by
        apply algebraSystemHom_ext
        apply NatTrans.ext
        funext i
        apply CommRingCat.hom_ext
        change (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge).comp
          (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).le) = RingHom.id _
        rw [extendedTransition_comp, extendedTransition_id] }) ?_
  intro P Q f
  apply algebraSystemHom_ext
  apply NatTrans.ext
  funext i
  apply CommRingCat.hom_ext
  change (extendedTransition Q ((ht i.unop).trans (hr (t i.unop))).ge).comp
    (f.nat.app _).hom = (f.nat.app _).hom.comp
      (extendedTransition P ((ht i.unop).trans (hr (t i.unop))).ge)
  exact (hom_extendedTransition f _).symm

private abbrev smallBasisIndex
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) :=
  ULift.{u + 1} (OrderDual (Set.range J.ideal))

private noncomputable def smallBasisRepresentative
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) (k : smallBasisIndex J) : I :=
  k.down.property.choose

private lemma smallBasisRepresentative_ideal
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) (k : smallBasisIndex J) :
    J.ideal (smallBasisRepresentative J k) = k.down.val := k.down.property.choose_spec

private def smallBasisPoint
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) (i : I) : smallBasisIndex J :=
  ⟨⟨J.ideal i, i, rfl⟩⟩

private lemma smallBasisIndex_nonempty
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [Nonempty I] (J : IdealBasis A I) :
    Nonempty (smallBasisIndex J) := ⟨smallBasisPoint J (Classical.arbitrary I)⟩

private lemma smallBasisIndex_directed
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I) :
    IsDirected (smallBasisIndex J) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨i, hai, hbi⟩ := exists_ge_ge (smallBasisRepresentative J a) (smallBasisRepresentative J b)
  refine ⟨smallBasisPoint J i, ?_, ?_⟩
  · change J.ideal i ≤ a.down.val
    rw [← smallBasisRepresentative_ideal J a]
    exact J.antitone hai
  · change J.ideal i ≤ b.down.val
    rw [← smallBasisRepresentative_ideal J b]
    exact J.antitone hbi

private noncomputable def smallIdealBasis
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) : IdealBasis A (smallBasisIndex J) where
  ideal k := k.down.val
  weak k := by rw [← smallBasisRepresentative_ideal J k]; exact J.weak _
  antitone {_ _} h := h
  cofinal L hL := by
    obtain ⟨i, hi⟩ := J.cofinal L hL
    exact ⟨smallBasisPoint J i, hi⟩

private noncomputable def reindexSmallEquivalence
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I) :
    FiniteTypeAlgebraSystem A I J ≌ FiniteTypeAlgebraSystem A (smallBasisIndex J)
      (smallIdealBasis J) := by
  have : IsDirected (smallBasisIndex J) (· ≤ ·) := smallBasisIndex_directed J
  let r := smallBasisRepresentative J
  let t := smallBasisPoint J
  have hr : ∀ k, (smallIdealBasis J).ideal k = J.ideal (r k) :=
    fun k => (smallBasisRepresentative_ideal J k).symm
  have ht : ∀ i, J.ideal i = (smallIdealBasis J).ideal (t i) := fun _ => rfl
  exact CategoryTheory.Equivalence.mk
    (reindexFunctor J (smallIdealBasis J) r hr)
    (reindexFunctor (smallIdealBasis J) J t ht)
    (doubleReindexIso J (smallIdealBasis J) r hr t ht).symm
    (doubleReindexIso (smallIdealBasis J) J t ht r hr)

end FiniteTypeAlgebraSystem

/-- **Stacks 0AL1.** Let `X` be a McQuillan affine formal algebraic space over `S` presented as
the formal spectrum of a weakly admissible topological ring `A`, and let `J` be a fundamental
system of weak ideals of definition of `A`. The category of inverse systems of finite type
algebras over the quotients of `J` is anti-equivalent to the category of finite type morphisms
to `X` from affine formal algebraic spaces. -/
@[stacks 0AL1 "anti-equivalence", no_expose]
noncomputable def finiteTypeAlgebraSystemAntiEquivalence
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (_hA : TopologicalRing.IsWeaklyAdmissible A)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : HasSomeSurjectivePresentation B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I) :
    (FiniteTypeAlgebraSystem A I J)ᵒᵖ ≌ AffineFiniteTypeOver B S hS X :=
  letI : Nonempty (FiniteTypeAlgebraSystem.smallBasisIndex J) :=
    FiniteTypeAlgebraSystem.smallBasisIndex_nonempty J
  letI : IsDirected (FiniteTypeAlgebraSystem.smallBasisIndex J) (· ≤ ·) :=
    FiniteTypeAlgebraSystem.smallBasisIndex_directed J
  (FiniteTypeAlgebraSystem.reindexSmallEquivalence J).op.trans
    (affineFiniteTypeOverEquivalenceSmall B S hS A X hX.1 P
      (FiniteTypeAlgebraSystem.smallBasisIndex J)
      (FiniteTypeAlgebraSystem.smallIdealBasis J))

end AlgebraicGeometry.FormalSpace

end
