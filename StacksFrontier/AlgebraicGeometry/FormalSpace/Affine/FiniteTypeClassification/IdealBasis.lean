module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Ideal bases and finite type algebra systems

This file defines the fundamental systems of weak ideals of definition `IdealBasis` and the
inverse systems of finite type algebras `FiniteTypeAlgebraSystem` of **Stacks 0AL1**, together
with the general facts on cartesian diagrams over a colimit, the functor from an ideal basis to
the canonical weak ideal index and its finality, and the thickenings between the spectra of the
quotients and of the stages of a system. It is part of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open CartesianColimit

universe u v w

/-- A fundamental system of weak ideals of definition, indexed so that later
indices correspond to smaller ideals. -/
structure IdealBasis (A : Type u) [CommRing A] [TopologicalSpace A]
    (I : Type v) [Preorder I] where
  /-- The ideal at index `i`. -/
  ideal : I → Ideal A
  /-- Each ideal of the family is a weak ideal of definition. -/
  weak : ∀ i, TopologicalRing.IsWeakIdealOfDefinition (ideal i)
  /-- Later indices give smaller ideals. -/
  antitone : ∀ ⦃i j⦄, i ≤ j → ideal j ≤ ideal i
  /-- Every weak ideal of definition contains an ideal of the family. -/
  cofinal : ∀ K : Ideal A, TopologicalRing.IsWeakIdealOfDefinition K →
    ∃ i, ideal i ≤ K

/-- An inverse system of finite type algebras over the quotients of a weak
ideal basis, with each transition given by reduction modulo the earlier ideal. -/
structure FiniteTypeAlgebraSystem
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (I : Type v) [Preorder I] (J : IdealBasis A I) where
  /-- The inverse system of rings. -/
  B : Iᵒᵖ ⥤ CommRingCat.{u}
  /-- The structure homomorphism from `A ⧸ J.ideal i` to the ring at index `i`. -/
  algebraMap : ∀ i : I, A ⧸ J.ideal i →+* B.obj (Opposite.op i)
  /-- Each ring of the system is of finite type over `A ⧸ J.ideal i`. -/
  finiteType : ∀ i, (algebraMap i).FiniteType
  /-- The transition maps are compatible with the structure homomorphisms and the reductions
  `A ⧸ J.ideal j → A ⧸ J.ideal i`. -/
  compatible : ∀ ⦃i j : I⦄ (h : i ≤ j),
    ((B.map (homOfLE h).op).hom).comp (algebraMap j) =
      (algebraMap i).comp
        (Ideal.Quotient.factor (J.antitone h))
  /-- The transition maps are surjective. -/
  transition_surjective : ∀ ⦃i j : I⦄ (h : i ≤ j),
    Function.Surjective ((B.map (homOfLE h).op).hom)
  /-- The kernel of the transition map from index `j` to index `i ≤ j` is generated by the image of
  `J.ideal i`. -/
  transition_ker : ∀ ⦃i j : I⦄ (h : i ≤ j),
    RingHom.ker ((B.map (homOfLE h).op).hom) =
      (J.ideal i).map ((algebraMap j).comp (Ideal.Quotient.mk (J.ideal j)))

namespace FiniteTypeAlgebraSystem

private abbrev librarySite (B : AlgebraicGeometry.BigFppfSite.{u}) :
    AlgebraicGeometry.BigFppfSite.{u} where
  initialSchemes := B.initialSchemes
  initialSchemes_small := B.initialSchemes_small
  cutoff := B.cutoff
  aleph0_lt_cutoff := B.aleph0_lt_cutoff
  cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
  aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
  initialSchemes_mem := B.initialSchemes_mem
  initialCoverings := B.initialCoverings
  initialCoverings_small := B.initialCoverings_small
  initialCoverings_supported := B.initialCoverings_supported
  coveringBound := B.coveringBound
  coveringOrdinal := B.coveringOrdinal
  coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
  initialCoverings_mem := B.initialCoverings_mem
  coverings_isSite := B.coverings_isSite
  fppf_has_representative := B.fppf_has_representative

private theorem librarySite_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    BigFppfOver.topology (librarySite B) S hS = AlgebraicGeometry.BigFppfOver.topology B S hS := rfl

/-- Maps over the base colimit lift uniquely through cartesian stage squares. -/
private theorem existsUnique_natTrans_of_colimitHom
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J C] {F G H : J ⥤ C}
    (α : F ⟶ H) (β : G ⟶ H)
    (hβ : ∀ i, IsPullback (colimit.ι G i) (β.app i)
      (colim.map β) (colimit.ι H i))
    (f : colimit F ⟶ colimit G) (hf : f ≫ colim.map β = colim.map α) :
    ∃! γ : F ⟶ G, γ ≫ β = α ∧ colim.map γ = f := by
  let γ : F ⟶ G :=
    { app := fun i => (hβ i).lift (colimit.ι F i ≫ f) (α.app i) (by
        rw [Category.assoc, hf, colimit.ι_map])
      naturality := fun i j g => by
        apply (hβ j).hom_ext
        · simp only [Category.assoc, IsPullback.lift_fst, colimit.w_assoc]
          rw [colimit.w, IsPullback.lift_fst]
        · simp only [Category.assoc, IsPullback.lift_snd]
          rw [β.naturality, IsPullback.lift_snd_assoc, α.naturality] }
  have hγ : γ ≫ β = α := by
    ext i
    exact (hβ i).lift_snd _ _ _
  have hcolim : colim.map γ = f := by
    apply colimit.hom_ext
    intro i
    rw [colimit.ι_map]
    exact (hβ i).lift_fst _ _ _
  refine ⟨γ, ⟨hγ, hcolim⟩, ?_⟩
  intro δ hδ
  apply NatTrans.ext
  funext i
  apply (hβ i).hom_ext
  · rw [← colimit.ι_map, hδ.2]
    exact ((hβ i).lift_fst _ _ _).symm
  · have hi := congrArg (fun t : F ⟶ H => t.app i) hδ.1
    exact hi.trans ((hβ i).lift_snd _ _ _).symm

private theorem overColimit_map_bijective
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J C] {H : J ⥤ C} (F G : Over H)
    (hG : ∀ i, IsPullback (colimit.ι G.left i) (G.hom.app i)
      (colim.map G.hom) (colimit.ι H i)) :
    Function.Bijective ((Over.post colim).map : (F ⟶ G) → _) := by
  constructor
  · intro f g h
    have hf : f.left ≫ G.hom = F.hom := Over.w f
    have hg : g.left ≫ G.hom = F.hom := Over.w g
    have hc : colim.map f.left ≫ colim.map G.hom = colim.map F.hom := by
      rw [← colim.map_comp, hf]
    obtain ⟨γ, hγ, huniq⟩ :=
      existsUnique_natTrans_of_colimitHom F.hom G.hom hG (colim.map f.left) hc
    exact Over.OverMorphism.ext <| (huniq f.left ⟨hf, rfl⟩).trans
      (huniq g.left ⟨hg, (congrArg (fun k => k.left) h).symm⟩).symm
  · intro f
    obtain ⟨γ, hγ, _⟩ :=
      existsUnique_natTrans_of_colimitHom F.hom G.hom hG f.left (Over.w f)
    exact ⟨Over.homMk γ hγ.1, Over.OverMorphism.ext hγ.2⟩

theorem overColimit_comp_full
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J C] {H : J ⥤ C}
    {D : Type*} [Category D] (T : D ⥤ Over H) [T.Full]
    (hT : ∀ X i, IsPullback (colimit.ι (T.obj X).left i) ((T.obj X).hom.app i)
      (colim.map (T.obj X).hom) (colimit.ι H i)) :
    (T ⋙ Over.post colim).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (overColimit_map_bijective (T.obj X) (T.obj Y) (hT Y)).2 f
    obtain ⟨h, hh⟩ := T.map_surjective g
    exact ⟨h, by change (Over.post colim).map (T.map h) = f; rw [hh, hg]⟩

theorem overColimit_comp_faithful
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J C] {H : J ⥤ C}
    {D : Type*} [Category D] (T : D ⥤ Over H) [T.Faithful]
    (hT : ∀ X i, IsPullback (colimit.ι (T.obj X).left i) ((T.obj X).hom.app i)
      (colim.map (T.obj X).hom) (colimit.ι H i)) :
    (T ⋙ Over.post colim).Faithful where
  map_injective {X Y} _f _g h := T.map_injective
    ((overColimit_map_bijective (T.obj X) (T.obj Y) (hT Y)).1 h)

theorem pullbackCocone_equifibered
    {J : Type w} [Category J] {C : Type u} [Category.{v} C]
    [HasPullbacks C] {H : J ⥤ C} (c : Cocone H) {Y : C} (f : Y ⟶ c.pt) :
    (pullback.fst c.ι ((Functor.const J).map f)).Equifibered := by
  let α := pullback.fst c.ι ((Functor.const J).map f)
  let β := pullback.snd c.ι ((Functor.const J).map f)
  have hp (i : J) : IsPullback (α.app i) (β.app i) (c.ι.app i) f :=
    (IsPullback.of_hasPullback c.ι ((Functor.const J).map f)).map
      ((evaluation J C).obj i)
  intro i j g
  apply IsPullback.of_right (p := α.naturality g) (t := (hp j).flip)
  have hb : (pullback c.ι ((Functor.const J).map f)).map g ≫ β.app j = β.app i :=
    (β.naturality g).trans (Category.comp_id _)
  simpa only [hb, c.w g] using (hp i).flip

/-- Cartesian diagrams over a connected exact colimit recover the slice category. -/
private noncomputable def cartesianDiagramColimitEquivalence
    {J : Type w} [Category J] [IsConnected J] {C : Type u} [Category.{v} C]
    [HasPullbacks C] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (H : J ⥤ C)
    (hcart : ∀ (F : Over H), F.hom.Equifibered → ∀ i,
      IsPullback (colimit.ι F.left i) (F.hom.app i)
        (colim.map F.hom) (colimit.ι H i)) :
    ObjectProperty.FullSubcategory (fun F : Over H => F.hom.Equifibered) ≌
      Over (colimit H) := by
  let P : ObjectProperty (Over H) := fun F => F.hom.Equifibered
  let T := P.ι ⋙ Over.post colim
  have hT (F : P.FullSubcategory) (i : J) := hcart F.obj F.property i
  have : T.Full := overColimit_comp_full P.ι hT
  have : T.Faithful := overColimit_comp_faithful P.ι hT
  have : T.EssSurj := by
    constructor
    intro Y
    let c := colimit.cocone H
    let f := Y.hom
    let β := pullback.snd c.ι ((Functor.const J).map f)
    let α := pullback.fst c.ι ((Functor.const J).map f)
    let F : P.FullSubcategory :=
      ⟨Over.mk α, pullbackCocone_equifibered c f⟩
    let e : colimit (pullback c.ι ((Functor.const J).map f)) ≅ Y.left :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        ((colimit.isColimit H).pullbackOfHasExactColimitsOfShape f)
    have he (i : J) : colimit.ι _ i ≫ e.hom = β.app i :=
      colimit.comp_coconePointUniqueUpToIso_hom
        ((colimit.isColimit H).pullbackOfHasExactColimitsOfShape f) i
    have hw : e.hom ≫ f = colim.map α := by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, he, colimit.ι_map]
      exact (NatTrans.congr_app
        (pullback.condition (f := c.ι) (g := (Functor.const J).map f)) i).symm
    exact ⟨F, ⟨Over.isoMk e hw⟩⟩
  letI : T.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact T.asEquivalence

attribute [local instance] bigFppfOver_subcanonical

attribute [local instance] Sheaf.sheafifiedYoneda_full Sheaf.sheafifiedYoneda_faithful

/-- View each ideal in the chosen basis as an object of the canonical weak
ideal index from the presenting ring data. -/
def idealBasisIndex
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) (i : I) :
    WeakIdeals A :=
  OrderDual.toDual ⟨J.ideal i, J.weak i⟩

/-- The ideals in an `IdealBasis` determine a functor into the canonical
quotient presentation. -/
def idealBasisFunctor
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) :
    I ⥤ WeakIdeals A where
  obj := idealBasisIndex J
  map f := homOfLE (J.antitone f.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Cofinality of the chosen ideal basis is exactly cofinality in the
canonical weak ideal index. -/
private theorem idealBasisFunctor_cofinal
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I) :
    ∀ K : WeakIdeals A,
      ∃ i : I, K ≤ (idealBasisFunctor J).obj i := by
  intro K
  obtain ⟨i, hi⟩ := J.cofinal K.1 K.2
  exact ⟨i, hi⟩

/-- The directedness of the chosen basis upgrades its order cofinality to
categorical finality, so it preserves colimits of the canonical quotient
diagram. -/
theorem idealBasisFunctor_final
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I) : Functor.Final (idealBasisFunctor J) := by
  refine ⟨fun K => ?_⟩
  let F := idealBasisFunctor J
  have : Nonempty (StructuredArrow K F) := by
    obtain ⟨i, hi⟩ := idealBasisFunctor_cofinal J K
    exact ⟨StructuredArrow.mk (homOfLE hi)⟩
  apply zigzag_isConnected
  intro x y
  obtain ⟨k, hxk, hyk⟩ := exists_ge_ge x.right y.right
  let z : StructuredArrow K F :=
    StructuredArrow.mk (homOfLE (le_trans x.hom.le (J.antitone hxk)))
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (Or.inl ⟨(StructuredArrow.homMk (homOfLE hxk) (Subsingleton.elim _ _) : x ⟶ z)⟩))
    (Relation.ReflTransGen.single
      (Or.inr ⟨(StructuredArrow.homMk (homOfLE hyk) (Subsingleton.elim _ _) : y ⟶ z)⟩))

attribute [local instance] idealBasisFunctor_final

/-- An element of a weak ideal of definition has a power vanishing in the quotient by another. -/
private theorem exists_pow_quotient_mk_eq_zero
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (K L : Ideal A) (hK : TopologicalRing.IsWeakIdealOfDefinition K)
    (hL : TopologicalRing.IsWeakIdealOfDefinition L)
    {x : A} (hx : x ∈ K) :
    ∃ n, Ideal.Quotient.mk L x ^ n = 0 := by
  obtain ⟨n, hn⟩ := hK.2 x hx |>.exists_pow_mem_of_mem_nhds (hL.1.mem_nhds L.zero_mem)
  exact ⟨n, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hn⟩

private theorem transitionKernel_isNil
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    ∀ b, b ∈ RingHom.ker ((P.B.map (homOfLE h).op).hom) → IsNilpotent b := by
  let q : A →+* P.B.obj (Opposite.op j) :=
    (P.algebraMap j).comp (Ideal.Quotient.mk (J.ideal j))
  have hmap :
      (J.ideal i).map q ≤ (⊥ : Ideal (P.B.obj (Opposite.op j))).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change q a ∈ (⊥ : Ideal (P.B.obj (Opposite.op j))).radical
    rw [Ideal.mem_radical_iff]
    obtain ⟨n, hn⟩ := exists_pow_quotient_mk_eq_zero
      (J.ideal i) (J.ideal j) (J.weak i) (J.weak j) ha
    exact ⟨n, by simp [q, ← map_pow, hn]⟩
  intro b hb
  rw [P.transition_ker h] at hb
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hmap hb)
  exact ⟨n, Ideal.mem_bot.mp hn⟩

theorem quotient_specMap_isThickening
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {K L : Ideal A} (hK : TopologicalRing.IsWeakIdealOfDefinition K)
    (hL : TopologicalRing.IsWeakIdealOfDefinition L) (h : L ≤ K) :
    Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  apply specMap_isThickening_of_nilKernel (Ideal.Quotient.factor h)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk L a, Ideal.Quotient.factor_mk h a⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk K a = 0 at hx
    exact exists_pow_quotient_mk_eq_zero K L hK hL (Ideal.Quotient.eq_zero_iff_mem.mp hx)

theorem transition_specMap_isThickening
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    Stacks.Thickenings.IsThickening (Scheme.Spec.map ((P.B.map (homOfLE h).op).op)) :=
  specMap_isThickening_of_nilKernel
    ((P.B.map (homOfLE h).op).hom) (P.transition_surjective h)
    (transitionKernel_isNil P h)

end FiniteTypeAlgebraSystem

end AlgebraicGeometry.FormalSpace

end
