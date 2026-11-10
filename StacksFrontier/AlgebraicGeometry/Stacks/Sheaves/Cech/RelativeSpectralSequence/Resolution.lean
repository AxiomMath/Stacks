module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.InjectivePushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# The relative Čech resolution of an abelian sheaf

This file contains the first part of the construction of the relative Čech-to-cohomology
spectral sequence: the geometry of the tuples making up the relative Čech nerve of a faithful
`1`-morphism `f : 𝒰 ⥤ 𝒳` (each projection is a fibred `1`-morphism, hence continuous and
cocontinuous for the inherited topologies), the relative Čech complex as an additive functor in
the presheaf, the identification of the direct image of `H⁰` along a cocontinuous functor, and
the augmentation of an injective resolution into its sheafified relative Čech complex together
with the cohomology of its columns.

## References

* [Stacks Project, Tag 06XF](https://stacks.math.columbia.edu/tag/06XF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

section TupleGeometry


variable {U X C : Type*} [Category U] [Category X] [Category C]
  (q : X ⥤ C) (f : U ⥤ X)

/-- If a morphism of tuples lifts `β` on its target component, each of its source components lifts
`β` over `f ⋙ q`. -/
lemma tuple_source_isHomLift {n : ℕ} {x y : Tuple q f n}
    (g : x ⟶ y) (i : Fin (n + 1)) {R T : C} (β : R ⟶ T)
    [q.IsHomLift β g.target] : (f ⋙ q).IsHomLift β (g.source i) := by
  have hx := x.comparison_lift i
  have hy := y.comparison_lift i
  have he : f.map (g.source i) =
      (x.comparison i).hom ≫ g.target ≫ (y.comparison i).inv := by
    rw [← Category.assoc, ← g.comparison_naturality i, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have h : q.IsHomLift β (f.map (g.source i)) := by
    rw [he]
    have : q.IsHomLift β (g.target ≫ (y.comparison i).inv) :=
      IsHomLift.comp_lift_id_right' q β g.target (q.obj y.target) _
    exact IsHomLift.comp_lift_id_left' q (q.obj x.target) _ β _
  exact (Functor.isHomLift_comp_iff f q β _).2 h

/-- A morphism of tuples is determined by its target component and its family of source
components. -/
lemma tuple_hom_ext {n : ℕ} {x y : Tuple q f n}
    {g h : x ⟶ y} (ht : g.target = h.target) (hs : g.source = h.source) : g = h := by
  cases g
  cases h
  cases ht
  cases hs
  rfl

/-- For `f` faithful, the projection of the degree-`n` term of the relative Čech nerve of `f`
to `X` is faithful. -/
lemma tuple_projection_faithful [f.Faithful] (n : ℕ) :
    (Tuple.projection q f n).Faithful := by
  refine ⟨?_⟩
  intro x y g h he
  apply tuple_hom_ext q f he
  funext i
  apply f.map_injective
  apply (cancel_mono (y.comparison i).hom).mp
  rw [g.comparison_naturality i, h.comparison_naturality i]
  exact congrArg ((x.comparison i).hom ≫ ·) he

/-- The image under `f` of a component of a tuple lies over the common target of the tuple. -/
private lemma tuple_source_obj_eq {n : ℕ} (x : Tuple q f n) (i : Fin (n + 1)) :
    (f ⋙ q).obj (x.source i) = q.obj x.target := by
  have := x.comparison_lift i
  exact IsHomLift.domain_eq q (𝟙 _) (x.comparison i).hom

/-- A lift of `q.map δ` to a component of a tuple is cartesian after composing with the
comparison isomorphism. -/
private lemma tuple_isStronglyCartesian_of_isHomLift (hq : q.IsFiberedInGroupoids)
    {n : ℕ} (x : Tuple q f n) {R : X} (δ : R ⟶ x.target) {i : Fin (n + 1)} {w : U}
    (φ : w ⟶ x.source i) (hφ : (f ⋙ q).IsHomLift (q.map δ) φ) :
    q.IsStronglyCartesian (q.map δ) (f.map φ ≫ (x.comparison i).hom) := by
  have := (Functor.isHomLift_comp_iff f q _ φ).1 hφ
  have := x.comparison_lift i
  exact hq.isStronglyCartesian_homLift (q.map δ) _

/-- The tuple over `R` pulled back from `x` along `δ`, given lifts `φ i` of `q.map δ`. -/
private def tuplePullback (hq : q.IsFiberedInGroupoids) {n : ℕ} (x : Tuple q f n) {R : X}
    (δ : R ⟶ x.target) {w : Fin (n + 1) → U} (φ : ∀ i, w i ⟶ x.source i)
    (hφ : ∀ i, (f ⋙ q).IsHomLift (q.map δ) (φ i)) : Tuple q f n where
  target := R
  source := w
  comparison i :=
    have := hq.isStronglyCartesian δ
    have := tuple_isStronglyCartesian_of_isHomLift q f hq x δ (φ i) (hφ i)
    Functor.IsCartesian.domainUniqueUpToIso q (q.map δ) δ (f.map (φ i) ≫ (x.comparison i).hom)
  comparison_lift i := by
    have := tuple_isStronglyCartesian_of_isHomLift q f hq x δ (φ i) (hφ i)
    infer_instance

/-- The canonical morphism from `tuplePullback` to `x`, with target `δ` and components `φ`. -/
private def tuplePullbackHom (hq : q.IsFiberedInGroupoids) {n : ℕ} (x : Tuple q f n) {R : X}
    (δ : R ⟶ x.target) {w : Fin (n + 1) → U} (φ : ∀ i, w i ⟶ x.source i)
    (hφ : ∀ i, (f ⋙ q).IsHomLift (q.map δ) (φ i)) : tuplePullback q f hq x δ φ hφ ⟶ x where
  target := δ
  source := φ
  comparison_naturality i := by
    have := hq.isStronglyCartesian δ
    have := tuple_isStronglyCartesian_of_isHomLift q f hq x δ (φ i) (hφ i)
    exact (Functor.IsCartesian.fac q (q.map δ) δ (f.map (φ i) ≫ (x.comparison i).hom)).symm

/-- The projection of the degree-`n` term of the relative Čech nerve of `f` to `X` is fibred in
groupoids. -/
lemma tuple_projection_isFiberedInGroupoids
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (n : ℕ) :
    (Tuple.projection q f n).IsFiberedInGroupoids where
  exists_lift := by
    intro R T β x hx
    change x.target = T at hx
    subst T
    choose w φ hφ using fun i =>
      hp.exists_lift (q.map β) (x.source i) (tuple_source_obj_eq q f x i)
    exact ⟨_, tuplePullbackHom q f hq x β φ hφ,
      IsHomLift.map (Tuple.projection q f n) (tuplePullbackHom q f hq x β φ hφ)⟩
  unique_lift := by
    intro x y z g h β hβ
    change z.target ⟶ y.target at β
    change β ≫ g.target = h.target at hβ
    have hg (i : Fin (n + 1)) :
        (f ⋙ q).IsStronglyCartesian (q.map g.target) (g.source i) := by
      have := tuple_source_isHomLift q f g i (q.map g.target)
      exact hp.isStronglyCartesian_homLift _ _
    have hh (i : Fin (n + 1)) :
        (f ⋙ q).IsHomLift (q.map h.target) (h.source i) :=
      tuple_source_isHomLift q f h i _
    have hb : q.map h.target = q.map β ≫ q.map g.target := by
      rw [← q.map_comp, hβ]
    have hlift (i : Fin (n + 1)) : ∃! χ : z.source i ⟶ y.source i,
        (f ⋙ q).IsHomLift (q.map β) χ ∧ χ ≫ g.source i = h.source i := by
      have := hg i
      have := hh i
      exact Functor.IsStronglyCartesian.universal_property (f ⋙ q)
        (q.map g.target) (g.source i) (q.map β) (q.map h.target) hb (h.source i)
    choose χ hχ huniq using hlift
    have hχf (i : Fin (n + 1)) : q.IsHomLift (q.map β) (f.map (χ i)) := by
      have := (hχ i).1
      exact Functor.isHomLift_map_of_comp_eq rfl _ (χ i)
    have hn (i : Fin (n + 1)) :
        f.map (χ i) ≫ (y.comparison i).hom = (z.comparison i).hom ≫ β := by
      have := hχf i
      have := y.comparison_lift i
      have := z.comparison_lift i
      have := hq.isStronglyCartesian g.target
      have : q.IsHomLift (q.map β) ((z.comparison i).hom ≫ β) :=
        IsHomLift.comp_lift_id_left' q (q.obj z.target) _ (q.map β) β
      apply Functor.IsStronglyCartesian.ext q (q.map g.target) g.target (q.map β)
      rw [Category.assoc, ← g.comparison_naturality i, ← Category.assoc,
        ← f.map_comp, (hχ i).2, h.comparison_naturality i, Category.assoc, hβ]
    let k : z ⟶ y := ⟨β, χ, hn⟩
    refine ⟨k, ⟨rfl, tuple_hom_ext q f hβ (funext fun i => (hχ i).2)⟩, ?_⟩
    intro k' hk'
    change k'.target = β ∧ k' ≫ g = h at hk'
    apply tuple_hom_ext q f hk'.1
    funext i
    apply huniq i
    refine ⟨?_, ?_⟩
    · have htarget : q.IsHomLift (q.map β) k'.target := by
        rw [hk'.1]
        infer_instance
      exact tuple_source_isHomLift q f k' i _
    · exact congrArg (fun t : z ⟶ x => t.source i) hk'.2

private def tupleSource (n : ℕ) : Tuple q f n ⥤ U where
  obj x := x.source 0
  map g := g.source 0

private lemma tupleSource_faithful [f.Faithful] (n : ℕ) :
    (tupleSource q f n).Faithful where
  map_injective {x y} {g h} he := by
    change g.source 0 = h.source 0 at he
    have ht : g.target = h.target := by
      apply (cancel_epi (x.comparison 0).hom).mp
      rw [← g.comparison_naturality 0, ← h.comparison_naturality 0, he]
    apply tuple_hom_ext q f ht
    funext i
    apply f.map_injective
    apply (cancel_mono (y.comparison i).hom).mp
    rw [g.comparison_naturality i, h.comparison_naturality i, ht]

private lemma tupleSource_isFiberedInGroupoids [f.Faithful]
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (n : ℕ) :
    (tupleSource q f n).IsFiberedInGroupoids where
  exists_lift := by
    intro R T β x hx
    change x.source 0 = T at hx
    subst T
    let δ := f.map β ≫ (x.comparison 0).hom
    have hβ : (f ⋙ q).IsHomLift (q.map δ) β := by
      have := x.comparison_lift 0
      have h : q.IsHomLift (q.map δ) (f.map β) := by
        have he : f.map β = δ ≫ (x.comparison 0).inv := by simp [δ]
        rw [he]
        exact IsHomLift.comp_lift_id_right' q (q.map δ) δ (q.obj x.target) _
      exact (Functor.isHomLift_comp_iff f q _ β).2 h
    choose w' φ' hφ' using fun i : Fin n =>
      hp.exists_lift (q.map δ) (x.source i.succ) (tuple_source_obj_eq q f x i.succ)
    let w : Fin (n + 1) → U := Fin.cases R w'
    let φ : ∀ i, w i ⟶ x.source i := Fin.cases β φ'
    have hφ (i : Fin (n + 1)) : (f ⋙ q).IsHomLift (q.map δ) (φ i) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hβ
      · exact hφ' j
    exact ⟨_, tuplePullbackHom q f hq x δ φ hφ,
      IsHomLift.map (tupleSource q f n) (tuplePullbackHom q f hq x δ φ hφ)⟩
  unique_lift := by
    intro x y z g h β hβ
    change z.source 0 ⟶ y.source 0 at β
    change β ≫ g.source 0 = h.source 0 at hβ
    let δ := (z.comparison 0).inv ≫ f.map β ≫ (y.comparison 0).hom
    have hδ : δ ≫ g.target = h.target := by
      dsimp [δ]
      rw [Category.assoc, Category.assoc, ← g.comparison_naturality 0,
        ← Category.assoc (f.map β), ← f.map_comp, hβ, h.comparison_naturality 0]
      simp
    obtain ⟨k, hk, _⟩ :=
      (tuple_projection_isFiberedInGroupoids q f hp hq n).unique_lift g h δ hδ
    have ht : k.target = δ := hk.1
    have hs : k.source 0 = β := by
      apply f.map_injective
      apply (cancel_mono (y.comparison 0).hom).mp
      rw [k.comparison_naturality 0, ht]
      simp [δ]
    refine ⟨k, ⟨hs, hk.2⟩, ?_⟩
    intro k' hk'
    have := tupleSource_faithful q f n
    exact (tupleSource q f n).map_injective (hk'.1.trans hs.symm)

/-- The structure functor of the degree-`n` term of the relative Čech nerve of `f` is fibred in
groupoids over the base category. -/
lemma tuple_isFiberedInGroupoids
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (n : ℕ) :
    (Tuple.projection q f n ⋙ q).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp _ _
    (tuple_projection_isFiberedInGroupoids q f hp hq n) hq

private lemma tuple_hasEqualizers [f.Faithful] [HasEqualizers U]
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (n : ℕ) :
    HasEqualizers (Tuple q f n) := by
  have := tupleSource_faithful q f n
  exact hasEqualizers_of_faithful_isFiberedInGroupoids (tupleSource q f n)
    (tupleSource_isFiberedInGroupoids q f hp hq n)

private lemma tuple_projection_isFibredOneMorphism
    (hq : q.IsFiberedInGroupoids) (n : ℕ) :
    (Tuple.projection q f n ⋙ q).IsFibredOneMorphism q
      (Tuple.projection q f n) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro R T β x y g hg
    have := hg
    have := Functor.isHomLift_map_of_comp_eq
      (q := q) (G := Tuple.projection q f n) rfl β g
    exact hq.isStronglyCartesian_homLift β _

private lemma tuple_projection_continuous_cocontinuous [HasPullbacks C]
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (J : GrothendieckTopology C) (n : ℕ) :
    (Tuple.projection q f n).IsContinuous
        ((Tuple.projection q f n ⋙ q).inheritedTopology J) (q.inheritedTopology J) ∧
      (Tuple.projection q f n).IsCocontinuous
        ((Tuple.projection q f n ⋙ q).inheritedTopology J) (q.inheritedTopology J) := by
  have := hq.isFibered
  have := (tuple_isFiberedInGroupoids q f hp hq n).isFibered
  exact Functor.IsFibredOneMorphism.isContinuous_and_isCocontinuous_inheritedTopology J
    (tuple_projection_isFibredOneMorphism q f hq n)

end TupleGeometry

section CechFunctor

open scoped Simplicial

universe vU vX vC uU uX uC w
variable {U : Type uU} {X : Type uX} {C : Type uC}
  [Category.{vU} U] [Category.{vX} X] [Category.{vC} C]
  (q : X ⥤ C) (f : U ⥤ X)
  {F G H : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}}

private def termMap (φ : F ⟶ G) (n : ℕ) :
    term q f F n ⟶ term q f G n :=
  (Tuple.projection q f n).op.ran.map
    (Functor.whiskerLeft (Tuple.projection q f n).op φ)

private lemma termMap_fac (φ : F ⟶ G) (n : ℕ) :
    Functor.whiskerLeft (Tuple.projection q f n).op (termMap q f φ n) ≫
        (Tuple.projection q f n).op.ranCounit.app
          ((Tuple.projection q f n).op ⋙ G) =
      (Tuple.projection q f n).op.ranCounit.app
          ((Tuple.projection q f n).op ⋙ F) ≫
        Functor.whiskerLeft (Tuple.projection q f n).op φ :=
  (Tuple.projection q f n).op.ranCounit.naturality
    (Functor.whiskerLeft (Tuple.projection q f n).op φ)

private lemma reindexMap_naturality (φ : F ⟶ G) {m n : ℕ}
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    termMap q f φ m ≫ reindexMap q f G α =
      reindexMap q f F α ≫ termMap q f φ n := by
  apply ((Tuple.projection q f n).op.ran.obj
    ((Tuple.projection q f n).op ⋙ G)).hom_ext_of_isRightKanExtension
      ((Tuple.projection q f n).op.ranCounit.app
        ((Tuple.projection q f n).op ⋙ G))
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [reindexMap_fac, termMap_fac, ← Category.assoc,
    reindexMap_fac]
  apply NatTrans.ext
  funext x
  exact congr_app (termMap_fac q f φ m)
    ((Tuple.reindex q f α.toOrderHom).op.obj x)

private def cosimplicialMap (φ : F ⟶ G) :
    cosimplicial q f F ⟶ cosimplicial q f G where
  app n := termMap q f φ n.len
  naturality _ _ α := (reindexMap_naturality q f φ α).symm

private def cosimplicialFunctor :
    (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) ⥤
      CosimplicialObject (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) where
  obj := cosimplicial q f
  map := cosimplicialMap q f
  map_id F := by
    apply NatTrans.ext
    funext n
    simp [cosimplicialMap, termMap,
      cosimplicial, term]
  map_comp φ ψ := by
    apply NatTrans.ext
    funext n
    simp [cosimplicialMap, termMap, Functor.whiskerLeft_comp]

private def complexFunctor :
    (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) ⥤
      CochainComplex (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) ℕ :=
  cosimplicialFunctor q f ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

private lemma complexFunctor_obj (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) :
    (complexFunctor q f).obj F = complex q f F := rfl

private lemma termMap_add (φ ψ : F ⟶ G) (n : ℕ) :
    termMap q f (φ + ψ) n =
      termMap q f φ n + termMap q f ψ n := by
  have := ((Tuple.projection q f n).op.ranAdjunction
    AddCommGrpCat.{max uU uX vX w}).right_adjoint_additive
  change (Tuple.projection q f n).op.ran.map
      (Functor.whiskerLeft (Tuple.projection q f n).op φ +
        Functor.whiskerLeft (Tuple.projection q f n).op ψ) = _
  exact Functor.map_add _

private lemma cosimplicialFunctor_additive :
    (cosimplicialFunctor.{vU, vX, vC, uU, uX, uC, w} q f).Additive where
  map_add := by
    intro F G φ ψ
    apply NatTrans.ext
    funext n
    exact termMap_add q f φ ψ n.len

private lemma complexFunctor_additive :
    (complexFunctor.{vU, vX, vC, uU, uX, uC, w} q f).Additive where
  map_add := by
    intro F G φ ψ
    apply HomologicalComplex.Hom.ext
    funext n
    exact termMap_add q f φ ψ n

end CechFunctor

private def sheafifyRanRestrictionIso
    {U X A : Type*} [Category U] [Category X] [Category A]
    (J : GrothendieckTopology U) (K : GrothendieckTopology X) (f : U ⥤ X)
    [HasSheafify K A] [f.IsContinuous J K] [f.IsCocontinuous J K]
    [∀ G : Uᵒᵖ ⥤ A, f.op.HasPointwiseRightKanExtension G]
    (F : Sheaf K A) :
    (presheafToSheaf K A).obj (f.op.ran.obj (f.op ⋙ F.obj)) ≅
      (f.sheafPushforwardCocontinuous A J K).obj
        ((f.sheafPushforwardContinuous A J K).obj F) := by
  let I := (f.sheafPushforwardContinuous A J K).obj F
  let G := (f.sheafPushforwardCocontinuous A J K).obj I
  let e : G.obj ≅ f.op.ran.obj (f.op ⋙ F.obj) :=
    (f.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).app I ≪≫
      f.op.ran.mapIso ((f.sheafPushforwardContinuousCompSheafToPresheafIso A J K).app F)
  exact (sheafificationIso G ≪≫ (presheafToSheaf K A).mapIso e).symm

private def sheafifyRanRestrictionNatIso
    {U X A : Type*} [Category U] [Category X] [Category A]
    (J : GrothendieckTopology U) (K : GrothendieckTopology X) (f : U ⥤ X)
    [HasSheafify K A] [f.IsContinuous J K] [f.IsCocontinuous J K]
    [∀ G : Uᵒᵖ ⥤ A, f.op.HasPointwiseRightKanExtension G] :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft Uᵒᵖ Xᵒᵖ A).obj f.op ⋙
      f.op.ran ⋙ presheafToSheaf K A ≅
        f.sheafPushforwardContinuous A J K ⋙ f.sheafPushforwardCocontinuous A J K := by
  let S := f.sheafPushforwardContinuous A J K
  let R := f.sheafPushforwardCocontinuous A J K
  let e : S ⋙ R ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf K A ⋙ (Functor.whiskeringLeft Uᵒᵖ Xᵒᵖ A).obj f.op ⋙ f.op.ran :=
    Functor.isoWhiskerLeft S (f.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) ≪≫
      Functor.isoWhiskerRight (f.sheafPushforwardContinuousCompSheafToPresheafIso A J K)
        f.op.ran
  exact (Functor.isoWhiskerLeft (S ⋙ R) (sheafificationNatIso K A) ≪≫
    Functor.isoWhiskerRight e (presheafToSheaf K A)).symm

section H0Pushforward


universe u v u' v' a b
variable {U : Type u} {X : Type u'} [Category.{v} U] [Category.{v'} X]
  (J : GrothendieckTopology U) (K : GrothendieckTopology X) (f : U ⥤ X)
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
  [HasExt.{b} (Sheaf J AddCommGrpCat.{a})] [HasExt.{b} (Sheaf K AddCommGrpCat.{a})]
  [f.IsCocontinuous J K]
  [∀ G : Uᵒᵖ ⥤ AddCommGrpCat.{a}, f.op.HasPointwiseRightKanExtension G]

private def postcompAddEquiv {C : Type*} [Category C] [Preadditive C]
    (Z : C) {A B : C} (e : A ≅ B) : (Z ⟶ A) ≃+ (Z ⟶ B) where
  toFun x := x ≫ e.hom
  invFun x := x ≫ e.inv
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := Preadditive.add_comp _ _ _ x y e.hom

private def h0PushforwardAddEquiv (F : Sheaf J AddCommGrpCat.{a}) :
    ((f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K).obj F).H 0 ≃+ F.H 0 := by
  let Z := AddCommGrpCat.of (ULift.{a} ℤ)
  let R := f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K
  let e := (f.sheafPushforwardCocontinuousCompSheafToPresheafIso AddCommGrpCat.{a} J K).app F
  let e' : ((Functor.const Xᵒᵖ).obj Z ⟶ (R.obj F).obj) ≃+
      ((Functor.const Xᵒᵖ).obj Z ⟶ f.op.ran.obj F.obj) :=
    postcompAddEquiv _ e
  exact Abelian.Ext.addEquiv₀.trans
    (((sheafificationAdjunction K AddCommGrpCat.{a}).homAddEquiv _ _).trans
      (e'.trans (((f.op.ranAdjunction AddCommGrpCat.{a}).homAddEquiv _ _).symm.trans
        (((sheafificationAdjunction J AddCommGrpCat.{a}).homAddEquiv _ _).symm.trans
          Abelian.Ext.addEquiv₀.symm))))

private lemma h0PushforwardAddEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{a}} (φ : F ⟶ G)
    (x : ((f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K).obj F).H 0) :
    h0PushforwardAddEquiv J K f G (Sheaf.H.map
      ((f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K).map φ) 0 x) =
    Sheaf.H.map φ 0 (h0PushforwardAddEquiv J K f F x) := by
  let Z := (Functor.const Xᵒᵖ).obj (AddCommGrpCat.of (ULift.{a} ℤ))
  let R := f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K
  let e := f.sheafPushforwardCocontinuousCompSheafToPresheafIso AddCommGrpCat.{a} J K
  let aK := sheafificationAdjunction K AddCommGrpCat.{a}
  let aJ := sheafificationAdjunction J AddCommGrpCat.{a}
  let aR := f.op.ranAdjunction AddCommGrpCat.{a}
  let u : (presheafToSheaf K AddCommGrpCat.{a}).obj Z ⟶ R.obj F := Abelian.Ext.addEquiv₀ x
  have hmap : (Abelian.Ext.addEquiv₀ (Sheaf.H.map (R.map φ) 0 x) :
      (presheafToSheaf K AddCommGrpCat.{a}).obj Z ⟶ R.obj G) = u ≫ R.map φ :=
    Sheaf.H.addEquiv₀_map (R.map φ) x
  apply Abelian.Ext.addEquiv₀.injective
  rw [Sheaf.H.addEquiv₀_map]
  change Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm
    ((aJ.homEquiv _ G).symm ((aR.homEquiv Z G.obj).symm
      ((aK.homEquiv Z (R.obj G) (Abelian.Ext.addEquiv₀ (Sheaf.H.map (R.map φ) 0 x))) ≫
        (e.app G).hom)))) =
    Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm
      ((aJ.homEquiv _ F).symm ((aR.homEquiv Z F.obj).symm
        ((aK.homEquiv Z (R.obj F) u) ≫ (e.app F).hom)))) ≫ φ
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hmap,
    aK.homEquiv_naturality_right, ← aJ.homEquiv_naturality_right_symm]
  apply congrArg (aJ.homEquiv _ G).symm
  change (aR.homEquiv Z G.obj).symm
      (((aK.homEquiv Z (R.obj F)) u ≫
        (sheafToPresheaf K AddCommGrpCat.{a}).map (R.map φ)) ≫ (e.app G).hom) =
    (aR.homEquiv Z F.obj).symm ((aK.homEquiv Z (R.obj F)) u ≫ (e.app F).hom) ≫ φ.hom
  rw [← aR.homEquiv_naturality_right_symm]
  apply congrArg (aR.homEquiv Z G.obj).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg ((aK.homEquiv Z (R.obj F)) u ≫ ·)
      (e.hom.naturality φ)).trans (Category.assoc _ _ _).symm)

private def h0PushforwardIso :
    f.sheafPushforwardCocontinuous AddCommGrpCat.{a} J K ⋙ Sheaf.functorH K 0 ≅
      Sheaf.functorH J 0 :=
  NatIso.ofComponents (fun F => (h0PushforwardAddEquiv J K f F).toAddCommGrpIso)
    (fun φ => by ext x; exact h0PushforwardAddEquiv_naturality J K f φ x)

end H0Pushforward
section CechResolution

universe u vU vX uU uX w b

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : Type uU} {X : Type uX} [Category.{vU} U] [Category.{vX} X]
  (p : U ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : U ⥤ X)
  (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f)
  (hcover : ∀ x : X, ∃ R : Presieve x,
    Sieve.generate R ∈ BigFppfOver.associatedTopology B S hS q τ x ∧
      ∀ ⦃y : X⦄ (g : y ⟶ x), R g → ∃ z : U, Nonempty (y ≅ f.obj z))
  [HasSheafify (BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max uU uX vX w}]
  (F : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max uU uX vX w})

private def cechSheafComplexFunctor :
    Sheaf (BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max uU uX vX w} ⥤
      CochainComplex (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max uU uX vX w}) ℕ :=
  sheafToPresheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w} ⋙
    complexFunctor.{vU, vX, u, uU, uX, u + 1, w} q f ⋙
    (presheafToSheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w}).mapHomologicalComplex (.up ℕ)

private lemma cechSheafComplexFunctor_additive :
    (cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).Additive := by
  have := complexFunctor_additive.{vU, vX, u, uU, uX, u + 1, w} q f
  have := (sheafificationAdjunction (BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max uU uX vX w}).right_adjoint_additive
  dsimp [cechSheafComplexFunctor]
  infer_instance

private def augmentationResolution :
    (CochainComplex.single₀ _).obj F ⟶
      (cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).obj F :=
  (CochainComplex.fromSingle₀Equiv
    ((cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).obj F) F).symm
    ⟨sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS q f τ F,
      sheafAugmentation_comp_d.{u, uU, uX, vU, vX, w} B S hS q f τ F⟩

include hp hq hf hcover in
private lemma augmentationResolution_quasiIso :
    QuasiIso (augmentationResolution.{u, vU, vX, uU, uX, w} B S hS q f τ F) := by
  exact @quasiIso_fromSingle₀_of_exact _ _ _
    ((cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).obj F) _
    (sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS q f τ F)
    (mono_sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS q f τ hcover F)
    (sheafAugmentation_comp_d.{u, uU, uX, vU, vX, w} B S hS q f τ F)
    (exact_sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS p q f τ hp hq hf hcover F)
    (exactAt_sheafComplex_succ.{u, uU, uX, vU, vX, w} B S hS p q f τ hp hq hf hcover F)

private lemma sheafAugmentation_naturality
    {G : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w}} (φ : F ⟶ G) :
    φ ≫ sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS q f τ G =
      sheafAugmentation.{u, uU, uX, vU, vX, w} B S hS q f τ F ≫
        ((cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).map φ).f 0 := by
  let J := BigFppfOver.associatedTopology B S hS q τ
  let P := Tuple.projection q f 0
  have h₁ := (sheafificationNatIso J AddCommGrpCat.{max uU uX vX w}).hom.naturality φ
  have h₂ := (P.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).unit.naturality φ.hom
  change φ ≫ (sheafificationIso G).hom =
    (sheafificationIso F).hom ≫ (presheafToSheaf J _).map φ.hom at h₁
  dsimp only [Functor.id_map] at h₂
  change φ.hom ≫ augmentation.{u, uU, uX, vU, vX, w} q f G.obj 0 =
    augmentation.{u, uU, uX, vU, vX, w} q f F.obj 0 ≫ termMap q f φ.hom 0 at h₂
  change φ ≫ (sheafificationIso G).hom ≫
      (presheafToSheaf J AddCommGrpCat.{max uU uX vX w}).map
        (augmentation.{u, uU, uX, vU, vX, w} q f G.obj 0) =
    ((sheafificationIso F).hom ≫ (presheafToSheaf J AddCommGrpCat.{max uU uX vX w}).map
        (augmentation.{u, uU, uX, vU, vX, w} q f F.obj 0)) ≫
      (presheafToSheaf J AddCommGrpCat.{max uU uX vX w}).map (termMap q f φ.hom 0)
  rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, h₂,
    Functor.map_comp, ← Category.assoc]

private def augmentationResolutionNatTrans :
    CochainComplex.single₀ _ ⟶ cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ where
  app F := augmentationResolution.{u, vU, vX, uU, uX, w} B S hS q f τ F
  naturality F G φ := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      change ((CochainComplex.single₀ _).map φ ≫
          augmentationResolution.{u, vU, vX, uU, uX, w} B S hS q f τ G).f 0 =
        (augmentationResolution.{u, vU, vX, uU, uX, w} B S hS q f τ F ≫
          (cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).map φ).f 0
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]
      exact sheafAugmentation_naturality.{u, vU, vX, uU, uX, w} B S hS q f τ F φ
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 F (n + 1)
        (by omega)).eq_of_src _ _

include hp hq hf in
private lemma sheafComplex_injective [f.Faithful] [HasEqualizers U]
    [Injective F] (n : ℕ) :
    Injective ((sheafComplex.{u, uU, uX, vU, vX, w} B S hS q f τ F).X n) := by
  let fn := Tuple.projection q f n
  let JX := BigFppfOver.associatedTopology B S hS q τ
  let Jn := BigFppfOver.associatedTopology B S hS (fn ⋙ q) τ
  have hp' : (f ⋙ q).IsFiberedInGroupoids := hf.comp_eq.symm ▸ hp
  have hpn := tuple_isFiberedInGroupoids q f hp' hq n
  have hfn := tuple_projection_isFibredOneMorphism q f hq n
  have : q.IsFibered := hq.isFibered
  have : (fn ⋙ q).IsFibered := hpn.isFibered
  have htop := hfn.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)
  have : fn.IsContinuous Jn JX := htop.1
  have : fn.IsCocontinuous Jn JX := htop.2
  have : fn.Faithful := tuple_projection_faithful q f n
  have := tuple_hasEqualizers q f hp' hq n
  let I := (fn.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX w} Jn JX).obj F
  have : Injective I :=
    AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj
      B S hS (fn ⋙ q) q fn (B.baseTopology τ) hpn hq rfl F
  have : Functor.PreservesInjectiveObjects
      (fn.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JX) :=
    AlgebraicGeometry.Stack.abelianDirectImage_preservesInjectiveObjects
      B S hS hfn τ
  let G := (fn.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JX).obj I
  have : Injective G := inferInstance
  exact Injective.of_iso (sheafifyRanRestrictionIso Jn JX fn F).symm inferInstance

include hp hq hf hcover in
private lemma augmentationResolution_map_quasiIso
    [f.Faithful] [HasEqualizers U] [Injective F]
    {A : Type*} [Category A] [Abelian A]
    (Γ : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w} ⥤ A) [Γ.Additive] :
    QuasiIso ((Γ.mapHomologicalComplex (.up ℕ)).map
      (augmentationResolution.{u, vU, vX, uU, uX, w} B S hS q f τ F)) := by
  have := augmentationResolution_quasiIso.{u, vU, vX, uU, uX, w}
    B S hS p q f τ hp hq hf hcover F
  have : ∀ n, Injective
      (((cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ).obj F).X n) :=
    sheafComplex_injective.{u, vU, vX, uU, uX, w} B S hS p q f τ hp hq hf F
  exact quasiIso_map_of_injective Γ _

include hp hq hf hcover in
private lemma exists_cechSpectralSequence
    [f.Faithful] [HasEqualizers U]
    [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w})]
    (I : InjectiveResolution F) :
    letI := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
    let G := cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ ⋙
      (Sheaf.functorH (BigFppfOver.associatedTopology B S hS q τ) 0).mapHomologicalComplex
        (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{b}
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{b} 1,
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅
        (((G ⋙ HomologicalComplex.eval AddCommGrpCat.{b} (.up ℤ) p).mapHomologicalComplex
          (.up ℤ)).obj I.cochainComplex).homology q)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      Stacks.RelativeLeray.AbutsTo E
        (fun n : ℤ => if n < 0 then (⊥_ AddCommGrpCat.{b}) else
          (Sheaf.functorH (BigFppfOver.associatedTopology B S hS q τ) n.toNat).obj F) := by
  let := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
  let Γ := Sheaf.functorH (BigFppfOver.associatedTopology B S hS q τ) 0
  obtain ⟨E, hpage, hquad, habut⟩ := exists_spectralSequence_of_natFunctorResolution Γ
    (cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ)
    (augmentationResolutionNatTrans.{u, vU, vX, uU, uX, w} B S hS q f τ)
    I.cochainComplex (fun n => augmentationResolution_map_quasiIso.{u, vU, vX, uU, uX, w}
      B S hS p q f τ hp hq hf hcover (I.cochainComplex.X n) Γ)
  refine ⟨E, hpage, hquad, spectralSequence_abutsTo_of_iso E habut (fun n => ?_)⟩
  split_ifs with hn
  · exact (HomologicalComplex.ExactAt.of_isZero
      (K := ((Γ.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) (i := n)
      (Γ.map_isZero (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 n
        hn))).isZero_homology.isoIsInitial initialIsInitial
  · have hn' : (n.toNat : ℤ) = n := by omega
    simpa only [hn'] using (sheafCohomologyIso
      (BigFppfOver.associatedTopology B S hS q τ) F I n.toNat).symm

include hp hq hf in
private def cechColumnCohomologyIso
    [f.Faithful] [HasEqualizers U]
    [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX w})]
    [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max uU uX vX w}]
    [∀ n : ℕ, HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max uU uX vX w})]
    (I : InjectiveResolution F) (n k : ℕ) :
    letI := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
    let fn := Tuple.projection q f n
    let JX := BigFppfOver.associatedTopology B S hS q τ
    let Jn := BigFppfOver.associatedTopology B S hS (fn ⋙ q) τ
    letI : fn.IsContinuous Jn JX :=
      (tuple_projection_continuous_cocontinuous q f (hf.comp_eq.symm ▸ hp) hq
        (BigFppfOver.baseOverTopology B S hS τ) n).1
    let G := cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ ⋙
      (Sheaf.functorH JX 0).mapHomologicalComplex (.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{b}
    (((G ⋙ HomologicalComplex.eval AddCommGrpCat.{b} (.up ℤ) (n : ℤ)).mapHomologicalComplex
      (.up ℤ)).obj I.cochainComplex).homology (k : ℤ) ≅
      (Sheaf.functorH Jn k).obj
        ((fn.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX w} Jn JX).obj F) := by
  letI := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
  let fn := Tuple.projection q f n
  let JX := BigFppfOver.associatedTopology B S hS q τ
  let Jn := BigFppfOver.associatedTopology B S hS (fn ⋙ q) τ
  have htop := tuple_projection_continuous_cocontinuous q f
    (hf.comp_eq.symm ▸ hp) hq (BigFppfOver.baseOverTopology B S hS τ) n
  letI : fn.IsContinuous Jn JX := htop.1
  letI : fn.IsCocontinuous Jn JX := htop.2
  let Γ := Sheaf.functorH JX 0
  let Γn := Sheaf.functorH Jn 0
  let R := cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ
  let G := R ⋙ Γ.mapHomologicalComplex (.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{b}
  let Q := fn.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX w} Jn JX
  let P := fn.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JX
  have : Q.Additive := { map_add := rfl }
  have hpn := tuple_isFiberedInGroupoids q f (hf.comp_eq.symm ▸ hp) hq n
  have hfn := tuple_projection_isFibredOneMorphism q f hq n
  letI : q.IsFibered := hq.isFibered
  letI : (fn ⋙ q).IsFibered := hpn.isFibered
  have : fn.Faithful := tuple_projection_faithful q f n
  have := tuple_hasEqualizers q f (hf.comp_eq.symm ▸ hp) hq n
  have hI (j : ℕ) : Injective (Q.obj (I.cocomplex.X j)) :=
    AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj
      B S hS (fn ⋙ q) q fn (B.baseTopology τ) hpn hq rfl (I.cocomplex.X j)
  have : Q.PreservesHomology := by
    have := hfn.preservesFiniteLimits_inverseImage
      (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{max uU uX vX w}
    infer_instance
  let In := mapInjectiveResolution Q I hI
  let e₁ : G ⋙ HomologicalComplex.eval AddCommGrpCat.{b} (.up ℤ) (n : ℤ) ≅
      R ⋙ HomologicalComplex.eval _ (.up ℕ) n ⋙ Γ :=
    Functor.isoWhiskerLeft (R ⋙ Γ.mapHomologicalComplex (.up ℕ))
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{b}
        (i := n) rfl)
  let e₂ : R ⋙ HomologicalComplex.eval _ (.up ℕ) n ≅ Q ⋙ P :=
    sheafifyRanRestrictionNatIso Jn JX fn
  let e₃ : G ⋙ HomologicalComplex.eval AddCommGrpCat.{b} (.up ℤ) (n : ℤ) ≅ Q ⋙ Γn :=
    e₁ ≪≫ Functor.isoWhiskerRight e₂ Γ ≪≫
      Functor.isoWhiskerLeft Q (h0PushforwardIso Jn JX fn)
  let e₄ := (NatIso.mapHomologicalComplex e₃ (.up ℤ)).app I.cochainComplex
  let e₅ : ((Γn.mapHomologicalComplex (.up ℤ)).obj
      ((Q.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) ≅
      ((Γn.mapHomologicalComplex (.up ℤ)).obj In.cochainComplex) :=
    (Γn.mapHomologicalComplex (.up ℤ)).mapIso (mapExtendIso Q I.cocomplex)
  exact HomologicalComplex.homologyMapIso (e₄ ≪≫ e₅) (k : ℤ) ≪≫
    (sheafCohomologyIso Jn (Q.obj F) In k).symm

end CechResolution

end Stacks.RelativeCech

end
