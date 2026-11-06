module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Limit preservation is fppf-local for sheaves

An fppf sheaf on the big fppf site over a scheme preserves inverse limits of affine schemes
as soon as it does so after restriction to every member of an fppf covering of the base.

## Main results

* `AlgebraicGeometry.limitPreserving_of_fppfCover` descends limit preservation from an fppf
  covering of the base.

## Implementation notes

The fppf covering is presented in the big site but need not belong to its chosen bounded
covering system, so its covering sieve is obtained by replacing it with a tautologically
equivalent chosen family. Restriction to one of its members is composition with the
canonical functor between slice categories.

After base change to a fixed stage of the tested system the covering is refined by a finite
family with affine sources, and the sheaf condition then glues sections over the products
with the members of that family. Because the index objects live in `max w w'`, passage to
the slice over a stage keeps the same indexing size, and the tested limits and the target
property use the same cofiltered index universes.

## References

* [Stacks Project, Tag 049P](https://stacks.math.columbia.edu/tag/049P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry

/-! The lift of a cone to a slice is unfolded throughout this file at its underlying object.
Making `Over.lift` reducible for unification lets `rw` and instance search see through it,
instead of relying on relaxed transparency. (`PullbackCone.mk`, `prod.functor` and `Over.post`
are already `[implicit_reducible]` in Mathlib.) -/
attribute [local implicit_reducible] CategoryTheory.Over.lift

attribute [local instance] IsCofiltered.isConnected IsFiltered.isConnected

/-- An fppf covering family in a big fppf site generates a covering sieve for the site's
chosen topology, even when the family itself is not one of the chosen ones. -/
private lemma fppf_cover_sieve_mem_topology
    (B : BigFppfSite.{u}) {T : B.Schemes}
    (E : PreZeroHypercover.{u + 1} T)
    (hE : IsFppfCovering ⟨T, E⟩) :
    E.sieve₀ ∈ B.topology T := by
  let U := E.map B.inclusion
  have hU : U.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj T) := by
    simpa [U, IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hE
  obtain ⟨V, hV, hEq⟩ :=
    exists_isCovering_tautologicallyEquivalent_of_sources_iso
      B T U hU (fun i ↦ ⟨E.X i, E.f i, Iso.refl _, by simp [U, PreZeroHypercover.map]⟩)
  have hle : V.presieve₀ ≤ E.sieve₀.arrows := by
    obtain ⟨β, hβ⟩ := hEq.2
    let β' : V.I₀ → E.I₀ := β
    have hβ' (j : V.I₀) :
        ∃ e : B.inclusion.obj (V.X j) ≅ B.inclusion.obj (E.X (β' j)),
          e.hom ≫ B.inclusion.map (E.f (β' j)) = B.inclusion.map (V.f j) := by
      simpa [β', U, PreZeroHypercover.map] using hβ j
    rintro Z f ⟨j⟩
    obtain ⟨e, he⟩ := hβ' j
    exact ⟨E.X (β' j), B.inclusion.preimage e.hom, E.f (β' j), ⟨β' j⟩,
      B.inclusion.map_injective (by rwa [Functor.map_comp, Functor.map_preimage])⟩
  have hgen : Sieve.generate V.presieve₀ ∈ B.topology T :=
    Precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩
  exact B.topology.superset_covering (by rwa [Sieve.generate_le_iff]) hgen

/-- An fppf covering of an affine object of a big fppf site is refined by a finite fppf
covering with affine sources, together with a morphism of families to the original. -/
private lemma finite_affine_refinement
    (B : BigFppfSite.{u}) (T : B.Schemes)
    [IsAffine (B.inclusion.obj T)]
    (P : PreZeroHypercover.{u + 1} T)
    (hP : IsFppfCovering ⟨T, P⟩) :
    ∃ (Q : PreZeroHypercover.{u + 1} T) (_ : Q ⟶ P),
      Finite Q.I₀ ∧ IsFppfCovering ⟨T, Q⟩ ∧
        ∀ i, IsAffine (B.inclusion.obj (Q.X i)) := by
  classical
  have hP' : (P.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) := by
    simpa only [IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀_map] using hP
  let P' : (B.inclusion.obj T).Cover Scheme.fppfPrecoverage := ⟨P.map B.inclusion, hP'⟩
  have : MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      @IsOpenImmersion :=
    ⟨fun {X Y Z} i hi g hg ↦ by
      have : IsOpenImmersion i := hi
      have : Flat g := hg.1
      have : LocallyOfFinitePresentation g := hg.2
      exact ⟨inferInstance, inferInstance⟩⟩
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage :=
    inferInstanceAs (Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  have : QuasiCompactCover P'.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ by
      have : Flat (P'.f i) := (P'.map_prop i).1
      have : LocallyOfFinitePresentation (P'.f i) := (P'.map_prop i).2
      exact (P'.f i).isOpenMap)
  obtain ⟨U, f, hfin, hopen⟩ := QuasiCompactCover.exists_hom P'
  have : Finite U.I₀ := hfin
  have : ∀ i, IsAffine (U.cover.X i) := fun i ↦ inferInstanceAs (IsAffine (Scheme.Spec.obj _))
  have hstandard : IsStandardFppfCovering U.cover.X U.cover.f := by
    refine ⟨hfin, inferInstance, fun i ↦ inferInstance, fun i ↦ (U.cover.map_prop i).1,
      fun i ↦ ⟨(U.cover.map_prop i).2, inferInstance, inferInstance⟩, ?_⟩
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact U.cover.exists_eq x
  obtain ⟨V, hV, ⟨α, hα⟩, _⟩ :=
    exists_isCovering_tautologicallyEquivalent_standardFppfCovering
      B T U.cover.toPreZeroHypercover U.cover.mem₀ hstandard
  choose e he using hα
  let α' : U.cover.I₀ → V.I₀ := α
  let e' : ∀ i : U.cover.I₀, U.cover.X i ≅ B.inclusion.obj (V.X (α' i)) := e
  have he' (i : U.cover.I₀) :
      (e' i).hom ≫ B.inclusion.map (V.f (α' i)) = U.cover.f i := he i
  let Q : PreZeroHypercover.{u + 1} T :=
    { I₀ := U.cover.I₀
      X i := V.X (α' i)
      f i := V.f (α' i) }
  have hQiso : U.cover.toPreZeroHypercover ≅ Q.map B.inclusion :=
    PreZeroHypercover.isoMk (Equiv.refl _) (fun i ↦ e' i) (fun i ↦ he' i)
  have hQ : (Q.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) :=
    PreZeroHypercover.presieve₀_mem_of_iso hQiso U.cover.mem₀
  refine ⟨Q, { s₀ := f.s₀
               h₀ i := B.inclusion.preimage ((e' i).inv ≫ f.h₀ i)
               w₀ := fun i ↦ ?_ }, hfin, ?_, ?_⟩
  · apply B.inclusion.map_injective
    have hmap : B.inclusion.map (B.inclusion.preimage ((e' i).inv ≫ f.h₀ i) ≫ P.f (f.s₀ i)) =
        ((e' i).inv ≫ f.h₀ i) ≫ P'.f (f.s₀ i) := by
      simp only [Functor.map_comp, Functor.map_preimage]
      rfl
    refine hmap.trans ?_
    calc ((e' i).inv ≫ f.h₀ i) ≫ P'.f (f.s₀ i)
        = (e' i).inv ≫ U.cover.f i := by rw [Category.assoc, f.w₀]
      _ = B.inclusion.map (V.f (α' i)) := by rw [← he' i, Iso.inv_hom_id_assoc]
  · simpa only [IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀_map] using hQ
  · intro i
    exact IsAffine.of_isIso (e' i).inv

/-- In a filtered category a finite family of objects admits a common target. -/
private lemma finite_common_target
    {I : Type w} [Category.{w'} I] [IsFiltered I]
    {K : Type*} [Finite K] (j : K → I) :
    ∃ k : I, Nonempty (∀ a, j a ⟶ k) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨c⟩ := IsFiltered.cocone_nonempty (Discrete.functor j)
  exact ⟨c.pt, ⟨fun a ↦ c.ι.app ⟨a⟩⟩⟩

/-- In a filtered category a finite family of morphisms out of one object extends to a common
target compatibly. -/
private lemma finite_common_extension
    {I : Type w} [Category.{w'} I] [IsFiltered I]
    {K : Type*} [Finite K] {i : I} (j : K → I) (f : ∀ a, i ⟶ j a) :
    ∃ (k : I) (g : i ⟶ k) (h : ∀ a, j a ⟶ k), ∀ a, f a ≫ h a = g := by
  obtain ⟨k, ⟨h⟩⟩ := finite_common_target (fun a ↦ Under.mk (f a))
  exact ⟨k.right, k.hom, fun a ↦ (h a).right, fun a ↦ Under.w (h a)⟩

/-- A cocone is a colimit once finitely many comparison transformations into it detect
sections and separate them, with gluing available at every stage and at the apex. This is
the shape of the sheaf condition for a finite covering, applied to a filtered colimit. -/
private lemma isColimit_of_finite_gluing
    {I : Type w} [Category.{w'} I] [IsFiltered I]
    {K : Type*} [Finite K]
    (G : I ⥤ Type v) (A : K → I ⥤ Type v) (B : K → K → I ⥤ Type v)
    (r : ∀ k, G ⟶ A k) (s : ∀ k l, A k ⟶ B k l) (t : ∀ k l, A l ⟶ B k l)
    (cG : Cocone G) (cA : ∀ k, Cocone (A k)) (cB : ∀ k l, Cocone (B k l))
    (r₀ : ∀ k, cG.pt → (cA k).pt)
    (s₀ : ∀ k l, (cA k).pt → (cB k l).pt)
    (t₀ : ∀ k l, (cA l).pt → (cB k l).pt)
    (hr : ∀ k i x, r₀ k (cG.ι.app i x) = (cA k).ι.app i ((r k).app i x))
    (hs : ∀ k l i x, s₀ k l ((cA k).ι.app i x) =
      (cB k l).ι.app i ((s k l).app i x))
    (ht : ∀ k l i x, t₀ k l ((cA l).ι.app i x) =
      (cB k l).ι.app i ((t k l).app i x))
    (hstage : ∀ i (a : ∀ k, (A k).obj i),
      (∀ k l, (s k l).app i (a k) = (t k l).app i (a l)) →
      ∃! x, ∀ k, (r k).app i x = a k)
    (hcompat : ∀ x k l, s₀ k l (r₀ k x) = t₀ k l (r₀ l x))
    (hsep : ∀ x y, (∀ k, r₀ k x = r₀ k y) → x = y)
    (hA : ∀ k, IsColimit (cA k)) (hB : ∀ k l, IsColimit (cB k l))
    (hcomm : ∀ i x k l, (s k l).app i ((r k).app i x) =
      (t k l).app i ((r l).app i x)) : Nonempty (IsColimit cG) := by
  classical
  have nat_apply {H H' : I ⥤ Type v} (α : H ⟶ H') {i j : I} (f : i ⟶ j)
      (x : H.obj i) : H'.map f (α.app i x) = α.app j (H.map f x) :=
    (ConcreteCategory.congr_hom (α.naturality f) x).symm
  have cocone_apply {H : I ⥤ Type v} (c : Cocone H) {i j : I} (f : i ⟶ j)
      (x : H.obj i) : c.ι.app j (H.map f x) = c.ι.app i x :=
    ConcreteCategory.congr_hom (c.w f) x
  refine ⟨Types.FilteredColimit.isColimitOf' G cG ?_ ?_⟩
  · intro x
    choose j a ha using fun k ↦ Types.jointly_surjective_of_isColimit (hA k) (r₀ k x)
    obtain ⟨i, ⟨f⟩⟩ := finite_common_target j
    let ai : ∀ k, (A k).obj i := fun k ↦ (A k).map (f k) (a k)
    have hai (k) : (cA k).ι.app i (ai k) = r₀ k x := by
      simpa only [ai, cocone_apply] using ha k
    have heq (k l) : (cB k l).ι.app i ((s k l).app i (ai k)) =
        (cB k l).ι.app i ((t k l).app i (ai l)) := by
      rw [← hs, ← ht, hai, hai, hcompat]
    choose j' f' hf' using fun kl : K × K ↦
      (Types.FilteredColimit.isColimit_eq_iff' (hB kl.1 kl.2)
        ((s kl.1 kl.2).app i (ai kl.1)) ((t kl.1 kl.2).app i (ai kl.2))).mp
          (heq kl.1 kl.2)
    obtain ⟨i', g, h, hg⟩ := finite_common_extension j' f'
    let ai' : ∀ k, (A k).obj i' := fun k ↦ (A k).map g (ai k)
    have hmatch (k l) : (s k l).app i' (ai' k) = (t k l).app i' (ai' l) := by
      dsimp [ai']
      rw [← nat_apply (s k l) g (ai k), ← nat_apply (t k l) g (ai l), ← hg (k, l)]
      simpa only [Functor.map_comp, types_comp_apply] using
        congrArg ((B k l).map (h (k, l))) (hf' (k, l))
    obtain ⟨y, hy, _⟩ := hstage i' ai' hmatch
    refine ⟨i', y, hsep _ _ (fun k ↦ ?_)⟩
    rw [hr, hy, show ai' k = (A k).map g (ai k) from rfl, cocone_apply, hai]
  · intro i x y hxy
    have heq (k) : (cA k).ι.app i ((r k).app i x) =
        (cA k).ι.app i ((r k).app i y) := by
      rw [← hr, ← hr, hxy]
    choose j f hf using fun k ↦
      (Types.FilteredColimit.isColimit_eq_iff' (hA k)
        ((r k).app i x) ((r k).app i y)).mp (heq k)
    obtain ⟨i', g, h, hg⟩ := finite_common_extension j f
    have heq' (k) : (r k).app i' (G.map g x) = (r k).app i' (G.map g y) := by
      rw [← nat_apply (r k) g x, ← nat_apply (r k) g y, ← hg k]
      simpa only [Functor.map_comp, types_comp_apply] using
        congrArg ((A k).map (h k)) (hf k)
    obtain ⟨z, hz, hu⟩ := hstage i' (fun k ↦ (r k).app i' (G.map g x))
      (hcomm i' (G.map g x))
    exact ⟨i', g, (hu _ (fun _ ↦ rfl)).trans (hu _ (fun k ↦ (heq' k).symm)).symm⟩

/-- Sheaf gluing for the family of second projections from the products with a fixed finite
family of objects. -/
private lemma gluing_products
    {C : Type*} [Category C] [HasBinaryProducts C]
    (F : Cᵒᵖ ⥤ Type v) {K : Type*} (Q : K → C) (X : C)
    (hF : Presieve.IsSheafFor F
      (Presieve.ofArrows (fun k ↦ Q k ⨯ X) (fun _ ↦ prod.snd)))
    (a : ∀ k, F.obj (Opposite.op (Q k ⨯ X)))
    (ha : ∀ k l,
      F.map (prod.map (prod.fst : Q k ⨯ Q l ⟶ Q k) (𝟙 X)).op (a k) =
      F.map (prod.map (prod.snd : Q k ⨯ Q l ⟶ Q l) (𝟙 X)).op (a l)) :
    ∃! x, ∀ k, F.map (prod.snd : Q k ⨯ X ⟶ X).op x = a k := by
  apply ((Presieve.isSheafFor_arrows_iff F _).mp hF) a
  intro k l W f g hfg
  let h : W ⟶ (Q k ⨯ Q l) ⨯ X :=
    prod.lift (prod.lift (f ≫ prod.fst) (g ≫ prod.fst)) (f ≫ prod.snd)
  have hf : h ≫ prod.map prod.fst (𝟙 X) = f := by
    ext <;> simp [h]
  have hg : h ≫ prod.map prod.snd (𝟙 X) = g := by
    ext <;> simp [h, hfg]
  have eq := congrArg (F.map h.op) (ha k l)
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    hf, hg] using eq

/-- Functoriality of a presheaf on commuting squares, in composition form. -/
private lemma map_op_comp_eq {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type v)
    {W X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W} {d : W ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map b.op ≫ F.map a.op = F.map d.op ≫ F.map c.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]

/-- A presheaf sends a cofiltered limit cone to a colimit cocone as soon as it does so after
multiplying by each member and each pairwise product of a finite family which covers in the
sense required for gluing. -/
private lemma isColimit_of_products
    {C : Type*} [Category C] [HasBinaryProducts C]
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (F : Cᵒᵖ ⥤ Type v) (D : I ⥤ C) (c : Cone D)
    {K : Type*} [Finite K] (Q : K → C)
    (hglue : ∀ X, Presieve.IsSheafFor F
      (Presieve.ofArrows (fun k ↦ Q k ⨯ X) (fun _ ↦ prod.snd)))
    (hQ : ∀ k, Nonempty (IsColimit
      (F.mapCocone ((prod.functor.obj (Q k)).mapCone c).op)))
    (hQQ : ∀ k l, Nonempty (IsColimit
      (F.mapCocone ((prod.functor.obj (Q k ⨯ Q l)).mapCone c).op))) :
    Nonempty (IsColimit (F.mapCocone c.op)) := by
  classical
  let A (Y : C) : Iᵒᵖ ⥤ Type v := (D ⋙ prod.functor.obj Y).op ⋙ F
  let cA (Y : C) : Cocone (A Y) := F.mapCocone ((prod.functor.obj Y).mapCone c).op
  have hsnd {Y P P' : C} (u : P ⟶ P') :
      F.map u.op ≫ F.map (prod.snd : Y ⨯ P ⟶ P).op =
        F.map (prod.snd : Y ⨯ P' ⟶ P').op ≫ F.map (prod.map (𝟙 Y) u).op :=
    map_op_comp_eq F (by simp)
  have hprod {Y Z P P' : C} (g : Y ⟶ Z) (u : P ⟶ P') :
      F.map (prod.map (𝟙 Z) u).op ≫ F.map (prod.map g (𝟙 P)).op =
        F.map (prod.map g (𝟙 P')).op ≫ F.map (prod.map (𝟙 Y) u).op :=
    map_op_comp_eq F (by simp)
  let r (k : K) : D.op ⋙ F ⟶ A (Q k) :=
    { app i := F.map (prod.snd : Q k ⨯ D.obj i.unop ⟶ _).op
      naturality i j f := hsnd (D.map f.unop) }
  let aMap {Y Z : C} (f : Y ⟶ Z) : A Z ⟶ A Y :=
    { app i := F.map (prod.map f (𝟙 (D.obj i.unop))).op
      naturality i j g := hprod f (D.map g.unop) }
  have hcomm (X : C) (x : F.obj (Opposite.op X)) (k l : K) :
      F.map (prod.map (prod.fst : Q k ⨯ Q l ⟶ Q k) (𝟙 X)).op
        (F.map (prod.snd : Q k ⨯ X ⟶ X).op x) =
      F.map (prod.map (prod.snd : Q k ⨯ Q l ⟶ Q l) (𝟙 X)).op
        (F.map (prod.snd : Q l ⨯ X ⟶ X).op x) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      prod.map_snd, Category.comp_id]
  refine isColimit_of_finite_gluing (D.op ⋙ F) (fun k ↦ A (Q k))
    (fun k l ↦ A (Q k ⨯ Q l)) r (fun k l ↦ aMap prod.fst) (fun k l ↦ aMap prod.snd)
    (F.mapCocone c.op) (fun k ↦ cA (Q k)) (fun k l ↦ cA (Q k ⨯ Q l))
    (fun k ↦ F.map (prod.snd : Q k ⨯ c.pt ⟶ _).op)
    (fun k l ↦ F.map (prod.map (prod.fst : Q k ⨯ Q l ⟶ Q k) (𝟙 c.pt)).op)
    (fun k l ↦ F.map (prod.map (prod.snd : Q k ⨯ Q l ⟶ Q l) (𝟙 c.pt)).op)
    ?_ ?_ ?_ ?_ (hcomm c.pt) ?_ (fun k ↦ (hQ k).some)
    (fun k l ↦ (hQQ k l).some) ?_
  · intro k i x
    exact ConcreteCategory.congr_hom (hsnd (c.π.app i.unop)) x
  · intro k l i x
    exact ConcreteCategory.congr_hom (hprod (prod.fst : Q k ⨯ Q l ⟶ Q k) (c.π.app i.unop)) x
  · intro k l i x
    exact ConcreteCategory.congr_hom (hprod (prod.snd : Q k ⨯ Q l ⟶ Q l) (c.π.app i.unop)) x
  · intro i a ha
    exact gluing_products F Q (D.obj i.unop) (hglue _) a ha
  · intro x y hxy
    obtain ⟨z, hz, hu⟩ := gluing_products F Q c.pt (hglue _)
      (fun k ↦ F.map (prod.snd : Q k ⨯ c.pt ⟶ _).op x) (hcomm c.pt x)
    exact (hu _ (fun _ ↦ rfl)).trans (hu _ (fun k ↦ (hxy k).symm)).symm
  · intro i x
    exact hcomm (D.obj i.unop) x

/-- The square comparing the products with the source and the target of a morphism is
cartesian. -/
private lemma isPullback_prod_snd
    {C : Type*} [Category C] [HasBinaryProducts C] {A B : C} (f : A ⟶ B) (Y : C) :
    IsPullback (prod.snd : Y ⨯ A ⟶ A) (prod.map (𝟙 Y) f) f prod.snd where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift (s.snd ≫ prod.fst) s.fst, by simp, ?_, ?_⟩
    · ext <;> simp [PullbackCone.condition]
    · intro m h₁ h₂
      refine prod.hom_ext ?_ ?_
      · simp [← h₂]
      · simpa using h₁)⟩

/-- Multiplying a cofiltered limit cone by a fixed object again gives a limit cone, computed
after applying a pullback-preserving functor. -/
private noncomputable def isLimit_map_prodMapCone
    {C C' : Type*} [Category C] [Category C'] [HasBinaryProducts C]
    (G : C ⥤ C') [PreservesLimitsOfShape WalkingCospan G]
    {I : Type w} [Category.{w'} I] [IsConnected I]
    {D : I ⥤ C} {c : Cone D} (hc : IsLimit (G.mapCone c)) (Y : C) :
    IsLimit (G.mapCone ((prod.functor.obj Y).mapCone c)) := by
  let α : D ⋙ prod.functor.obj Y ⟶ D :=
    { app _ := prod.snd
      naturality i j g := prod.map_snd (𝟙 Y) (D.map g) }
  exact isLimitOfIsPullbackOfIsConnected (Functor.whiskerRight α G)
    (G.mapCone ((prod.functor.obj Y).mapCone c)) (G.mapCone c)
    { hom := G.map prod.snd
      w i := by
        have hπ : ((Cone.postcompose (Functor.whiskerRight α G)).obj
              (G.mapCone ((prod.functor.obj Y).mapCone c))).π.app i =
            G.map (prod.map (𝟙 Y) (c.π.app i)) ≫ G.map prod.snd := rfl
        simp only [hπ, Functor.mapCone_π_app, ← Functor.map_comp, prod.map_snd]
        rfl }
    (fun i ↦ ((isPullback_prod_snd (c.π.app i) Y).flip).map G) hc

/-- The inclusion of a big fppf site's underlying category into schemes preserves
pullbacks. -/
private theorem bigFppfPreservesPullbacks (B : BigFppfSite.{u}) :
    PreservesLimitsOfShape WalkingCospan B.inclusion := by
  show PreservesLimitsOfShape WalkingCospan
    (ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < B.cutoff))
  infer_instance

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

/-- A binary product of affine objects over an affine base object of a big fppf site is
affine. -/
private lemma isAffine_prod_over
    (B : BigFppfSite.{u}) (X : B.Schemes) (Y Z : Over X)
    [IsAffine (B.inclusion.obj X)]
    [IsAffine (B.inclusion.obj Y.left)] [IsAffine (B.inclusion.obj Z.left)] :
    IsAffine (B.inclusion.obj (Y ⨯ Z).left) := by
  let e := B.inclusion.mapIso (Over.prodLeftIsoPullback Y Z) ≪≫
    PreservesPullback.iso B.inclusion Y.hom Z.hom
  exact IsAffine.of_isIso e.hom

/-- A commuting square from an object `Y` over `W` extends along the first projection of a
product `Y ⨯ Z` in `Over W`. -/
private lemma prod_fst_left_comp_comp
    {C : Type*} [Category C] [HasPullbacks C] {W T A : C} {g : W ⟶ T} {Y : Over W} (Z : Over W)
    {a : Y.left ⟶ A} {b : A ⟶ T}
    (h : a ≫ b = Y.hom ≫ g) :
    ((prod.fst : Y ⨯ Z ⟶ Y).left ≫ a) ≫ b = (Y ⨯ Z).hom ≫ g := by
  rw [Category.assoc, h, ← Category.assoc, Over.w]

/-- For an fppf sheaf on the big fppf site over `S`, the family of second projections from
the products with the members of an fppf covering is a sheaf-gluing family. -/
private lemma isSheafFor_products
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (Over (B.obj hS))ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (B.topology.over (B.obj hS)) F)
    (X : Over (B.obj hS)) (Q : PreZeroHypercover.{u + 1} X.left)
    (hQ : IsFppfCovering ⟨X.left, Q⟩) (Z : Over X.left) :
    Presieve.IsSheafFor ((Over.map X.hom).op ⋙ F)
      (Presieve.ofArrows (fun k ↦ Over.mk (Q.f k) ⨯ Z) (fun _ ↦ prod.snd)) := by
  apply (Presieve.isSheafFor_over_map_op_comp_ofArrows_iff _ _ _).mpr
  apply (isSheaf_iff_isSheaf_of_type _ _).mp hF |>.isSheafFor
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let R : PreZeroHypercover.{u + 1} Z.left :=
    { I₀ := Q.I₀
      X k := (Over.mk (Q.f k) ⨯ Z).left
      f k := (prod.snd : Over.mk (Q.f k) ⨯ Z ⟶ Z).left }
  show R.sieve₀ ∈ B.topology Z.left
  apply fppf_cover_sieve_mem_topology B R
  have hQ' : Q.presieve₀ ∈ (Scheme.fppfPrecoverage.comap B.inclusion) X.left := hQ
  exact Precoverage.mem_coverings_of_isPullback Q.f hQ' Z.hom
    (fun k ↦ (prod.snd : Over.mk (Q.f k) ⨯ Z ⟶ Z).left)
    (fun k ↦ (prod.fst : Over.mk (Q.f k) ⨯ Z ⟶ Over.mk (Q.f k)).left)
    (fun k ↦ (Over.isPullback_of_binaryFan_isLimit _
      (prodIsProd (Over.mk (Q.f k)) Z)).flip)

/-- Recognizing the comparison cocone of a presheaf as a colimit transports along an
isomorphism of the tested diagram together with a compatible isomorphism of the apices. -/
private lemma isColimit_mapCocone_of_iso
    {C : Type*} [Category C] {I : Type*} [Category I]
    (F : Cᵒᵖ ⥤ Type v) {D E : I ⥤ C} (cD : Cone D) (cE : Cone E)
    (e : D ≅ E) (p : cD.pt ≅ cE.pt)
    (hp : ∀ i, p.hom ≫ cE.π.app i = cD.π.app i ≫ e.hom.app i)
    (hc : Nonempty (IsColimit (F.mapCocone cD.op))) :
    Nonempty (IsColimit (F.mapCocone cE.op)) := by
  let eF : E.op ⋙ F ≅ D.op ⋙ F := Functor.isoWhiskerRight (NatIso.op e) F
  have hpre := (IsColimit.precomposeHomEquiv eF (F.mapCocone cD.op)).symm hc.some
  refine ⟨IsColimit.ofIsoColimit hpre (Cocone.ext (F.mapIso p.symm.op) ?_)⟩
  intro i
  dsimp [eF]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg Quiver.Hom.op
  simpa only [Iso.op_inv, Quiver.Hom.unop_op, unop_comp, NatIso.op_hom,
    NatTrans.op_app, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    congrArg (fun f ↦ p.inv ≫ f) (hp i.unop).symm

/-- If a presheaf becomes limit preserving after restriction to the slice over a member of a
covering, then its comparison cocone for the product with an object mapping to that member
is a colimit. -/
private lemma isColimit_product_of_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (Over (B.obj hS))ᵒᵖ ⥤ Type v)
    (U : B.Schemes) (f : U ⟶ B.obj hS)
    (hloc : LimitPreserving.{u, v, w, w', u + 1}
      (Over.forget U ⋙ B.inclusion) ((Over.map f).op ⋙ F))
    (X : Over (B.obj hS)) (Y : Over X.left) (p : Y.left ⟶ U)
    (hp : p ≫ f = Y.hom ≫ X.hom)
    [IsAffine (B.inclusion.obj X.left)] [IsAffine (B.inclusion.obj Y.left)]
    {I : Type (max w w')} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ Over X.left) (c : Cone D)
    (hc : IsLimit ((Over.forget X.left ⋙ B.inclusion).mapCone c))
    (hD : ∀ i, IsAffine (B.inclusion.obj (D.obj i).left))
    (hcpt : IsAffine (B.inclusion.obj c.pt.left)) :
    Nonempty (IsColimit (((Over.map X.hom).op ⋙ F).mapCocone
      ((prod.functor.obj Y).mapCone c).op)) := by
  classical
  let G := prod.functor.obj Y
  let H := D ⋙ G ⋙ Over.forget X.left
  let cH : Cone H := (Over.forget X.left).mapCone (G.mapCone c)
  let q : H ⟶ (Functor.const I).obj U :=
    { app i := (prod.fst : Y ⨯ D.obj i ⟶ Y).left ≫ p
      naturality i j g := by
        dsimp [H, G]
        rw [← Category.assoc, ← Over.comp_left]
        simp }
  let cp : cH.pt ⟶ U := (prod.fst : Y ⨯ c.pt ⟶ Y).left ≫ p
  have hcp (i : I) : cH.π.app i ≫ q.app i = cp := by
    have key : (prod.map (𝟙 Y) (c.π.app i) : (Y ⨯ c.pt : Over X.left) ⟶ Y ⨯ D.obj i) ≫
        prod.fst = prod.fst := by simp
    show (prod.map (𝟙 Y) (c.π.app i) : (Y ⨯ c.pt : Over X.left) ⟶ Y ⨯ D.obj i).left ≫
        ((prod.fst : Y ⨯ D.obj i ⟶ Y).left ≫ p) = (prod.fst : Y ⨯ c.pt ⟶ Y).left ≫ p
    rw [← Category.assoc, ← Over.comp_left, key]
  let L := Over.lift H q
  let cL : Cone L := Over.liftCone H q cH cp hcp
  have hcL : IsLimit ((Over.forget U ⋙ B.inclusion).mapCone cL) :=
    isLimit_map_prodMapCone (Over.forget X.left ⋙ B.inclusion) hc Y
  obtain ⟨hl⟩ := hloc I L cL hcL
    (fun i ↦ by
      have : IsAffine (B.inclusion.obj (D.obj i).left) := hD i
      exact isAffine_prod_over B X.left Y (D.obj i))
    (by
      have : IsAffine (B.inclusion.obj c.pt.left) := hcpt
      exact isAffine_prod_over B X.left Y c.pt)
  let M := D ⋙ G ⋙ Over.map X.hom
  let cM : Cone M := (Over.map X.hom).mapCone (G.mapCone c)
  let e : L ⋙ Over.map f ≅ M := NatIso.ofComponents
    (fun i ↦ Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans (prod_fst_left_comp_comp (D.obj i) hp).symm))
    (by intro i j g; ext; simp [L, M, H, G])
  let ep : (Over.map f).obj cL.pt ≅ cM.pt :=
    Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans (prod_fst_left_comp_comp c.pt hp).symm)
  apply isColimit_mapCocone_of_iso F ((Over.map f).mapCone cL) cM e ep
  · intro i
    apply Over.OverMorphism.ext
    show 𝟙 ((Y ⨯ c.pt : Over X.left).left) ≫
        (prod.map (𝟙 Y) (c.π.app i) : (Y ⨯ c.pt : Over X.left) ⟶ Y ⨯ D.obj i).left =
      (prod.map (𝟙 Y) (c.π.app i) : (Y ⨯ c.pt : Over X.left) ⟶ Y ⨯ D.obj i).left ≫
        𝟙 ((Y ⨯ D.obj i : Over X.left).left)
    rw [Category.id_comp, Category.comp_id]
  · exact ⟨hl⟩

/-- Limit preservation for an fppf sheaf can be checked on an fppf cover of
the base scheme. -/
@[stacks 049P]
public theorem limitPreserving_of_fppfCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (E : PreZeroHypercover.{u + 1} (B.obj hS))
    (hE : IsFppfCovering ⟨B.obj hS, E⟩)
    (hlocal : ∀ i : E.I₀,
      LimitPreserving.{u, v, w, w', u + 1}
        (Over.forget (E.X i) ⋙ B.inclusion)
        ((Over.map (E.f i)).op ⋙ F)) :
    LimitPreserving.{u, v, w, w', u + 1}
      (BigFppfOver.toScheme B S hS) F := by
  classical
  intro I _ _ D c hc hD hT
  let i₀ : I := IsCofiltered.nonempty.some
  let X := D.obj i₀
  let H : I ⥤ B.Schemes := D ⋙ Over.forget (B.obj hS)
  let cH : Cone H := (Over.forget (B.obj hS)).mapCone c
  have hcH : IsLimit cH := isLimitOfReflects B.inclusion hc
  let Dt : Over i₀ ⥤ Over X.left := Over.post H
  let ct : Cone Dt := (Over.conePost H i₀).obj cH
  have hct : IsLimit ((Over.forget X.left ⋙ B.inclusion).mapCone ct) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀)
      ((BigFppfOver.toScheme B S hS).mapCone c)).symm hc
  let : IsAffine (B.inclusion.obj X.left) := hD i₀
  let P : PreZeroHypercover.{u + 1} X.left := E.pullback₂ X.hom
  have hP : IsFppfCovering ⟨X.left, P⟩ :=
    Precoverage.mem_coverings_of_isPullback E.f hE X.hom
      (fun j ↦ pullback.snd (E.f j) X.hom)
      (fun j ↦ pullback.fst (E.f j) X.hom)
      (fun j ↦ (IsPullback.of_hasPullback (E.f j) X.hom).flip)
  obtain ⟨Q, q, hfin, hQ, haff⟩ := finite_affine_refinement B X.left P hP
  have : Finite Q.I₀ := hfin
  let s : Q.I₀ → E.I₀ := q.s₀
  let h : ∀ k : Q.I₀, Q.X k ⟶ pullback (E.f (s k)) X.hom := q.h₀
  have hw (k : Q.I₀) : h k ≫ pullback.snd (E.f (s k)) X.hom = Q.f k := q.w₀ k
  let Y : Q.I₀ → Over X.left := fun k ↦ Over.mk (Q.f k)
  let p (k : Q.I₀) : (Y k).left ⟶ E.X (s k) :=
    h k ≫ pullback.fst (E.f (s k)) X.hom
  have hp (k) : p k ≫ E.f (s k) = (Y k).hom ≫ X.hom := by
    show (h k ≫ pullback.fst (E.f (s k)) X.hom) ≫ E.f (s k) = Q.f k ≫ X.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hcol : Nonempty (IsColimit (((Over.map X.hom).op ⋙ F).mapCocone ct.op)) := by
    apply isColimit_of_products ((Over.map X.hom).op ⋙ F) Dt ct Y
      (fun Z ↦ isSheafFor_products B S hS F hF X Q hQ Z)
    · intro k
      let : IsAffine (B.inclusion.obj (Y k).left) := haff k
      exact isColimit_product_of_local B S hS F _ _ (hlocal (s k))
        X (Y k) (p k) (hp k) Dt ct hct (fun i ↦ hD i.left) hT
    · intro k l
      let : IsAffine (B.inclusion.obj (Y k).left) := haff k
      let : IsAffine (B.inclusion.obj (Y l).left) := haff l
      let : IsAffine (B.inclusion.obj (Y k ⨯ Y l).left) :=
        isAffine_prod_over B X.left (Y k) (Y l)
      apply isColimit_product_of_local B S hS F _ _ (hlocal (s k))
        X (Y k ⨯ Y l) ((prod.fst : Y k ⨯ Y l ⟶ Y k).left ≫ p k)
        ?_ Dt ct hct (fun i ↦ hD i.left) hT
      exact prod_fst_left_comp_comp _ (hp k)
  let M := Dt ⋙ Over.map X.hom
  let cM : Cone M := (Over.map X.hom).mapCone ct
  let e : M ≅ Over.forget i₀ ⋙ D := NatIso.ofComponents
    (fun i ↦ Over.isoMk (Iso.refl _) (by
      show 𝟙 ((D.obj i.left).left) ≫ (D.obj i.left).hom =
        (D.map i.hom).left ≫ (D.obj i₀).hom
      rw [Category.id_comp, Over.w]))
    (by intro i j f; ext; simp [M, Dt, H])
  let ep : cM.pt ≅ c.pt := Over.isoMk (Iso.refl _) (by
    show 𝟙 (c.pt.left) ≫ c.pt.hom = (c.π.app i₀).left ≫ (D.obj i₀).hom
    rw [Category.id_comp, Over.w]
    rfl)
  have htail := isColimit_mapCocone_of_iso F cM (c.whisker (Over.forget i₀)) e ep
    (by
      intro i
      apply Over.OverMorphism.ext
      have h1 : ep.hom.left = 𝟙 c.pt.left := rfl
      have h2 : (e.hom.app i).left = 𝟙 (D.obj i.left).left := rfl
      have h3 : (cM.π.app i).left = (c.π.app i.left).left := rfl
      have h4 : (Cone.whisker (Over.forget i₀) c).π.app i = c.π.app i.left := rfl
      rw [h4, Over.comp_left, Over.comp_left, h1, h2, h3]
      exact (Category.id_comp _).trans (Category.comp_id _).symm) hcol
  exact ⟨Functor.Final.isColimitWhiskerEquiv (Over.forget i₀).op
    (F.mapCocone c.op) htail.some⟩

end AlgebraicGeometry
