module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram

/-!
# Faithfulness of the relative finite Hilbert stack over the absolute one

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a positive integer. The 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` forgets the object of
`𝒴` and the identification of `F x` with its restriction, keeping the cover and the object of
`𝒳`. It is faithful: a morphism of the relative finite Hilbert category is determined by its
base, cover and `𝒳` components.

## Main results

* `AlgebraicGeometry.Stack.forgetRelativeStructure_faithful`: for a positive degree `d`, the
  1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful.

## References

* [Stacks Project, Tag 05XV](https://stacks.math.columbia.edu/tag/05XV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₁ u₁ v₂ u₂

namespace AlgebraicGeometry.Stack

/-- An endomorphism of an object lying over `U` which lies over the identity of `U` is an
endomorphism of the fibre category over `U`. -/
private theorem fibreHom_of_isHomLift_id {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂}
    [Category.{v₂} 𝒮] (p : 𝒮 ⥤ 𝒞) {U : 𝒞} {a : 𝒮} (ha : p.obj a = U) {φ : a ⟶ a}
    (h : p.IsHomLift (𝟙 U) φ) : p.FibreHom a a ha ha φ := by
  subst ha
  simp only [CategoryTheory.Functor.FibreHom, eqToHom_refl, Category.comp_id]
  exact h

/-- The identity of an object lying over `U` is a morphism of the fibre category over `U`. -/
private theorem fibreHom_id {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
    (p : 𝒮 ⥤ 𝒞) {U : 𝒞} {a : 𝒮} (ha : p.obj a = U) : p.FibreHom a a ha ha (𝟙 a) :=
  fibreHom_of_isHomLift_id p ha (by subst ha; infer_instance)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- A finite locally free morphism of positive degree `d` is surjective. -/
private theorem surjective_of_isFiniteLocallyFreeOfRank (hd : 0 < d) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] : Surjective f := by
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    f).mp (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d)
  have : IsFinite f := h.1
  have : Flat f := h.2.1
  refine f.one_le_finrank_iff_surjective.mp fun y => ?_
  show 1 ≤ Scheme.Hom.finrank f y
  rw [(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f d).mp inferInstance y]
  exact hd

/-- The degree-`d` cover of an object of the relative finite Hilbert category generates a
covering sieve of the big fppf site when `d` is positive. -/
private theorem cover_mem_topology (P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) (hd : 0 < d) :
    Sieve.generate (Presieve.singleton P.q) ∈ BigFppfOver.topology B S hS P.U := by
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
    ((BigFppfOver.toScheme B S hS).map P.q) d := P.finiteLocallyFree
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    ((BigFppfOver.toScheme B S hS).map P.q)).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS P.q
    (surjective_of_isFiniteLocallyFreeOfRank hd _) h.2.1 h.2.2

/-- An endomorphism `δ` of `y` lying over the identity of `U` whose restriction along the
degree-`d` cover `Z ⟶ U` is the identity is itself the identity, provided `d` is positive. -/
private theorem eq_id_of_comp_alpha_eq (P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) (hd : 0 < d)
    (δ : P.y ⟶ P.y) (hδ : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) δ)
    (hαδ : P.α ≫ δ = P.α) : δ = 𝟙 P.y := by
  have hα : 𝒴.toBasedCategory.p.IsHomLift P.q P.α := P.α_over
  have hαcart : 𝒴.toBasedCategory.p.IsStronglyCartesian P.q P.α :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift P.q P.α
  have hdom : 𝒴.toBasedCategory.p.obj (F.obj P.x) = P.Z :=
    IsHomLift.domain_eq 𝒴.toBasedCategory.p P.q P.α
  let xr : 𝒴.toBasedCategory.p.Restriction P.q P.y P.y_over :=
    Functor.Restriction.ofCartesian hdom P.y_over P.α hαcart
  let V : PUnit.{w + 1} → BigFppfOver B S hS := fun _ => P.Z
  let f0 : ∀ i, V i ⟶ P.U := fun _ => P.q
  let W : PUnit.{w + 1} → PUnit.{w + 1} → BigFppfOver B S hS := fun _ _ => pullback P.q P.q
  let pr1 : ∀ i j, W i j ⟶ V i := fun _ _ => pullback.fst P.q P.q
  let pr2 : ∀ i j, W i j ⟶ V j := fun _ _ => pullback.snd P.q P.q
  have hW : ∀ i j, IsPullback (pr1 i j) (pr2 i j) (f0 i) (f0 j) :=
    fun _ _ => IsPullback.of_hasPullback P.q P.q
  let xrW : ∀ i j, 𝒴.toBasedCategory.p.Restriction (pr1 i j ≫ f0 i) P.y P.y_over := fun _ _ =>
    Functor.Restriction.ofIsFiberedInGroupoids 𝒴.toBasedCategory.p
      𝒴.isStackInGroupoids.isFiberedInGroupoids (pullback.fst P.q P.q ≫ P.q) P.y P.y_over
  have hcover : Sieve.ofArrows V f0 ∈ BigFppfOver.topology B S hS P.U := by
    simpa [V, f0, Sieve.ofArrows, Presieve.ofArrows_pUnit] using cover_mem_topology P hd
  obtain ⟨g, -, hguniq⟩ := 𝒴.isStackInGroupoids.isom_isSheaf P.y P.y P.y_over P.y_over
    V f0 hcover W pr1 pr2 hW (fun _ => xr) (fun _ => xr) xrW xrW
    (fun _ => 𝟙 xr.pt) (fun _ => fibreHom_id _ _) (fun _ => inferInstance)
    (fun i j => ⟨𝟙 (xrW i j).pt, fibreHom_id _ _,
      by simp [CategoryTheory.Functor.IsRestrictionOf],
      by simp [CategoryTheory.Functor.IsRestrictionOf]⟩)
  have hδ' : 𝒴.toBasedCategory.p.IsHomLift (𝟙 (𝒴.toBasedCategory.p.obj P.y)) δ := by
    rw [P.y_over]; exact hδ
  refine (hguniq δ ⟨fibreHom_of_isHomLift_id _ P.y_over hδ, ?_, ?_⟩).trans
    (hguniq (𝟙 P.y) ⟨fibreHom_id _ P.y_over, inferInstance, ?_⟩).symm
  · exact Functor.isIso_of_isHomLift_id 𝒴.toBasedCategory.p
      𝒴.isStackInGroupoids.isFiberedInGroupoids δ hδ'
  · intro _
    show P.α ≫ δ = 𝟙 (F.obj P.x) ≫ P.α
    simpa using hαδ
  · intro _
    show P.α ≫ 𝟙 P.y = 𝟙 (F.obj P.x) ≫ P.α
    simp

/-- For a positive degree `d`, the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` from the relative to the
absolute finite Hilbert category is faithful. -/
@[stacks 05XV]
theorem forgetRelativeStructure_faithful (hd : 0 < d) :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS)
      (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor.Faithful := by
  refine ⟨fun {P Q} φ ψ h => ?_⟩
  have hf : φ.f = ψ.f := congrArg (fun z => z.cover.f) h
  have hg : φ.g = ψ.g := congrArg (fun z => z.cover.g) h
  have ha : φ.a = ψ.a := congrArg (fun z => z.a) h
  refine FiniteHilbert.Hom.ext hf hg ?_ ha
  have hbφ : 𝒴.toBasedCategory.p.IsHomLift φ.f φ.b := φ.b_over
  have hbψ : 𝒴.toBasedCategory.p.IsHomLift ψ.f ψ.b := ψ.b_over
  have hbcart : 𝒴.toBasedCategory.p.IsStronglyCartesian φ.f φ.b :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.f φ.b
  obtain ⟨δ, ⟨hδlift, hδfac⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒴.toBasedCategory.p φ.f φ.b
      (𝟙 P.U) ψ.f (by rw [Category.id_comp]; exact hf.symm) ψ.b
  have hα : 𝒴.toBasedCategory.p.IsHomLift P.q P.α := P.α_over
  have hcomp : 𝒴.toBasedCategory.p.IsHomLift P.q (P.α ≫ δ) := by
    rw [← Category.comp_id P.q]
    infer_instance
  have hαδ : P.α ≫ δ = P.α := by
    refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p φ.f φ.b P.q ?_
    rw [Category.assoc, hδfac, ← ψ.compatible, ← ha, φ.compatible]
  rw [← hδfac, eq_id_of_comp_alpha_eq P hd δ hδlift hαδ, Category.id_comp]

end AlgebraicGeometry.Stack

end
