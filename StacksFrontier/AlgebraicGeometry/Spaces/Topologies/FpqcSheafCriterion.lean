module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SliceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity

/-!
# The fpqc sheaf condition on the slice over an algebraic space

Let `X` be an algebraic space over `S` and let `F` be a presheaf of sets on the slice category of
algebraic spaces over `X`. If `F` satisfies étale descent, then to check that it satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `X` it suffices to check
it for the finite fpqc coverings of affine schemes by affine schemes.

## Main definitions

* `AlgebraicGeometry.Space.IsAffineFpqcSheafOver` — the sheaf condition for the finite fpqc
  families of affine schemes over an affine scheme over `X`.

## Main results

* `AlgebraicGeometry.Space.eq_of_isFpqcCovering` — granted étale descent and affine fpqc
  descent, two sections which agree on the members of an fpqc covering family agree.
* `AlgebraicGeometry.Space.isSheafFor_of_isFpqcCovering` — **granted étale descent and affine
  fpqc descent, the sheaf condition holds for every fpqc covering family of algebraic spaces
  over `X`.**

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (F : (Over X)ᵒᵖ ⥤ Type w)

/-! ### Affine scheme-valued points of an object of the slice -/

/-- The object of the slice over `X` given by a scheme-valued point `h` of an object `U` of the
slice: the represented algebraic space, mapping to `X` through `U`. -/
abbrev slicePoint (U : Over X) {T : BigFppfOver B S hS} (h : yoneda.obj T ⟶ U.left.obj) :
    Over X :=
  Over.mk ((ObjectProperty.homMk h : (schemeSpaceFunctor B S hS).obj T ⟶ U.left) ≫ U.hom)

/-- The morphism of the slice over `X` underlying a scheme-valued point. -/
abbrev slicePointHom (U : Over X) {T : BigFppfOver B S hS} (h : yoneda.obj T ⟶ U.left.obj) :
    slicePoint B S hS X U h ⟶ U :=
  Over.homMk (ObjectProperty.homMk h)

/-! ### The affine fpqc sheaf condition -/

/-- Descent for the finite affine fpqc families over an affine scheme over `X`: for every affine
object `T` of the big fppf site of `S` with a morphism `a` to `X`, and every finite family of
affine objects over `T` whose underlying family of schemes is an fpqc covering, the presheaf
satisfies the sheaf condition for the family, read in the slice over `X`. -/
def IsAffineFpqcSheafOver : Prop :=
  ∀ (T : BigAffineFppf B S hS)
    (a : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X)
    (R : PreZeroHypercover.{u + 1} T), Finite R.I₀ →
    Presieve.map (BigAffineFppf.toScheme B S hS) R.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T) →
    Presieve.IsSheafFor F (Presieve.ofArrows
      (fun j ↦ Over.mk ((schemeSpaceFunctor B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫ a))
      (fun j ↦ (Over.homMk ((schemeSpaceFunctor B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (R.f j))) : _ ⟶ Over.mk a)))

variable {B S hS X F}

/-! ### Étale descent along an affine étale covering -/

/-- Étale descent for a family indexed in `Type (u + 1)`: a presheaf satisfying étale descent
satisfies the sheaf condition for every étale covering family of the slice indexed in
`Type (u + 1)`. -/
theorem isSheafFor_of_isEtaleCovering (h₁ : IsEtaleSheafOnSlice B S hS X F) {U : Over X}
    {I : Type (u + 1)} {V : I → Over X} (f : ∀ i, V i ⟶ U)
    (hf : IsEtaleCovering B S hS (fun i ↦ (V i).left.1) (fun i ↦ (f i).left.hom)) :
    Presieve.IsSheafFor F (Presieve.ofArrows V f) := by
  have he : Presieve.ofArrows (fun i : ULift.{u + 2} I ↦ V i.down) (fun i ↦ f i.down) =
      Presieve.ofArrows V f :=
    Presieve.ofArrows_comp_eq_of_surjective f (a := ULift.down) fun i ↦ ⟨⟨i⟩, rfl⟩
  rw [← he]
  exact h₁ U ⟨ULift.{u + 2} I, fun i ↦ V i.down, fun i ↦ f i.down⟩
    (hf.reindex B S hS (σ := ULift.down) fun i ↦ ⟨⟨i⟩, rfl⟩)

/-- Every object of the slice over `X` has an étale covering family by objects represented by
affine schemes of the big fppf site, indexed by its points. -/
theorem exists_affine_etale_cover (U : Over X) :
    ∃ (W : points B S hS U.left.obj → BigAffineFppf B S hS)
      (b : ∀ x, yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (W x)) ⟶ U.left.obj),
      IsEtaleCovering B S hS (fun x ↦ (slicePoint B S hS X U (b x)).left.1)
        (fun x ↦ (slicePointHom B S hS X U (b x)).left.hom) := by
  obtain ⟨W, b, hWaff, -, -, hcov⟩ :=
    exists_isEtaleCovering_affine B S hS U.left.obj U.left.property
  exact ⟨fun x ↦ ⟨W x, hWaff x⟩, b, hcov⟩

/-! ### Refining an fpqc covering over an affine point -/

section Refinement

variable {U : Over X} {I : Type v} {V : I → Over X} (f : ∀ i, V i ⟶ U)

/-- A member of a finite affine refinement of an fpqc family over an affine point `h` of `U`,
as an object of the slice over `X`. -/
abbrev refinementOver {T : BigAffineFppf B S hS}
    (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ U.left.obj)
    (R : PreZeroHypercover.{u + 1} T) (j : R.I₀) : Over X :=
  Over.mk ((schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫
    (slicePoint B S hS X U h).hom)

/-- The structure morphism of a member of a refinement to the affine point. -/
abbrev refinementOverHom {T : BigAffineFppf B S hS}
    (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ U.left.obj)
    (R : PreZeroHypercover.{u + 1} T) (j : R.I₀) :
    refinementOver (X := X) h R j ⟶ slicePoint B S hS X U h :=
  Over.homMk ((schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (R.f j)))

/-- The factorization of a member of a refinement through a member of the family, as a morphism
of the slice over `X`. -/
abbrev refinementLift {T : BigAffineFppf B S hS}
    (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ U.left.obj)
    (R : PreZeroHypercover.{u + 1} T) (j : R.I₀) (i : I)
    (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (R.X j)) ⟶ (V i).left.obj)
    (ha : a ≫ (f i).left.hom =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫ h) :
    refinementOver (X := X) h R j ⟶ V i :=
  let a' : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (R.X j)) ⟶
      (V i).left := ObjectProperty.homMk a
  have ha' : a' ≫ (f i).left =
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫
        ObjectProperty.homMk h := ObjectProperty.hom_ext _ ha
  Over.homMk a' (by
    change a' ≫ (V i).hom = _
    rw [← Over.w (f i), ← Category.assoc, ha', Category.assoc]
    rfl)

/-- The factorization commutes over `U`. -/
theorem refinementLift_comp {T : BigAffineFppf B S hS}
    (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ U.left.obj)
    (R : PreZeroHypercover.{u + 1} T) (j : R.I₀) (i : I)
    (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (R.X j)) ⟶ (V i).left.obj)
    (ha : a ≫ (f i).left.hom =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫ h) :
    refinementLift f h R j i a ha ≫ f i =
      refinementOverHom h R j ≫ slicePointHom B S hS X U h := by
  exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ ha)

end Refinement

/-! ### Separatedness -/

/-- **Granted étale and affine fpqc descent, two sections agreeing on the members of an fpqc
covering family agree.** -/
theorem eq_of_isFpqcCovering (h₁ : IsEtaleSheafOnSlice B S hS X F)
    (h₂ : IsAffineFpqcSheafOver B S hS X F) {U : Over X} {I : Type v} {V : I → Over X}
    (f : ∀ i, V i ⟶ U) (hf : IsFpqcCovering B S hS (fun i ↦ (f i).left.hom))
    {t₁ t₂ : F.obj (op U)} (h : ∀ i, F.map (f i).op t₁ = F.map (f i).op t₂) : t₁ = t₂ := by
  obtain ⟨W, b, hcov⟩ := exists_affine_etale_cover (B := B) (S := S) (hS := hS) U
  refine (isSheafFor_of_isEtaleCovering h₁ _ hcov).isSeparatedFor.ext fun Z g hg ↦ ?_
  obtain ⟨x⟩ := hg
  obtain ⟨R, hfin, hR, hfac⟩ := hf.2 (W x) (b x)
  choose i a ha using hfac
  refine (h₂ (W x) (slicePoint B S hS X U (b x)).hom R hfin hR).isSeparatedFor.ext
    fun Z' g' hg' ↦ ?_
  obtain ⟨j⟩ := hg'
  have hc := refinementLift_comp f (b x) R j (i j) (a j) (ha j)
  show F.map (refinementOverHom (b x) R j).op (F.map (slicePointHom B S hS X U (b x)).op t₁) =
    F.map (refinementOverHom (b x) R j).op (F.map (slicePointHom B S hS X U (b x)).op t₂)
  have key : ∀ t, F.map (refinementOverHom (b x) R j).op
      (F.map (slicePointHom B S hS X U (b x)).op t) =
        F.map (refinementLift f (b x) R j (i j) (a j) (ha j)).op (F.map (f (i j)).op t) := by
    intro t
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      hc]
  rw [key, key, h]

/-- Separatedness for an fpqc covering family, in the form of `Presieve.IsSeparatedFor`. -/
theorem isSeparatedFor_of_isFpqcCovering (h₁ : IsEtaleSheafOnSlice B S hS X F)
    (h₂ : IsAffineFpqcSheafOver B S hS X F) {U : Over X} {I : Type v} {V : I → Over X}
    (f : ∀ i, V i ⟶ U) (hf : IsFpqcCovering B S hS (fun i ↦ (f i).left.hom)) :
    Presieve.IsSeparatedFor F (Presieve.ofArrows V f) := by
  intro x t₁ t₂ ht₁ ht₂
  exact eq_of_isFpqcCovering h₁ h₂ f hf fun i ↦
    (ht₁ _ (Presieve.ofArrows.mk i)).trans (ht₂ _ (Presieve.ofArrows.mk i)).symm

/-- Two sections agree if their restrictions to the base change of an fpqc covering family agree. -/
private theorem eq_of_isFpqcCovering_pullback (h₁ : IsEtaleSheafOnSlice B S hS X F)
    (h₂ : IsAffineFpqcSheafOver B S hS X F) {U W : Over X} {I : Type v} {V : I → Over X}
    (f : ∀ i, V i ⟶ U) (hf : IsFpqcCovering B S hS (fun i ↦ (f i).left.hom)) (g : W ⟶ U)
    {t₁ t₂ : F.obj (op W)}
    (h : ∀ i, F.map (sliceFiberProductSnd B S hS X (f i) g).op t₁ =
      F.map (sliceFiberProductSnd B S hS X (f i) g).op t₂) : t₁ = t₂ :=
  eq_of_isFpqcCovering h₁ h₂ _
    (isFpqcCovering_pullback B S hS (fun i ↦ (f i).left) g.left hf) h

/-! ### A finite affine fpqc family is an fpqc covering of algebraic spaces -/

/-- **A finite fpqc family of affine schemes over an affine scheme of the site is an fpqc covering
of the represented algebraic spaces.** -/
theorem isFpqcCovering_yoneda_of_mem_fpqcPrecoverage {T : BigAffineFppf B S hS}
    (R : PreZeroHypercover.{u + 1} T) [Finite R.I₀]
    (hR : Presieve.map (BigAffineFppf.toScheme B S hS) R.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T)) :
    IsFpqcCovering B S hS (fun j ↦ yoneda.map ((BigAffineFppf.inclusion B S hS).map (R.f j))) := by
  let G := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  have hR' : Presieve.ofArrows (fun j ↦ G.obj (A.obj (R.X j))) (fun j ↦ G.map (A.map (R.f j))) ∈
      Scheme.fpqcPrecoverage (G.obj (A.obj T)) := by
    rwa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hR
  have hflat : ∀ j, Flat (G.map (A.map (R.f j))) := fun j ↦
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hR'.2).2 j
  refine ⟨fun j ↦ isFlat_yoneda_map B S hS _ (hflat j), fun T' h ↦ ?_⟩
  let φ : A.obj T' ⟶ A.obj T := yoneda.preimage h
  have hφ : yoneda.map φ = h := yoneda.map_preimage _
  have sq : ∀ j, IsPullback (G.map (pullback.fst φ (A.map (R.f j))))
      (G.map (pullback.snd φ (A.map (R.f j)))) (G.map φ) (G.map (A.map (R.f j))) :=
    fun j ↦ (IsPullback.of_hasPullback φ (A.map (R.f j))).map G
  have hT' : IsAffine (G.obj (A.obj T')) := T'.property
  have hRj : ∀ j, IsAffine (G.obj (A.obj (R.X j))) := fun j ↦ (R.X j).property
  have hT : IsAffine (G.obj (A.obj T)) := T.property
  have hP : ∀ j, IsAffine (G.obj (pullback φ (A.map (R.f j)))) :=
    fun j ↦ IsAffine.of_isIso (sq j).isoPullback.hom
  let R' : PreZeroHypercover.{u + 1} T' :=
    { I₀ := R.I₀
      X := fun j ↦ ⟨pullback φ (A.map (R.f j)), hP j⟩
      f := fun j ↦ ObjectProperty.homMk (pullback.fst φ (A.map (R.f j))) }
  refine ⟨R', ‹Finite R.I₀›, ?_, fun j ↦ ⟨j, yoneda.map (pullback.snd φ (A.map (R.f j))), ?_⟩⟩
  · rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
    exact Precoverage.mem_coverings_of_isPullback (J := Scheme.fpqcPrecoverage) _ hR' (G.map φ)
        (fun j ↦ G.map (pullback.fst φ (A.map (R.f j))))
        (fun j ↦ G.map (pullback.snd φ (A.map (R.f j)))) sq
  · show yoneda.map (pullback.snd φ (A.map (R.f j))) ≫ yoneda.map (A.map (R.f j)) =
      yoneda.map (pullback.fst φ (A.map (R.f j))) ≫ h
    rw [← hφ, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-! ### Gluing -/

section Gluing

variable {U : Over X} {I : Type v} {V : I → Over X} (f : ∀ i, V i ⟶ U)

/-- **A section glued over an affine point from a finite affine refinement restricts as the
family does.** Let `z` be a section over an affine point `h` of `U` whose restrictions to the
members of a finite affine refinement of the family are the corresponding restrictions of a
compatible family `x`. Then for any morphism `g : Z ⟶ h` and any factorization `c : Z ⟶ V k` of
`g` through a member of the family, the restriction of `z` along `g` is that of `x k` along
`c`. -/
theorem map_eq_of_refinement (h₁ : IsEtaleSheafOnSlice B S hS X F)
    (h₂ : IsAffineFpqcSheafOver B S hS X F) {x : ∀ i, F.obj (op (V i))}
    (hx : Presieve.Arrows.Compatible F f x) {T : BigAffineFppf B S hS}
    (h : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ U.left.obj)
    (R : PreZeroHypercover.{u + 1} T) [Finite R.I₀]
    (hR : Presieve.map (BigAffineFppf.toScheme B S hS) R.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T))
    (i : R.I₀ → I)
    (a : ∀ j, yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (R.X j)) ⟶ (V (i j)).left.obj)
    (ha : ∀ j, a j ≫ (f (i j)).left.hom =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (R.f j)) ≫ h)
    (z : F.obj (op (slicePoint B S hS X U h)))
    (hz : ∀ j, F.map (refinementOverHom h R j).op z =
      F.map (refinementLift f h R j (i j) (a j) (ha j)).op (x (i j)))
    {Z : Over X} (g : Z ⟶ slicePoint B S hS X U h) (k : I) (c : Z ⟶ V k)
    (hc : c ≫ f k = g ≫ slicePointHom B S hS X U h) :
    F.map g.op z = F.map c.op (x k) := by
  refine eq_of_isFpqcCovering_pullback h₁ h₂ (fun j ↦ refinementOverHom (X := X) h R j)
    (isFpqcCovering_yoneda_of_mem_fpqcPrecoverage R hR) g fun j ↦ ?_
  have hw := (sliceFiberProduct_isPullback B S hS X (refinementOverHom (X := X) h R j) g).w
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    ← hw, op_comp, FunctorToTypes.map_comp_apply, hz j, ← FunctorToTypes.map_comp_apply,
    ← op_comp]
  refine hx _ _ _ _ _ ?_
  rw [Category.assoc, refinementLift_comp, ← Category.assoc, hw, Category.assoc, Category.assoc,
    hc]

end Gluing

/-- **Reduction of the fpqc sheaf condition to affine schemes.** A presheaf on the slice category
of algebraic spaces over `X` which satisfies étale descent, and the sheaf condition for the finite
fpqc families of affine schemes over an affine scheme over `X`, satisfies the sheaf condition for
every family of the slice whose underlying family of algebraic spaces is an fpqc covering
(Stacks 03MQ). -/
theorem isSheafFor_of_isFpqcCovering (h₁ : IsEtaleSheafOnSlice B S hS X F)
    (h₂ : IsAffineFpqcSheafOver B S hS X F) {U : Over X} {I : Type v} {V : I → Over X}
    (f : ∀ i, V i ⟶ U) (hf : IsFpqcCovering B S hS (fun i ↦ (f i).left.hom)) :
    Presieve.IsSheafFor F (Presieve.ofArrows V f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  obtain ⟨W, b, hcov⟩ := exists_affine_etale_cover (B := B) (S := S) (hS := hS) U
  choose R hfin hR hfac using fun p ↦ hf.2 (W p) (b p)
  choose i a ha using hfac
  have hz : ∀ p, ∃ z : F.obj (op (slicePoint B S hS X U (b p))), ∀ j,
      F.map (refinementOverHom (b p) (R p) j).op z =
        F.map (refinementLift f (b p) (R p) j (i p j) (a p j) (ha p j)).op (x (i p j)) := by
    intro p
    refine (((Presieve.isSheafFor_arrows_iff _ _).mp
      (h₂ (W p) (slicePoint B S hS X U (b p)).hom (R p) (hfin p) (hR p)))
        (fun j ↦ F.map (refinementLift f (b p) (R p) j (i p j) (a p j) (ha p j)).op
          (x (i p j))) ?_).exists
    intro j j' Z gj gj' hg
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp]
    refine hx _ _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, refinementLift_comp, refinementLift_comp,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ slicePointHom B S hS X U (b p)) hg
  choose z hz using hz
  have hC : ∀ p {Z : Over X} (g : Z ⟶ slicePoint B S hS X U (b p)) (k : I) (c : Z ⟶ V k),
      c ≫ f k = g ≫ slicePointHom B S hS X U (b p) → F.map g.op (z p) = F.map c.op (x k) :=
    fun p _ g k c hc ↦ by
      have := hfin p
      exact map_eq_of_refinement f h₁ h₂ hx (b p) (R p) (hR p) (i p) (a p) (ha p) (z p) (hz p)
        g k c hc
  have hcompat : Presieve.Arrows.Compatible F (fun p ↦ slicePointHom B S hS X U (b p)) z := by
    intro p q Z gp gq hpq
    refine eq_of_isFpqcCovering_pullback h₁ h₂ f hf (gp ≫ slicePointHom B S hS X U (b p))
      fun k ↦ ?_
    have hw := (sliceFiberProduct_isPullback B S hS X (f k)
      (gp ≫ slicePointHom B S hS X U (b p))).w
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      hC p _ k _ (by rw [hw, Category.assoc]),
      hC q _ k _ (by rw [hw, Category.assoc, hpq])]
  obtain ⟨t, ht, -⟩ := ((Presieve.isSheafFor_arrows_iff _ _).mp
    (isSheafFor_of_isEtaleCovering h₁ _ hcov)) z hcompat
  have hall : ∀ k, F.map (f k).op t = x k := by
    intro k
    refine eq_of_isFpqcCovering_pullback h₁ h₂ (fun p ↦ slicePointHom B S hS X U (b p))
      (isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov) (f k) fun p ↦ ?_
    have hw := (sliceFiberProduct_isPullback B S hS X (slicePointHom B S hS X U (b p)) (f k)).w
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← hw, op_comp, FunctorToTypes.map_comp_apply,
      ht p]
    exact hC p _ k _ hw.symm
  exact ⟨t, hall, fun t' ht' ↦ eq_of_isFpqcCovering h₁ h₂ f hf fun k ↦ (ht' k).trans (hall k).symm⟩

end AlgebraicGeometry.Space

end
