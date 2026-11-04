module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct

/-!
# A coproduct of finitely many affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. An affine formal algebraic space over `S`
(Stacks 0AI7) is an fppf sheaf which satisfies the set-theoretic condition of Stacks 0AIS and
is a colimit of a nonempty directed system of affine schemes over `S` along thickenings. This
file proves that a coproduct of *finitely many* of them is again one, which is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma`.

Given presentations `Z i ≅ colim_{Idx i} D i` for `i` in a finite index type `I`, the combined
system is indexed by the product preorder `K = ∏ᵢ Idx i`, nonempty and directed because each
factor is, and its stage at `k ∈ K` is the coproduct `∐ᵢ (D i) (k i)`. That stage is an affine
scheme over `S` because a finite coproduct of affine schemes is affine, and the transition
morphisms are thickenings because a finite coproduct of thickenings is a thickening — both
summand-by-summand statements, the second by locality of closed immersions and of
surjectivity at the target. The colimit of the combined system is `∐ Z` because the coproduct
commutes with the colimits (Fubini), because the projections `K ⥤ Idx i` are final, and
because the sheafified Yoneda embedding carries a finite coproduct of the site to the
coproduct of the representable sheaves.

The set-theoretic condition is proved separately, in
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_sigma`: the coproduct `∐ᵢ Uᵢ` of
the objects of the site surjecting onto the `Z i` surjects onto `∐ Z`, and the kernel pair of
that surjection is the coproduct of the kernel pairs of the `Uᵢ ⟶ Z i`, which the coproduct
`∐ᵢ Rᵢ` therefore covers.

## Main results

* `CategoryTheory.Limits.nonempty_isColimit_cofan_kernelPair`: the kernel pair of a morphism
  of finite coproducts is the coproduct of the kernel pairs of its summands.
* `AlgebraicGeometry.Stacks.Thickenings.isThickening_sigmaMap` and
  `AlgebraicGeometry.Stacks.Thickenings.isThickening_of_cofan`: a finite coproduct of
  thickenings of schemes is a thickening.
* `CategoryTheory.PiOrder.final_proj`: the projections out of a product of nonempty directed
  preorders are final functors.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_sigma`: **Stacks 0AIS** for a
  finite coproduct.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma`: a coproduct of finitely
  many affine formal algebraic spaces over `S` is an affine formal algebraic space over `S`.

## Implementation notes

The statement carries no `@[stacks]` registration. The Stacks project uses it inside the proof
of Stacks 0AQD, where it appears as the bare assertion that "a finite union of formal affine
algebraic spaces is a formal affine algebraic space", with no tag of its own and with the
argument omitted; so it is an untagged step of a proof rather than a tagged statement.

Disjointness of the coproducts is never used. The usual route to the kernel pair of
`∐ᵢ Uᵢ ⟶ ∐ᵢ Z i` decomposes it into the blocks `Uᵢ ×_{∐ Z} U_j` and discards the off-diagonal
ones as initial, which needs disjointness of the coproduct of sheaves, available in this
library only for sheaves of types in the universe of the morphisms of the site and not for the
sheaves of `Type (u + 1)` in which formal algebraic spaces live. Instead
`CategoryTheory.Limits.nonempty_isColimit_cofan_kernelPair` exhibits the block `Uᵢ ×_{Z i} Uᵢ`
as the base change of the second projection of the kernel pair along the `i`-th inclusion, by
cancelling the kernel-pair square out of the square presenting it as `(∐ᵢ Uᵢ) ×_{∐ Z} Uᵢ`;
only universality of finite coproducts — `CategoryTheory.FinitaryExtensive` — is involved,
and that Mathlib provides for sheaves of types in any universe.

`CategoryTheory.PiOrder` wraps the product of the index preorders in a structure. On a bare
product of types carrying categories `CategoryTheory.pi` applies and gives the product of the
categories, whereas the index of a directed system must carry the category of the
coordinatewise *preorder*.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/-! ### Products of directed preorders -/

namespace CategoryTheory

/-- A product of preorders, as a type of its own. The point of the wrapper is the category
structure: on a bare product of types carrying categories, `CategoryTheory.pi` applies and
gives the product of the categories, whereas a directed system is indexed by the *preorder*
and so needs `CategoryTheory.Preorder.smallCategory` of the coordinatewise order. -/
structure PiOrder {Ix : Type w} (Idx : Ix → Type v) where
  /-- The underlying family. -/
  val : ∀ i, Idx i

namespace PiOrder

variable {Ix : Type w} {Idx : Ix → Type v} [∀ i, Preorder (Idx i)]

/-- The coordinatewise order: `x ≤ y` when `x.val i ≤ y.val i` for every `i`. -/
instance : Preorder (PiOrder Idx) where
  le x y := ∀ i, x.val i ≤ y.val i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := (h₁ i).trans (h₂ i)

/-- The order of `PiOrder Idx` is coordinatewise, by definition. -/
theorem le_def {x y : PiOrder Idx} : x ≤ y ↔ ∀ i, x.val i ≤ y.val i := Iff.rfl

/-- A product of nonempty preorders is nonempty. -/
instance [∀ i, Nonempty (Idx i)] : Nonempty (PiOrder Idx) :=
  ⟨⟨fun i ↦ Classical.arbitrary (Idx i)⟩⟩

/-- A product of directed preorders is directed: an upper bound of `x` and `y` is chosen
coordinate by coordinate. -/
instance [∀ i, IsDirectedOrder (Idx i)] : IsDirectedOrder (PiOrder Idx) := by
  classical
  refine ⟨fun x y ↦ ?_⟩
  choose m h₁ h₂ using fun i ↦ exists_ge_ge (x.val i) (y.val i)
  exact ⟨⟨m⟩, h₁, h₂⟩

/-- The `i`-th projection out of a product of preorders, as a functor. -/
def proj (i : Ix) : PiOrder Idx ⥤ Idx i :=
  Monotone.functor (f := fun x : PiOrder Idx ↦ x.val i) fun _ _ h ↦ h i

/-- The `i`-th projection sends `x` to its `i`-th coordinate. -/
@[simp]
theorem proj_obj (i : Ix) (x : PiOrder Idx) : (proj (Idx := Idx) i).obj x = x.val i := rfl

/-- **The projections out of a product of nonempty directed preorders are final.** Every object
of a factor is the `i`-th coordinate of some object of the product — fill the remaining
coordinates arbitrarily — and parallel morphisms of a preorder are equal, so the objects lying
over a fixed one form a directed, hence connected, family. Consequently a colimit over the
product computes the colimit over any one factor. -/
theorem final_proj [∀ i, Nonempty (Idx i)] [∀ i, IsDirectedOrder (Idx i)] (i : Ix) :
    (proj (Idx := Idx) i).Final := by
  classical
  refine Functor.final_of_exists_of_isFiltered _ (fun d ↦ ?_)
    (fun {_ x} _ _ ↦ ⟨x, 𝟙 x, by subsingleton⟩)
  exact ⟨⟨Function.update (fun j ↦ Classical.arbitrary (Idx j)) i d⟩,
    ⟨homOfLE (le_of_eq (by simp))⟩⟩

end PiOrder

end CategoryTheory

namespace CategoryTheory.Limits

/-- A kernel pair read through an isomorphism of the ambient object. -/
theorem IsPullback.kernelPair_compIso {C : Type*} [Category C] {P A A' Zz : C} {p q : P ⟶ A}
    {f : A ⟶ Zz} (h : IsPullback p q f f) (e : A' ≅ A) :
    IsPullback (p ≫ e.inv) (q ≫ e.inv) (e.hom ≫ f) (e.hom ≫ f) := by
  have hr : IsPullback e.inv f (e.hom ≫ f) (𝟙 Zz) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have s1 : IsPullback (p ≫ e.inv) q (e.hom ≫ f) f := by simpa using h.paste_horiz hr
  have s2 : IsPullback (q ≫ e.inv) (p ≫ e.inv) (e.hom ≫ f) (e.hom ≫ f) := by
    simpa using s1.flip.paste_horiz hr
  exact s2.flip

variable {C : Type*} [Category C] [FinitaryExtensive C] {ι : Type*} [Finite ι]
  {X Y : ι → C} {A Bv : C} {lam : ∀ i, X i ⟶ A} {sig : ∀ i, Y i ⟶ Bv}

/-- **A morphism of finite coproducts is the coproduct of its summands.** If `A` is the
coproduct of the `X i`, if `Bv` is the coproduct of the `Y i` and if `t : A ⟶ Bv` restricts on
the `i`-th summand to `a i : X i ⟶ Y i`, then `X i` is the base change of `t` along the `i`-th
inclusion of `Bv`. -/
theorem isPullback_of_isColimit_cofan (hX : IsColimit (Cofan.mk A lam))
    (hY : IsColimit (Cofan.mk Bv sig)) (a : ∀ i, X i ⟶ Y i) (t : A ⟶ Bv)
    (hcomm : ∀ i, lam i ≫ t = a i ≫ sig i) (i : ι) :
    IsPullback (lam i) (a i) t (sig i) :=
  (FinitaryExtensive.isVanKampen_finiteCoproducts hY (Cofan.mk A lam)
    (Discrete.natTrans fun j ↦ a j.as) t (by ext ⟨j⟩; simpa using (hcomm j).symm)
    (NatTrans.Equifibered.of_discrete _)).1 ⟨hX⟩ ⟨i⟩

/-- **The kernel pair of a morphism of finite coproducts is the coproduct of the kernel pairs
of its summands.** With `A`, `Bv` and `t` as in
`CategoryTheory.Limits.isPullback_of_isColimit_cofan`, let `P i` be the kernel pair of the
`i`-th summand `a i` and let `pb` be the kernel pair of `t`. Then `pb` is the coproduct of the
`P i`.

No disjointness of the coproducts is used: the comparison `P i ⟶ pb` is exhibited as the base
change of the second projection of `pb` along the `i`-th inclusion of `A`, by cancelling the
kernel-pair square of `t` out of the square which presents `P i` as `A ×_Bv X i`. -/
theorem nonempty_isColimit_cofan_kernelPair (hX : IsColimit (Cofan.mk A lam))
    (hY : IsColimit (Cofan.mk Bv sig)) {a : ∀ i, X i ⟶ Y i} {t : A ⟶ Bv}
    (hcomm : ∀ i, lam i ≫ t = a i ≫ sig i) {P : ι → C} {q₁ q₂ : ∀ i, P i ⟶ X i}
    (hP : ∀ i, IsPullback (q₁ i) (q₂ i) (a i) (a i)) {pb : C} {π₁ π₂ : pb ⟶ A}
    (hpb : IsPullback π₁ π₂ t t) (ρ : ∀ i, P i ⟶ pb)
    (hρ₁ : ∀ i, ρ i ≫ π₁ = q₁ i ≫ lam i) (hρ₂ : ∀ i, ρ i ≫ π₂ = q₂ i ≫ lam i) :
    Nonempty (IsColimit (Cofan.mk pb ρ)) := by
  have hq : ∀ i, IsPullback (lam i) (a i) t (sig i) :=
    isPullback_of_isColimit_cofan hX hY a t hcomm
  have hS : ∀ i, IsPullback (ρ i) (q₂ i) π₂ (lam i) := by
    intro i
    refine IsPullback.of_right (h₁₂ := π₁) ?_ (hρ₂ i) hpb
    rw [hρ₁ i, hcomm i]
    exact (hP i).paste_horiz (hq i)
  exact (FinitaryExtensive.isVanKampen_finiteCoproducts hX (Cofan.mk pb ρ)
    (Discrete.natTrans fun j ↦ q₂ j.as) π₂ (by ext ⟨j⟩; simpa using (hρ₂ j).symm)
    (NatTrans.Equifibered.of_discrete _)).2 fun j ↦ hS j.as

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {ι : Type v} [Finite ι] [Small.{u} ι] {X Y : ι → Scheme.{u}}

/-- **A property local at the target holds for a morphism of finite coproducts as soon as it
holds for each summand**, in the form carrying abstract colimit cofans rather than the chosen
coproducts. -/
theorem IsZariskiLocalAtTarget.of_cofan {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] {A Bv : Scheme.{u}} {lam : ∀ i, X i ⟶ A} {sig : ∀ i, Y i ⟶ Bv}
    (hA : IsColimit (Cofan.mk A lam)) (hB : IsColimit (Cofan.mk Bv sig))
    {a : ∀ i, X i ⟶ Y i} {t : A ⟶ Bv} (hcomm : ∀ i, lam i ≫ t = a i ≫ sig i)
    (ha : ∀ i, P (a i)) : P t := by
  let eA : A ≅ ∐ X := hA.coconePointUniqueUpToIso (coproductIsCoproduct X)
  let eB : Bv ≅ ∐ Y := hB.coconePointUniqueUpToIso (coproductIsCoproduct Y)
  have heA : ∀ i, Limits.Sigma.ι X i ≫ eA.inv = lam i := fun i ↦ by
    have h : lam i ≫ eA.hom = Limits.Sigma.ι X i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom hA (coproductIsCoproduct X) ⟨i⟩
    rw [← h]
    simp
  have heB : ∀ i, Limits.Sigma.ι Y i ≫ eB.inv = sig i := fun i ↦ by
    have h : sig i ≫ eB.hom = Limits.Sigma.ι Y i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom hB (coproductIsCoproduct Y) ⟨i⟩
    rw [← h]
    simp
  have ht : eA.inv ≫ t = Limits.Sigma.map a ≫ eB.inv := by
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    have h1 : Limits.Sigma.ι X i ≫ eA.inv ≫ t = a i ≫ sig i := by
      rw [← Category.assoc, heA i, hcomm i]
    have h2 : Limits.Sigma.ι X i ≫ Limits.Sigma.map a ≫ eB.inv = a i ≫ sig i := by
      rw [Limits.Sigma.ι_map_assoc, heB i]
    rw [h1, h2]
  have htt : t = eA.hom ≫ Limits.Sigma.map a ≫ eB.inv := by rw [← ht, Iso.hom_inv_id_assoc]
  rw [htt]
  exact (P.cancel_left_of_respectsIso _ _).2 ((P.cancel_right_of_respectsIso _ _).2
    (IsZariskiLocalAtTarget.sigmaMap a ha))

/-- A finite coproduct of thickenings is a thickening. -/
theorem Stacks.Thickenings.isThickening_sigmaMap (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Stacks.Thickenings.IsThickening (f i)) :
    Stacks.Thickenings.IsThickening (Limits.Sigma.map f) := by
  refine ⟨IsZariskiLocalAtTarget.sigmaMap f fun i ↦ (hf i).1, ?_⟩
  have : Surjective (Limits.Sigma.map f) :=
    IsZariskiLocalAtTarget.sigmaMap (P := @Surjective) f fun i ↦ ⟨(hf i).2⟩
  exact (Limits.Sigma.map f).surjective

/-- **A morphism of finite coproducts is a thickening as soon as each of its summands is**, in
the form carrying abstract colimit cofans. -/
theorem Stacks.Thickenings.isThickening_of_cofan {A Bv : Scheme.{u}} {lam : ∀ i, X i ⟶ A}
    {sig : ∀ i, Y i ⟶ Bv} (hA : IsColimit (Cofan.mk A lam)) (hB : IsColimit (Cofan.mk Bv sig))
    (a : ∀ i, X i ⟶ Y i) {t : A ⟶ Bv} (hcomm : ∀ i, lam i ≫ t = a i ≫ sig i)
    (ha : ∀ i, Stacks.Thickenings.IsThickening (a i)) :
    Stacks.Thickenings.IsThickening t := by
  refine ⟨IsZariskiLocalAtTarget.of_cofan hA hB hcomm fun i ↦ (ha i).1, ?_⟩
  have : AlgebraicGeometry.Surjective t :=
    IsZariskiLocalAtTarget.of_cofan (P := @AlgebraicGeometry.Surjective) hA hB hcomm
      fun i ↦ ⟨(ha i).2⟩
  exact t.surjective

/-! ### Finite coproducts in the big affine fppf category -/

namespace BigAffineFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type w} [Finite I] [Small.{u} I] (A : I → BigAffineFppf B S hS)

/-- The coproduct of a finite family of objects of the big affine fppf category over `S`:
the coproduct of the underlying objects of the big fppf category, which is again affine
because a finite coproduct of affine schemes is affine. -/
noncomputable def sigmaObj : BigAffineFppf B S hS :=
  ⟨BigFppfOver.sigmaObj B S hS fun i ↦ (inclusion B S hS).obj (A i), by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj _)
    rw [BigFppfOver.toScheme_obj_sigmaObj]
    exact inferInstanceAs (IsAffine (∐ fun i ↦ (toScheme B S hS).obj (A i)))⟩

/-- The `i`-th inclusion into the coproduct of a finite family of objects of the big affine
fppf category over `S`. -/
noncomputable def sigmaIncl (i : I) : A i ⟶ sigmaObj B S hS A :=
  ObjectProperty.homMk (BigFppfOver.sigmaIncl B S hS (fun i ↦ (inclusion B S hS).obj (A i)) i)

/-- The underlying scheme of a coproduct of the big affine fppf category over `S`. -/
theorem toScheme_obj_sigmaObj :
    (toScheme B S hS).obj (sigmaObj B S hS A) = ∐ fun i ↦ (toScheme B S hS).obj (A i) := rfl

/-- The underlying morphism of the `i`-th inclusion into the coproduct, in the big fppf
category over `S`. -/
theorem inclusion_map_sigmaIncl (i : I) :
    (inclusion B S hS).map (sigmaIncl B S hS A i) =
      BigFppfOver.sigmaIncl B S hS (fun i ↦ (inclusion B S hS).obj (A i)) i := rfl

/-- The underlying scheme morphism of the `i`-th inclusion into the coproduct. -/
theorem toScheme_map_sigmaIncl (i : I) :
    (toScheme B S hS).map (sigmaIncl B S hS A i) =
      Limits.Sigma.ι (fun i ↦ (toScheme B S hS).obj (A i)) i :=
  BigFppfOver.toScheme_map_sigmaIncl B S hS _ i

/-- The coproduct of a finite family of objects of the big affine fppf category over `S` is a
coproduct there: the category is a full subcategory of the big fppf category over `S`, in
which the coproduct is computed, and the coproduct of affines is affine. -/
noncomputable def isColimitSigmaCofan :
    IsColimit (Cofan.mk (sigmaObj B S hS A) (sigmaIncl B S hS A)) :=
  let hc := BigFppfOver.isColimit_sigmaCofan B S hS fun i ↦ (inclusion B S hS).obj (A i)
  Cofan.IsColimit.mk _
    (fun t ↦ ObjectProperty.homMk (Cofan.IsColimit.desc hc fun i ↦ (t.inj i).hom))
    (fun t i ↦ ObjectProperty.hom_ext _ (Cofan.IsColimit.fac hc (fun i ↦ (t.inj i).hom) i))
    (fun t _m hm ↦ ObjectProperty.hom_ext _ (Cofan.IsColimit.hom_ext hc _ _ fun i ↦
      (congrArg (fun q : A i ⟶ t.pt ↦ q.hom) (hm i)).trans
        (Cofan.IsColimit.fac hc (fun i ↦ (t.inj i).hom) i).symm))

/-- The underlying schemes of a finite coproduct of the big affine fppf category over `S` form
a coproduct of schemes. -/
noncomputable def isColimitToSchemeSigmaCofan :
    IsColimit (Cofan.mk ((toScheme B S hS).obj (sigmaObj B S hS A))
      fun i ↦ (toScheme B S hS).map (sigmaIncl B S hS A i)) := by
  simp only [toScheme_map_sigmaIncl B S hS A]
  exact coproductIsCoproduct fun i ↦ (toScheme B S hS).obj (A i)

/-- The big affine fppf category over `S` has finite coproducts. -/
noncomputable instance hasColimitsOfShape_discrete :
    HasColimitsOfShape (Discrete I) (BigAffineFppf B S hS) where
  has_colimit F := HasColimit.mk
    ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj
        (Cofan.mk (sigmaObj B S hS fun i ↦ F.obj ⟨i⟩) (sigmaIncl B S hS fun i ↦ F.obj ⟨i⟩)),
      (IsColimit.precomposeHomEquiv _ _).symm (isColimitSigmaCofan B S hS _)⟩

/-- **The representable sheaf of a finite coproduct of affines is the coproduct of the
representable sheaves**, the affine case of
`AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaSigmaCofan`. -/
noncomputable def isColimitUliftYonedaSigmaCofan :
    IsColimit (Cofan.mk
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
        ((inclusion B S hS).obj (sigmaObj B S hS A)))
      fun i ↦ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map
        ((inclusion B S hS).map (sigmaIncl B S hS A i))) :=
  BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS fun i ↦ (inclusion B S hS).obj (A i)

/-- The universe-raising Yoneda embedding of the big fppf category over `S`, restricted to
affines, preserves finite coproducts. -/
noncomputable instance preservesColimitsOfShape_uliftYoneda :
    PreservesColimitsOfShape (Discrete I)
      (inclusion B S hS ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) where
  preservesColimit {F} := by
    have : PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk))
        (inclusion B S hS ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitSigmaCofan B S hS (F.obj ∘ Discrete.mk))
        ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
          (isColimitUliftYonedaSigmaCofan B S hS (F.obj ∘ Discrete.mk)))
    exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := F)).symm

/-- The sheafified Yoneda embedding of the big fppf category over `S`, restricted to affines,
preserves finite coproducts. -/
noncomputable instance preservesColimitsOfShape_sheafifiedYoneda :
    PreservesColimitsOfShape (Discrete I)
      (inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
  preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (inclusion B S hS)
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm)

end BigAffineFppf

/-! ### The set-theoretic condition for a finite coproduct -/

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIS for a finite coproduct.** A coproduct of finitely many fppf sheaves each of
which satisfies the set-theoretic condition satisfies it again: the coproduct of the chosen
objects of the site surjects onto the coproduct, and the coproduct of the objects covering the
kernel pairs of the summands covers the kernel pair of that surjection, the kernel pair of a
morphism of finite coproducts being the coproduct of the kernel pairs of its summands. -/
theorem satisfiesSetTheoreticCondition_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS)
    (hZ : ∀ i, SatisfiesSetTheoreticCondition B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    SatisfiesSetTheoreticCondition B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  show SatisfiesSetTheoreticCondition B S hS (∐ Z)
  let : Small.{u} I := Countable.toSmall.{u} I
  let J := BigFppfOver.topology B S hS
  have key : ∀ i, ∃ (Ui Ri : BigFppfOver B S hS) (a : J.uliftYoneda.{u + 1}.obj Ui ⟶ Z i),
      Epi a ∧ ∃ (Pi : FppfSheaf B S hS) (p₁ p₂ : Pi ⟶ J.uliftYoneda.{u + 1}.obj Ui),
        IsPullback p₁ p₂ a a ∧
          ∃ b : J.uliftYoneda.{u + 1}.obj Ri ⟶ Pi, Epi b := by
    intro i
    obtain ⟨Ui, Ri, hU, hR, ⟨eU⟩, ⟨eR⟩, f, hf, g, hg⟩ := hZ i
    let eSU : J.uliftYoneda.{u + 1}.obj Ui ≅ hU :=
      (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
        (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app Ui ≪≫ eU.symm)
    let eSR : J.uliftYoneda.{u + 1}.obj Ri ≅ hR :=
      (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
        (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app Ri ≪≫ eR.symm)
    have := hf
    have := hg
    exact ⟨Ui, Ri, eSU.hom ≫ f, epi_comp _ _, pullback f f,
      pullback.fst f f ≫ eSU.inv, pullback.snd f f ≫ eSU.inv,
      Limits.IsPullback.kernelPair_compIso (IsPullback.of_hasPullback f f) eSU,
      eSR.hom ≫ g, epi_comp _ _⟩
  choose Ui Ri a ha Pi p₁ p₂ hP b hb using key
  have : ∀ i, Epi (a i) := ha
  have : ∀ i, Epi (b i) := hb
  -- the two objects of the site, and the coproducts of their representable sheaves
  let Utot := BigFppfOver.sigmaObj B S hS Ui
  let Rtot := BigFppfOver.sigmaObj B S hS Ri
  let lam : ∀ i, J.uliftYoneda.{u + 1}.obj (Ui i) ⟶ J.uliftYoneda.{u + 1}.obj Utot :=
    fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS Ui i)
  have hULift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj Utot) lam) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS Ui
  have hRLift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj Rtot)
      fun i ↦ J.uliftYoneda.{u + 1}.map (BigFppfOver.sigmaIncl B S hS Ri i)) :=
    BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS Ri
  -- the surjection onto the coproduct
  have hZcop : IsColimit (Cofan.mk (∐ Z) (Limits.Sigma.ι Z)) := coproductIsCoproduct Z
  let f : J.uliftYoneda.{u + 1}.obj Utot ⟶ ∐ Z :=
    Cofan.IsColimit.desc hULift fun i ↦ a i ≫ Limits.Sigma.ι Z i
  have hfac : ∀ i, lam i ≫ f = a i ≫ Limits.Sigma.ι Z i :=
    Cofan.IsColimit.fac hULift _
  have hfEpi : Epi f := epi_of_isColimit_cofan hZcop hfac ha
  -- the kernel pair of that surjection is the coproduct of the kernel pairs of the summands
  let ρ : ∀ i, Pi i ⟶ pullback f f := fun i ↦ pullback.lift (p₁ i ≫ lam i) (p₂ i ≫ lam i) (by
    rw [Category.assoc, Category.assoc, hfac i, ← Category.assoc, ← Category.assoc, (hP i).w])
  obtain ⟨hcof⟩ := nonempty_isColimit_cofan_kernelPair hULift hZcop hfac hP
    (IsPullback.of_hasPullback f f) ρ (fun i ↦ pullback.lift_fst _ _ _)
    (fun i ↦ pullback.lift_snd _ _ _)
  let g : J.uliftYoneda.{u + 1}.obj Rtot ⟶ pullback f f :=
    Cofan.IsColimit.desc hRLift fun i ↦ b i ≫ ρ i
  have hgEpi : Epi g := epi_of_isColimit_cofan hcof (Cofan.IsColimit.fac hRLift _) hb
  exact ⟨Utot, Rtot, J.uliftYoneda.{u + 1}.obj Utot, J.uliftYoneda.{u + 1}.obj Rtot,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app Utot⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app Rtot⟩, f, hfEpi, g, hgEpi⟩

/-! ### A finite coproduct of affine formal algebraic spaces -/

/-- **A coproduct of finitely many affine formal algebraic spaces over `S` is an affine formal
algebraic space over `S`.**

The presentations `Z i ≅ colim_{Idx i} D i` are combined over the product
`K = ∏ᵢ Idx i` of their index preorders, which is again nonempty and directed: the stage of
the combined system at `k ∈ K` is the coproduct `∐ᵢ (D i) (k i)`, an affine scheme over `S`
because a finite coproduct of affine schemes is affine, and its transition morphisms are
thickenings because a finite coproduct of thickenings is a thickening. That the colimit of the
combined system is `∐ Z` is the interchange of the coproduct with the two colimits, together
with finality of the projections `K ⥤ Idx i` and the fact that the sheafified Yoneda embedding
carries a finite coproduct of the site to the coproduct of the representable sheaves. The
set-theoretic condition is `satisfiesSetTheoreticCondition_sigma`. -/
theorem isAffineFormalAlgebraicSpace_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS)
    (hZ : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsAffineFormalAlgebraicSpace B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  show IsAffineFormalAlgebraicSpace B S hS (∐ Z)
  let : Small.{u} I := Countable.toSmall.{u} I
  let J := BigFppfOver.topology B S hS
  let G := BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  refine ⟨satisfiesSetTheoreticCondition_sigma B S hS Z fun i ↦ (hZ i).1, ?_⟩
  choose Idx pre hne hdir D hthick hiso using fun i ↦ (hZ i).2
  let : ∀ i, Preorder (Idx i) := pre
  let : ∀ i, Nonempty (Idx i) := hne
  let : ∀ i, IsDirectedOrder (Idx i) := hdir
  -- the combined directed system over the product of the index preorders
  let T : Discrete I ⥤ (PiOrder Idx ⥤ BigAffineFppf B S hS) :=
    Discrete.functor fun i ↦ PiOrder.proj i ⋙ D i
  let E : PiOrder Idx ⥤ BigAffineFppf B S hS := T.flip ⋙ colim
  -- its stages, computed as explicit coproducts of the stages of the given systems
  let Stage : PiOrder Idx → I → BigAffineFppf B S hS := fun k i ↦ (T.flip.obj k).obj ⟨i⟩
  have cof : ∀ k : PiOrder Idx, IsColimit ((Cocone.precompose
      (Discrete.natIsoFunctor (F := T.flip.obj k)).hom).obj
      (Cofan.mk (BigAffineFppf.sigmaObj B S hS (Stage k))
        (BigAffineFppf.sigmaIncl B S hS (Stage k)))) := fun k ↦
    (IsColimit.precomposeHomEquiv _ _).symm (BigAffineFppf.isColimitSigmaCofan B S hS (Stage k))
  let eK : ∀ k : PiOrder Idx, colimit (T.flip.obj k) ≅
      BigAffineFppf.sigmaObj B S hS (Stage k) := fun k ↦
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (T.flip.obj k)) (cof k)
  have heK : ∀ (k : PiOrder Idx) (i : I), colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom =
      BigAffineFppf.sigmaIncl B S hS (Stage k) i := by
    intro k i
    have h0 : colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom =
        (Discrete.natIsoFunctor (F := T.flip.obj k)).hom.app ⟨i⟩ ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k) i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (T.flip.obj k)) (cof k) ⟨i⟩
    rw [h0]
    simp
  -- the transition morphisms are thickenings
  have hthickE : ∀ ⦃k k' : PiOrder Idx⦄ (h : k ⟶ k'),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map h)) := by
    intro k k' h
    set ψ : BigAffineFppf.sigmaObj B S hS (Stage k) ⟶
        BigAffineFppf.sigmaObj B S hS (Stage k') := (eK k).inv ≫ E.map h ≫ (eK k').hom with hψdef
    have hψ : ∀ i, colimit.ι (T.flip.obj k) ⟨i⟩ ≫ E.map h ≫ (eK k').hom =
        (D i).map ((PiOrder.proj i).map h) ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k') i := by
      intro i
      rw [show E.map h = colimMap (T.flip.map h) from rfl, ← Category.assoc, ι_colimMap,
        Category.assoc, heK k' i]
      rfl
    have hψ' : ∀ i, BigAffineFppf.sigmaIncl B S hS (Stage k) i ≫ ψ =
        (D i).map ((PiOrder.proj i).map h) ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k') i := by
      intro i
      calc BigAffineFppf.sigmaIncl B S hS (Stage k) i ≫ ψ
          = (colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom) ≫ ψ := by rw [heK k i]
        _ = colimit.ι (T.flip.obj k) ⟨i⟩ ≫ E.map h ≫ (eK k').hom := by
            rw [hψdef, Category.assoc, Iso.hom_inv_id_assoc]
        _ = _ := hψ i
    have hψthick : Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map ψ) :=
      Stacks.Thickenings.isThickening_of_cofan
        (BigAffineFppf.isColimitToSchemeSigmaCofan B S hS (Stage k))
        (BigAffineFppf.isColimitToSchemeSigmaCofan B S hS (Stage k'))
        (fun i ↦ (BigAffineFppf.toScheme B S hS).map ((D i).map ((PiOrder.proj i).map h)))
        (fun i ↦ by rw [← Functor.map_comp, hψ' i, Functor.map_comp])
        (fun i ↦ hthick i _)
    have hE : E.map h = (eK k).hom ≫ ψ ≫ (eK k').inv := by
      rw [hψdef]; simp
    rw [hE, Functor.map_comp, Functor.map_comp]
    refine ⟨?_, ?_⟩
    · have := hψthick.1
      infer_instance
    · have : AlgebraicGeometry.Surjective ((BigAffineFppf.toScheme B S hS).map ψ) :=
        ⟨hψthick.2⟩
      exact (((BigAffineFppf.toScheme B S hS).map (eK k).hom) ≫
        ((BigAffineFppf.toScheme B S hS).map ψ) ≫
        ((BigAffineFppf.toScheme B S hS).map (eK k').inv)).surjective
  -- the colimit of the combined system is the coproduct
  let W : Discrete I ⥤ (PiOrder Idx ⥤ FppfSheaf B S hS) :=
    T ⋙ (Functor.whiskeringRight (PiOrder Idx) (BigAffineFppf B S hS)
      (FppfSheaf B S hS)).obj G
  have e1 : E ⋙ G ≅ W.flip ⋙ colim :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft T.flip (preservesColimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm
  have hfin : ∀ i : I, (PiOrder.proj (Idx := Idx) i).Final := fun i ↦ PiOrder.final_proj i
  have e3 : W ⋙ colim ≅ Discrete.functor Z :=
    Discrete.natIso fun i ↦
      Functor.Final.colimitIso (PiOrder.proj i.as) (D i.as ⋙ G) ≪≫ (hiso i.as).some.symm
  refine ⟨PiOrder Idx, inferInstance, inferInstance, inferInstance, E, hthickE,
    ⟨(HasColimit.isoOfNatIso e1 ≪≫ colimitFlipCompColimIsoColimitCompColim W ≪≫
      HasColimit.isoOfNatIso e3).symm⟩⟩

end FormalSpace

end AlgebraicGeometry

end
