module

public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Representable categories fibred in groupoids satisfy (RS*)

Let `X₀` be a scheme over `S` in the big fppf site and regard it as a category fibred in
groupoids through its slice `Sch/X₀`, as in `AlgebraicGeometry.Stack.schemeFibredCategory`.
This file proves that it satisfies the Rim–Schlessinger condition (RS*) of Stacks 07Y8: for a
fibre-product square of affine schemes over `S` whose ring square is cartesian with one
surjection, restriction from the fibre over the fourth corner to the two-fibre product of the
other three fibres is an equivalence.

The fibres of a slice are thin: an object over `T` is a morphism `T ⟶ X₀` and a morphism of
the fibre exists exactly when the two morphisms agree. So the comparison functor is an
equivalence exactly when morphisms `Z ⟶ X₀` out of the fourth corner are the compatible pairs
of morphisms out of the two others, that is when the square is a pushout as seen by `X₀`. For
affine schemes this is Stacks 0ET0
(`Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective`): the spectrum of a fibre
product of rings over a surjection is a pushout in the category of all schemes.

## Main results

* `Deformation.Artin.fiberSquareComparison_overForget_isEquivalence`: for the slice over any
  object of any category, the comparison functor of a square is an equivalence as soon as
  morphisms to that object out of the fourth corner are the compatible pairs.
* `Deformation.Artin.existsUnique_desc_of_isPushout_toScheme`: a square of the big fppf site
  whose square of schemes is a pushout has the universal property of a pushout in the site. The
  pushout of schemes comes from `Deformation.Artin.isPushout_of_isPullback_appTop`
  (`StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts`).
* `Deformation.Artin.satisfiesRSStar_overForget`: the slice of the big fppf site over a
  scheme satisfies (RS*).

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w

/-! ### The fibres of a slice are thin -/

section SliceFiber

variable {𝒮 : Type u} [Category.{v} 𝒮] (X₀ : 𝒮)

/-- The morphism to `X₀` underlying an object of the fibre over `T` of the slice over `X₀`. -/
public def sliceFiberStructureHom {T : 𝒮} (a : (Over.forget X₀).Fiber T) : T ⟶ X₀ :=
  eqToHom a.2.symm ≫ a.1.hom

variable {X₀}

/-- An arrow of the slice lying over `k` relates the underlying morphisms of its ends by `k`. -/
public theorem sliceFiberStructureHom_of_isHomLift {T T' : 𝒮} {k : T ⟶ T'}
    {a : (Over.forget X₀).Fiber T} {b : (Over.forget X₀).Fiber T'} (φ : a.1 ⟶ b.1)
    (hφ : (Over.forget X₀).IsHomLift k φ) :
    sliceFiberStructureHom X₀ a = k ≫ sliceFiberStructureHom X₀ b := by
  have hfac : φ.left = eqToHom a.2 ≫ k ≫ eqToHom b.2.symm := IsHomLift.fac' (Over.forget X₀) k φ
  have hw : φ.left ≫ b.1.hom = a.1.hom := Over.w φ
  rw [hfac] at hw
  unfold sliceFiberStructureHom
  rw [← hw]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Two morphisms of a fibre of a slice are equal. -/
public theorem sliceFiber_hom_ext {T : 𝒮} {a b : (Over.forget X₀).Fiber T} (φ ψ : a ⟶ b) :
    φ = ψ := by
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have := φ.2
  have := ψ.2
  exact (IsHomLift.fac' (Over.forget X₀) (𝟙 T) φ.1).trans
    (IsHomLift.fac' (Over.forget X₀) (𝟙 T) ψ.1).symm

/-- Morphisms between two objects of a fibre of a slice form a subsingleton. -/
public instance sliceFiber_hom_subsingleton {T : 𝒮} (a b : (Over.forget X₀).Fiber T) :
    Subsingleton (a ⟶ b) :=
  ⟨sliceFiber_hom_ext⟩

/-- A morphism of a fibre of a slice from an equality of the underlying morphisms. -/
public def sliceFiberHomOfEq {T : 𝒮} {a b : (Over.forget X₀).Fiber T}
    (h : sliceFiberStructureHom X₀ a = sliceFiberStructureHom X₀ b) : a ⟶ b :=
  ⟨Over.homMk (eqToHom (a.2.trans b.2.symm)) (by
      simpa [sliceFiberStructureHom] using (congrArg (eqToHom a.2 ≫ ·) h).symm),
    IsHomLift.of_fac' (p := Over.forget X₀) _ _ a.2 b.2 (by simp)⟩

/-- An isomorphism of a fibre of a slice from an equality of the underlying morphisms. -/
public def sliceFiberIsoOfEq {T : 𝒮} {a b : (Over.forget X₀).Fiber T}
    (h : sliceFiberStructureHom X₀ a = sliceFiberStructureHom X₀ b) : a ≅ b where
  hom := sliceFiberHomOfEq h
  inv := sliceFiberHomOfEq h.symm
  hom_inv_id := sliceFiber_hom_ext _ _
  inv_hom_id := sliceFiber_hom_ext _ _

/-- The underlying morphisms of two objects related by a morphism of the fibre agree. -/
public theorem sliceFiberStructureHom_eq_of_hom {T : 𝒮} {a b : (Over.forget X₀).Fiber T}
    (φ : a ⟶ b) :
    sliceFiberStructureHom X₀ a = sliceFiberStructureHom X₀ b :=
  (sliceFiberStructureHom_of_isHomLift φ.1 φ.2).trans (Category.id_comp _)

/-- The chosen pullback along `k` of an object of a fibre of a slice has underlying morphism
the composite with `k`. -/
public theorem sliceFiberStructureHom_pullback (c : (Over.forget X₀).ChoiceOfPullbacks) {T T' : 𝒮}
    (k : T ⟶ T') (a : (Over.forget X₀).Fiber T') :
    sliceFiberStructureHom X₀ ((c.pullbackFunctor k).obj a) = k ≫ sliceFiberStructureHom X₀ a :=
  sliceFiberStructureHom_of_isHomLift (c.map k a) (c.isStronglyCartesian k a).toIsHomLift

/-- The underlying morphisms of two pulled-back objects related by a fibre morphism agree. -/
private theorem comp_sliceFiberStructureHom_eq_of_hom (c : (Over.forget X₀).ChoiceOfPullbacks)
    {T T' T'' : 𝒮} {k : T ⟶ T'} {k' : T ⟶ T''} {a : (Over.forget X₀).Fiber T'}
    {b : (Over.forget X₀).Fiber T''}
    (φ : (c.pullbackFunctor k).obj a ⟶ (c.pullbackFunctor k').obj b) :
    k ≫ sliceFiberStructureHom X₀ a = k' ≫ sliceFiberStructureHom X₀ b := by
  rw [← sliceFiberStructureHom_pullback c k a, ← sliceFiberStructureHom_pullback c k' b]
  exact sliceFiberStructureHom_eq_of_hom φ

end SliceFiber

/-! ### The comparison functor of a slice -/

section Comparison

variable {𝒮 : Type u} [Category.{v} 𝒮] {X₀ : 𝒮} (c : (Over.forget X₀).ChoiceOfPullbacks)
  {U V W Z : 𝒮} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)

/-- **The comparison functor of a slice is an equivalence over a square that is a pushout as
seen by `X₀`.** If morphisms `Z ⟶ X₀` correspond exactly to the pairs of morphisms
`V ⟶ X₀`, `W ⟶ X₀` agreeing on `U`, then restriction from the fibre over `Z` of the slice over
`X₀` to the two-fibre product of the fibres over `V`, `U`, `W` is an equivalence. -/
public theorem fiberSquareComparison_overForget_isEquivalence
    (hpo : ∀ (a : V ⟶ X₀) (b : W ⟶ X₀), f ≫ a = g ≫ b →
      ∃! z : Z ⟶ X₀, i ≫ z = a ∧ j ≫ z = b) :
    (fiberSquareComparison (Over.forget X₀) c f g i j h).IsEquivalence := by
  refine ⟨⟨fun {a b} _ _ _ => sliceFiber_hom_ext _ _⟩, ⟨fun {a b} m => ?_⟩, ⟨fun P => ?_⟩⟩
  · -- fullness: the two components of `m` force the underlying morphisms to agree
    obtain ⟨z, -, hz⟩ := hpo (i ≫ sliceFiberStructureHom X₀ b) (j ≫ sliceFiberStructureHom X₀ b)
      (by rw [reassoc_of% h])
    have hab : sliceFiberStructureHom X₀ a = sliceFiberStructureHom X₀ b :=
      (hz _ ⟨comp_sliceFiberStructureHom_eq_of_hom c (k := i) (k' := i) m.fst,
        comp_sliceFiberStructureHom_eq_of_hom c (k := j) (k' := j) m.snd⟩).trans
        (hz _ ⟨rfl, rfl⟩).symm
    exact ⟨sliceFiberHomOfEq hab,
      CategoricalPullback.hom_ext (sliceFiber_hom_ext _ _) (sliceFiber_hom_ext _ _)⟩
  · -- essential surjectivity: glue the two underlying morphisms along the pushout
    obtain ⟨z, ⟨hzV, hzW⟩, -⟩ :=
      hpo _ _ (comp_sliceFiberStructureHom_eq_of_hom c (k := f) (k' := g) P.iso.hom)
    let a : (Over.forget X₀).Fiber Z := ⟨Over.mk z, rfl⟩
    have ha : sliceFiberStructureHom X₀ a = z := Category.id_comp z
    refine ⟨a, ⟨CategoricalPullback.mkIso
      (sliceFiberIsoOfEq ((sliceFiberStructureHom_pullback c i a).trans (by rw [ha, hzV])))
      (sliceFiberIsoOfEq ((sliceFiberStructureHom_pullback c j a).trans (by rw [ha, hzW])))
      (sliceFiber_hom_ext _ _)⟩⟩

end Comparison

/-! ### Squares of affine schemes -/

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square of the big fppf site over `S` whose underlying square of schemes is a pushout has
the universal property of a pushout towards every object of the site. -/
public theorem existsUnique_desc_of_isPushout_toScheme {U V W Z X₀ : BigFppfOver B S hS}
    {f : U ⟶ V} {g : U ⟶ W} {i : V ⟶ Z} {j : W ⟶ Z}
    (H : IsPushout ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map j))
    (a : V ⟶ X₀) (b : W ⟶ X₀) (hab : f ≫ a = g ≫ b) :
    ∃! z : Z ⟶ X₀, i ≫ z = a ∧ j ≫ z = b := by
  set T := BigFppfOver.toScheme B S hS
  have hab' : T.map f ≫ T.map a = T.map g ≫ T.map b := by
    rw [← T.map_comp, ← T.map_comp, hab]
  let z₀ := H.desc (T.map a) (T.map b) hab'
  let zS : Z.left ⟶ X₀.left := B.inclusion.preimage z₀
  have hzS : B.inclusion.map zS = z₀ := B.inclusion.map_preimage z₀
  have hw : zS ≫ X₀.hom = Z.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hzS]
    apply H.hom_ext
    · rw [H.inl_desc_assoc]
      change B.inclusion.map a.left ≫ B.inclusion.map X₀.hom =
        B.inclusion.map i.left ≫ B.inclusion.map Z.hom
      rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w a, Over.w i]
    · rw [H.inr_desc_assoc]
      change B.inclusion.map b.left ≫ B.inclusion.map X₀.hom =
        B.inclusion.map j.left ≫ B.inclusion.map Z.hom
      rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w b, Over.w j]
  refine ⟨Over.homMk zS hw, ⟨?_, ?_⟩, fun z ⟨hzi, hzj⟩ => ?_⟩
  · refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change B.inclusion.map (i.left ≫ zS) = B.inclusion.map a.left
    rw [Functor.map_comp, hzS]
    exact H.inl_desc _ _ _
  · refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change B.inclusion.map (j.left ≫ zS) = B.inclusion.map b.left
    rw [Functor.map_comp, hzS]
    exact H.inr_desc _ _ _
  · refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change T.map z = B.inclusion.map zS
    rw [hzS]
    apply H.hom_ext
    · rw [H.inl_desc, ← T.map_comp, hzi]
    · rw [H.inr_desc, ← T.map_comp, hzj]

/-- **The slice of the big fppf site over a scheme satisfies (RS\*).** A scheme `X₀` over `S`,
regarded as a category fibred in groupoids through its slice, satisfies the Rim–Schlessinger
condition of Stacks 07Y8: morphisms to `X₀` out of the spectrum of a fibre product of rings
over a surjection are the compatible pairs of morphisms out of the two factors, by Stacks 0ET0. -/
public theorem satisfiesRSStar_overForget (X₀ : BigFppfOver B S hS) :
    SatisfiesRSStar B S hS (Over.forget X₀) (Functor.IsFiberedInGroupoids.over_forget X₀) := by
  intro U V W Z f g i j h hpb hg _
  apply fiberSquareComparison_overForget_isEquivalence
  apply existsUnique_desc_of_isPushout_toScheme
  have := U.property
  have := V.property
  have := W.property
  have := Z.property
  exact isPushout_of_isPullback_appTop (U := (BigAffineFppf.toScheme B S hS).obj U)
    (V := (BigAffineFppf.toScheme B S hS).obj V) (W := (BigAffineFppf.toScheme B S hS).obj W)
    (Z := (BigAffineFppf.toScheme B S hS).obj Z) _ _ _ _ hpb hg

end Affine

end Deformation.Artin

end
