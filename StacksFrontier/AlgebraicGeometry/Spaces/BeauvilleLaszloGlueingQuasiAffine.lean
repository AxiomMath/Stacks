module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Quasi-affine triples under the Beauville--Laszlo gluing functor (Stacks 0F9U)

Let `(R → R', f)` be a glueing pair, so that `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and
`U' = Spec R'_f`. Stacks 0F9U asserts that every cartesian gluing triple `(V, V', Y')` whose
three components are quasi-affine is isomorphic to the image, under the gluing functor of
Stacks 0F9N, of a *separated* algebraic space `Y` over `X`.

The source proves this by producing from the triple an affine presentation: an affine `T → X`
with a flat morphism of finite presentation `T → Y` onto the sought space, whose kernel pair
`W = T ×_Y T` is a closed subspace of `T ×_X T`. Separatedness of `Y` is then read off from
that presentation, because the relative diagonal of `Y` base-changes along the fpqc covering
`T ×_X T → Y ×_X Y` to the closed immersion `W → T ×_X T`, and being a closed immersion is
fpqc local on the base by Stacks 0420.

That last step is what this module proves, in the generality in which it is used: the
identification of the kernel pair of a morphism with the base change of the diagonal, and the
descent of separatedness along an fpqc covering of the product. Producing the presentation
itself is the part of the source's argument that rests on results this library does not yet
carry — the essential-surjectivity half of the affine equivalence of Stacks 0F9Q, of which only
the restriction clause is available, and the quotient theorem Stacks 04S6 — and it is not done
here. Stacks 0F9U itself is
`BeauvilleLaszlo.Space.exists_isSeparatedOver_iso_of_isQuasiAffineComponents` in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingQuasiAffineUnconditional.lean`.

## Main definitions

* `AlgebraicGeometry.Space.IsQuasiAffineSpace`: an algebraic space over `S` is quasi-affine
  when it is represented by an object of the site with quasi-affine underlying scheme.
* `AlgebraicGeometry.AlgebraicSpaces.productDiagonal`,
  `AlgebraicGeometry.AlgebraicSpaces.productMapHom` and
  `AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct`: the diagonal `Y → Y ⨯ Y`, the
  product `a ⨯ a` of a morphism with itself, and the morphism `(p₀, p₁) : E ×_Y E → E ⨯ E`,
  all as morphisms of algebraic spaces over `S`.
* `BeauvilleLaszlo.Space.quasiAffineComponents`: cartesian gluing triples whose three
  components are quasi-affine.

## Main results

* `AlgebraicGeometry.AlgebraicSpaces.isPullback_kernelPairToProduct`: the kernel pair of
  `a : E ⟶ Y` is the base change of the diagonal of `Y` along `a ⨯ a`.
* `AlgebraicGeometry.Space.isSeparatedOver_of_fpqcCovering_productDiagonal` and
  `AlgebraicGeometry.Space.isSeparatedOver_of_kernelPair_isClosedImmersion`: separatedness over
  the base descends along an fpqc covering of the product, hence holds for a space whose kernel
  pair along an fpqc-covering presentation is a closed immersion.

## Implementation notes

Products of algebraic spaces over `S` are taken in the explicit form
`AlgebraicGeometry.AlgebraicSpaces.product`, whose underlying presheaf is the presheaf product
on the nose. This matters: separatedness over `S` is by
`AlgebraicGeometry.Space.IsSeparatedOver` a property of the *presheaf* diagonal `diag F`, while
the locality statement of Stacks 0420 is about the category of algebraic spaces, and with the
explicit product the two diagonals are the same morphism rather than merely isomorphic ones.

## References

* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-affine algebraic spaces -/

/-- A presheaf on the big fppf category over `S` is a *quasi-affine* algebraic space when it is
isomorphic to the presheaf represented by an object of the site whose underlying scheme is
quasi-affine. -/
abbrev IsQuasiAffineSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ T : BigFppfOver B S hS,
    Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (F ≅ yoneda.obj T)

/-- The presheaf represented by an object of the big fppf site of `S` with quasi-affine
underlying scheme is a quasi-affine algebraic space. -/
theorem isQuasiAffineSpace_yoneda (T : BigFppfOver B S hS)
    (hT : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiAffineSpace B S hS (yoneda.obj T) :=
  ⟨T, hT, ⟨Iso.refl _⟩⟩

variable {B S hS}

/-- A presheaf isomorphic to a quasi-affine algebraic space is a quasi-affine algebraic
space. -/
theorem IsQuasiAffineSpace.of_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsQuasiAffineSpace B S hS F) (e : F ≅ F') : IsQuasiAffineSpace B S hS F' := by
  obtain ⟨T, hT, ⟨i⟩⟩ := h
  exact ⟨T, hT, ⟨e.symm.trans i⟩⟩

/-- An affine algebraic space is quasi-affine. -/
theorem IsAffineSpace.isQuasiAffineSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsAffineSpace B S hS F) : IsQuasiAffineSpace B S hS F := by
  obtain ⟨T, hT, hi⟩ := h
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  exact ⟨T, inferInstance, hi⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.AlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The diagonal and the kernel pair as morphisms of algebraic spaces -/

/-- The first projection of the product of two algebraic spaces over `S`. -/
noncomputable abbrev productProjFst (F G : AlgebraicSpaces B S hS) :
    product B S hS F G ⟶ F :=
  ObjectProperty.homMk prod.fst

/-- The second projection of the product of two algebraic spaces over `S`. -/
noncomputable abbrev productProjSnd (F G : AlgebraicSpaces B S hS) :
    product B S hS F G ⟶ G :=
  ObjectProperty.homMk prod.snd

/-- The diagonal of an algebraic space over `S`, as a morphism of algebraic spaces into the
product. Its underlying morphism of presheaves is the presheaf diagonal, so it is the morphism
tested by `AlgebraicGeometry.Space.IsSeparatedOver`. -/
noncomputable abbrev productDiagonal (F : AlgebraicSpaces B S hS) :
    F ⟶ product B S hS F F :=
  ObjectProperty.homMk (diag F.obj)

/-- The product of a morphism of algebraic spaces over `S` with itself. -/
noncomputable abbrev productMapHom {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    product B S hS F F ⟶ product B S hS G G :=
  ObjectProperty.homMk (prod.map a.hom a.hom)

/-- The morphism from the kernel pair `F ×_G F` of `a : F ⟶ G` to the product `F ⨯ F`, given by
the two projections. -/
noncomputable abbrev kernelPairToProduct {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    Limits.pullback a a ⟶ product B S hS F F :=
  ObjectProperty.homMk (prod.lift (pullback.fst a a).hom (pullback.snd a a).hom)

/-- Two morphisms into a product of algebraic spaces agree once both projections do. -/
theorem product_hom_ext {F G Z : AlgebraicSpaces B S hS} {f g : Z ⟶ product B S hS F G}
    (h₁ : f ≫ productProjFst B S hS F G = g ≫ productProjFst B S hS F G)
    (h₂ : f ≫ productProjSnd B S hS F G = g ≫ productProjSnd B S hS F G) : f = g :=
  ObjectProperty.hom_ext _ (prod.hom_ext
    (congrArg (fun k : Z ⟶ F => k.hom) h₁) (congrArg (fun k : Z ⟶ G => k.hom) h₂))

/-- The first projection of the diagonal is the identity. -/
@[simp]
theorem productDiagonal_comp_fst (F : AlgebraicSpaces B S hS) :
    productDiagonal B S hS F ≫ productProjFst B S hS F F = 𝟙 F :=
  ObjectProperty.hom_ext _ (show diag F.obj ≫ prod.fst = 𝟙 F.obj by simp)

/-- The second projection of the diagonal is the identity. -/
@[simp]
theorem productDiagonal_comp_snd (F : AlgebraicSpaces B S hS) :
    productDiagonal B S hS F ≫ productProjSnd B S hS F F = 𝟙 F :=
  ObjectProperty.hom_ext _ (show diag F.obj ≫ prod.snd = 𝟙 F.obj by simp)

/-- The first projection intertwines `a ⨯ a` with `a`. -/
@[simp]
theorem productMapHom_comp_fst {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    productMapHom B S hS a ≫ productProjFst B S hS G G =
      productProjFst B S hS F F ≫ a :=
  ObjectProperty.hom_ext _
    (show prod.map a.hom a.hom ≫ prod.fst = prod.fst ≫ a.hom by simp)

/-- The second projection intertwines `a ⨯ a` with `a`. -/
@[simp]
theorem productMapHom_comp_snd {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    productMapHom B S hS a ≫ productProjSnd B S hS G G =
      productProjSnd B S hS F F ≫ a :=
  ObjectProperty.hom_ext _
    (show prod.map a.hom a.hom ≫ prod.snd = prod.snd ≫ a.hom by simp)

/-- The first component of the kernel-pair morphism is the first projection of the kernel
pair. -/
@[simp]
theorem kernelPairToProduct_comp_fst {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    kernelPairToProduct B S hS a ≫ productProjFst B S hS F F = pullback.fst a a :=
  ObjectProperty.hom_ext _
    (show prod.lift (pullback.fst a a).hom (pullback.snd a a).hom ≫ prod.fst =
      (pullback.fst a a).hom by simp)

/-- The second component of the kernel-pair morphism is the second projection of the kernel
pair. -/
@[simp]
theorem kernelPairToProduct_comp_snd {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    kernelPairToProduct B S hS a ≫ productProjSnd B S hS F F = pullback.snd a a :=
  ObjectProperty.hom_ext _
    (show prod.lift (pullback.fst a a).hom (pullback.snd a a).hom ≫ prod.snd =
      (pullback.snd a a).hom by simp)

/-- A cone over the diagonal of `G` and `a ⨯ a` recovers its first leg from a projection of its
second leg. -/
private theorem cone_snd_comp_proj_comp {F G : AlgebraicSpaces B S hS} (a : F ⟶ G)
    (s : PullbackCone (productDiagonal B S hS G) (productMapHom B S hS a))
    (pF : product B S hS F F ⟶ F) (pG : product B S hS G G ⟶ G)
    (hd : productDiagonal B S hS G ≫ pG = 𝟙 G) (hm : productMapHom B S hS a ≫ pG = pF ≫ a) :
    (s.snd ≫ pF) ≫ a = s.fst := by
  have h := congrArg (fun k => k ≫ pG) s.condition
  simp only [Category.assoc, hd, Category.comp_id, hm] at h
  simp [h]

/-- **The kernel pair is the base change of the diagonal.** For a morphism `a : F ⟶ G` of
algebraic spaces over `S`, the square formed by `F ×_G F → F ⨯ F`, the diagonal of `G` and the
product `a ⨯ a` is cartesian. This is the identification the source of Stacks 0F9U makes when
it reads separatedness of a quotient off its presentation. -/
theorem isPullback_kernelPairToProduct {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    IsPullback (pullback.fst a a ≫ a) (kernelPairToProduct B S hS a)
      (productDiagonal B S hS G) (productMapHom B S hS a) := by
  have hsq : (pullback.fst a a ≫ a) ≫ productDiagonal B S hS G =
      kernelPairToProduct B S hS a ≫ productMapHom B S hS a := by
    refine product_hom_ext B S hS ?_ ?_
    · simp only [Category.assoc, productDiagonal_comp_fst, Category.comp_id,
        productMapHom_comp_fst]
      rw [← Category.assoc, kernelPairToProduct_comp_fst]
    · simp only [Category.assoc, productDiagonal_comp_snd, Category.comp_id,
        productMapHom_comp_snd]
      rw [← Category.assoc, kernelPairToProduct_comp_snd, pullback.condition]
  have hfst := fun s => cone_snd_comp_proj_comp B S hS a s _ _
    (productDiagonal_comp_fst B S hS G) (productMapHom_comp_fst B S hS a)
  have hsnd := fun s => cone_snd_comp_proj_comp B S hS a s _ _
    (productDiagonal_comp_snd B S hS G) (productMapHom_comp_snd B S hS a)
  refine IsPullback.of_isLimit' ⟨hsq⟩ (PullbackCone.IsLimit.mk hsq
    (fun s => pullback.lift (s.snd ≫ productProjFst B S hS F F)
      (s.snd ≫ productProjSnd B S hS F F) ((hfst s).trans (hsnd s).symm))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · rw [← Category.assoc, pullback.lift_fst]
    exact hfst s
  · refine product_hom_ext B S hS ?_ ?_
    · rw [Category.assoc, kernelPairToProduct_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, kernelPairToProduct_comp_snd, pullback.lift_snd]
  · refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← kernelPairToProduct_comp_fst B S hS a, ← Category.assoc, hm₂]
    · rw [pullback.lift_snd, ← kernelPairToProduct_comp_snd B S hS a, ← Category.assoc, hm₂]

end AlgebraicGeometry.AlgebraicSpaces

namespace AlgebraicGeometry.Space

/-! ### Separatedness from a presentation -/

/-- **Separatedness over the base descends along an fpqc covering of the product.** If the
diagonal of an algebraic space `F` over `S` pulls back to a closed immersion along every member
of an fpqc covering of `F ⨯ F`, then `F` is separated over `S`. This is Stacks 0420 applied to
the diagonal. -/
theorem isSeparatedOver_of_fpqcCovering_productDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : AlgebraicSpaces B S hS) {I : Type v} (Z : I → AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ AlgebraicSpaces.product B S hS F F)
    (hcov : Topology.IsCovering .fpqc B S hS (fun i => (Z i).obj) (fun i => (g i).hom))
    (hci : ∀ i, IsClosedImmersion B S hS
      (pullback.snd (AlgebraicSpaces.productDiagonal B S hS F) (g i)).hom) :
    IsSeparatedOver B S hS F.obj := by
  have hlocal : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    isClosedImmersion_isLocalAtTarget_fpqc B S hS
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom)
    (K := Topology.precoverage.{u, v} .fpqc B S hS)
    (f := AlgebraicSpaces.productDiagonal B S hS F)
    (R := Presieve.ofArrows Z g) ⟨I, Z, g, rfl, hcov⟩ ?_
  rintro U k _ ⟨i⟩
  exact hci i

/-- **Separatedness from a presentation.** Let `a : E ⟶ F` be a morphism of algebraic spaces
over `S` whose square `a ⨯ a` is an fpqc covering of `F ⨯ F`. If the kernel pair `E ×_F E` is a
closed subspace of `E ⨯ E`, then `F` is separated over `S`. -/
theorem isSeparatedOver_of_kernelPair_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F : AlgebraicSpaces B S hS} (a : E ⟶ F)
    (hcov : Topology.IsCovering .fpqc B S hS
      (fun _ : PUnit.{v + 1} => (AlgebraicSpaces.product B S hS E E).obj)
      (fun _ => (AlgebraicSpaces.productMapHom B S hS a).hom))
    (hrel : IsClosedImmersion B S hS
      (AlgebraicSpaces.kernelPairToProduct B S hS a).hom) :
    IsSeparatedOver B S hS F.obj := by
  have hrespects : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom) :=
    (isClosedImmersion_isLocalAtTarget_fpqc.{u, v} B S hS).toRespects
  have hpb := AlgebraicSpaces.isPullback_kernelPairToProduct B S hS a
  refine isSeparatedOver_of_fpqcCovering_productDiagonal.{u, v} B S hS F
    (fun _ : PUnit.{v + 1} => AlgebraicSpaces.product B S hS E E)
    (fun _ => AlgebraicSpaces.productMapHom B S hS a) hcov fun _ => ?_
  rw [← hpb.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom)
    hpb.isoPullback.inv (AlgebraicSpaces.kernelPairToProduct B S hS a)).mpr hrel

end AlgebraicGeometry.Space

namespace BeauvilleLaszlo.Space

/-! ### Triples with quasi-affine components -/

/-- The property of a cartesian gluing triple that its three components are quasi-affine. -/
abbrev quasiAffineComponents (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :
    ObjectProperty (GlueingData B U' U X' hU' hU hX' gU gX') :=
  fun Z =>
    AlgebraicGeometry.Space.IsQuasiAffineSpace B U hU
        ((overU B U' U X' hU' hU hX' gU gX').obj Z).1 ∧
      AlgebraicGeometry.Space.IsQuasiAffineSpace B U' hU'
          ((overU' B U' U X' hU' hU hX' gU gX').obj Z).1 ∧
        AlgebraicGeometry.Space.IsQuasiAffineSpace B X' hX'
          ((overX' B U' U X' hU' hU hX' gU gX').obj Z).1

/-- A cartesian gluing triple with affine components has quasi-affine components. -/
theorem quasiAffineComponents_of_affineComponents (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    (hZ : affineComponents B U' U X' hU' hU hX' gU gX' Z) :
    quasiAffineComponents B U' U X' hU' hU hX' gU gX' Z :=
  ⟨hZ.1.isQuasiAffineSpace, hZ.2.1.isQuasiAffineSpace, hZ.2.2.isQuasiAffineSpace⟩

end BeauvilleLaszlo.Space

end
