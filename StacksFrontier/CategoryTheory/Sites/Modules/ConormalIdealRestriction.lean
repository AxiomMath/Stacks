module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence

/-!
# Maps out of a conormal sheaf, and the difference cocycle of two of them

Let `φ : 𝒜 ⟶ ℬ` be a locally surjective morphism of sheaves of commutative rings on a site,
write `ℐ = Ker φ`, and let `𝒢` be a sheaf of `ℬ`-modules. A *restriction datum* for `φ` is a
natural family of maps `ℐ(U) ⟶ 𝒢(U)` which is linear over `𝒜` acting through `φ`. Such a
family automatically annihilates `ℐ²`, because a local section of `ℐ` acts as zero on `𝒢`, and
therefore descends to a morphism of sheaves of `ℬ`-modules

`ℐ/ℐ² ⟶ 𝒢`.

Restriction data can be subtracted, and the construction is additive, so the difference of two
restriction data gives a *cocycle*: the map attached to `(ρ₁, ρ₂)` plus the map attached to
`(ρ₂, ρ₃)` is the map attached to `(ρ₁, ρ₃)`.

This is Step 1 of the proof of [Stacks 08U8] in the form in which it is used by
[Stacks 08UC]: the two restriction data are the restrictions `a|_{ℐ'}` and `b|_{ℐ'}` to the
ideal of a polynomial presentation of the two algebra maps attached to two solutions of the
deformation problem, and the cocycle identity is the telescoping of their differences. See the
implementation notes for what this does *not* do.

## Main definitions

* `Stacks.Sites.Conormal.presentationScalar`: the structural ring map `𝒜(U) ⟶ ℬ(U)` of the
  presentation, read as a map into the scalars of a sheaf of `ℬ`-modules.
* `Stacks.Sites.Conormal.IdealRestriction`: a restriction datum — an `𝒜`-linear natural family
  of maps `ℐ(U) ⟶ 𝒢(U)`.
* `Stacks.Sites.Conormal.IdealRestriction.sub`: the difference of two restriction data.
* `Stacks.Sites.Conormal.IdealRestriction.cotangentApp`: the induced map on sections of the
  conormal presheaf `U ↦ ℐ(U)/ℐ(U)²`.
* `Stacks.Sites.Conormal.conormalDesc`: the morphism `ℐ/ℐ² ⟶ 𝒢` of sheaves of `ℬ`-modules
  determined by a restriction datum.
* `Stacks.Sites.Conormal.conormalDifference`: the morphism `ℐ/ℐ² ⟶ 𝒢` attached to a pair of
  restriction data, namely the one determined by their difference.

## Main results

* `Stacks.Sites.Conormal.IdealRestriction.app_mul`: a restriction datum annihilates `ℐ²`. This
  is the one computation the descent to `ℐ/ℐ²` rests on, and it is free: `ρ (g · h)` is
  `φ(g) · ρ h` and `φ(g) = 0`.
* `Stacks.Sites.Conormal.conormalDesc_conormalClass`: the descended morphism sends the conormal
  class of a local section `g` of `ℐ` to `ρ g`. This formula pins it down, by
  `Stacks.Sites.Conormal.sheafify_hom_ext`.
* `Stacks.Sites.Conormal.conormalDesc_sub`: the descent is additive, in the form needed for the
  cocycle identity.
* `Stacks.Sites.Conormal.conormalDifference_add_conormalDifference`: **the cocycle identity**
  `ξ(ρ₁, ρ₂) + ξ(ρ₂, ρ₃) = ξ(ρ₁, ρ₃)`, and
  `Stacks.Sites.Conormal.conormalDifference_self`, its vanishing on the diagonal.

## Implementation notes

The `𝒜`-linearity of a restriction datum is stated with the scalar written through `φ`, which
is what makes the annihilation of `ℐ²` automatic rather than an extra hypothesis: it is the
same cancellation that `Stacks.Sites.SqZeroPushout.PushoutData` bundles as `smul_eq_zero`, here
available for free because `𝒢` is given as a sheaf of `ℬ`-modules from the start, whereas there
`𝒢` is a module over the source of the presentation.

The descent to `ℐ/ℐ²` is objectwise — `Ideal.Cotangent.lift` applied to each `ℐ(U)` — followed
by `Stacks.Sites.Conormal.sheafifyLiftDesc`, which is the universal property of the
sheafification that `Stacks.Sites.Conormal.conormalSheaf` is. Scalar restriction along `φ` is
performed with `ModuleCat.restrictScalars` rather than `Module.compHom`, because the `Module`
instance produced by the latter is only semireducible and `Ideal.Cotangent.lift`'s `map_smul'`
field is then not accepted.

**What this file does not do.** It does not construct the difference cocycle of two solutions
of the deformation problem of [Stacks 08U7] on the conormal sheaf of the *base* presentation
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`, which is the conormal term of `NL(α)` and hence the group that
[Stacks 08UC] needs. Two solutions give restriction data for the presentation
`f⁻¹𝒪_{S'}[ℰ] ⟶ 𝒪_X` with the *larger* coefficient sheaf, so this file's output is a map out
of `ℐ'/(ℐ')²`, and the source then *descends* it along the surjection `ℐ' ⟶ ℐ` whose kernel is
`𝒥·f⁻¹𝒪_{S'}[ℰ]`. That surjection, and the computation of its kernel, is not in the library:
`Stacks.Sites.Conormal.presentationConormalMap` goes from `ℐ'/(ℐ')²` to `ℐ/ℐ²`, so it cannot be
composed with a map out of `ℐ'/(ℐ')²`, and nothing says it is an epimorphism or identifies its
kernel. Descending along it is therefore the remaining step, and this file is its input.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public section

open CategoryTheory

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
  (G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The structural map `𝒜(U) ⟶ ℬ(U)` of a presentation, read as a ring homomorphism into the
scalars of a sheaf of `ℬ`-modules. -/
noncomputable abbrev presentationScalar (X : Cᵒᵖ) :
    ↥(A.obj.obj X) →+* ↥((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X) :=
  (φ.hom.app X).hom

/-- The sections of a sheaf of `ℬ`-modules, read as a module over `𝒜(U)` acting through the
presentation. This is the module in which `Ideal.Cotangent.lift` is applied. -/
noncomputable abbrev restrictPresentation (X : Cᵒᵖ) :
    ModuleCat.{max w u v z} ↥(A.obj.obj X) :=
  (ModuleCat.restrictScalars (presentationScalar φ X)).obj (G.val.obj X)

/-- A *restriction datum* for the presentation `φ : 𝒜 ⟶ ℬ` with values in a sheaf of
`ℬ`-modules `𝒢`: a natural family of maps `ℐ(U) ⟶ 𝒢(U)` out of the kernel ideal `ℐ = Ker φ`,
linear over `𝒜` acting on `𝒢` through `φ`.

This is the datum `a|_{ℐ'}` of Step 1 of the proof of [Stacks 08U8]: the restriction to the
ideal of a presentation of an algebra map into a square-zero extension of `ℬ` by `𝒢`. -/
structure IdealRestriction where
  /-- The map `ℐ(U) ⟶ 𝒢(U)` on sections over an object of the site. -/
  app (X : Cᵒᵖ) : ↥(kernelIdeal φ.hom X) →+ ↥(G.val.obj X)
  /-- The maps on sections are linear over `𝒜` acting through the presentation. -/
  app_smul (X : Cᵒᵖ) (r : ↥(A.obj.obj X)) (g : ↥(kernelIdeal φ.hom X)) :
    app X (r • g) = presentationScalar φ X r • app X g
  /-- The maps on sections commute with the restriction maps. -/
  app_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : ↥(kernelIdeal φ.hom X)) :
    app Y ⟨(A.obj.map f).hom (g : ↥(A.obj.obj X)), map_kernel φ.hom f g.2⟩ =
      G.val.map f (app X g)

namespace IdealRestriction

variable {φ G}

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A restriction datum annihilates `ℐ²`.** The product `g · h` of two local sections of `ℐ`
is `g` acting on `h`, so `ρ (g · h) = φ(g) · ρ h`, and `φ(g) = 0`. -/
theorem app_mul (ρ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g h : ↥(kernelIdeal φ.hom X)) : ρ.app X (g * h) = 0 := by
  have hz : presentationScalar φ X (g : ↥(A.obj.obj X)) = 0 := g.2
  have hgh : (g * h : ↥(kernelIdeal φ.hom X)) = (g : ↥(A.obj.obj X)) • h := rfl
  rw [hgh, ρ.app_smul, hz, zero_smul]

/-- The difference of two restriction data. -/
protected noncomputable def sub (ρ σ : IdealRestriction φ G) : IdealRestriction φ G where
  app X := ρ.app X - σ.app X
  app_smul X r g := by
    change ρ.app X (r • g) - σ.app X (r • g) =
      presentationScalar φ X r • (ρ.app X g - σ.app X g)
    rw [ρ.app_smul, σ.app_smul, smul_sub]
  app_map {X Y} f g := by
    change ρ.app Y _ - σ.app Y _ = G.val.map f (ρ.app X g - σ.app X g)
    rw [ρ.app_map, σ.app_map]
    exact (map_sub (G.val.map f).hom _ _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- On sections, the difference of two restriction data is the difference of their maps. -/
@[simp] theorem sub_app (ρ σ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal φ.hom X)) :
    (IdealRestriction.sub ρ σ).app X g = ρ.app X g - σ.app X g :=
  rfl

/-- The objectwise descent of a restriction datum through `ℐ(U) ⟶ ℐ(U)/ℐ(U)²`, as a linear map
over `𝒜(U)` into the sections of `𝒢` with scalars restricted along the presentation. The
descent is available because `ρ` annihilates `ℐ²`. -/
noncomputable def cotangentHom (ρ : IdealRestriction φ G) (X : Cᵒᵖ) :
    (kernelIdeal φ.hom X).Cotangent →ₗ[↥(A.obj.obj X)] ↥(restrictPresentation φ G X) :=
  Ideal.Cotangent.lift
    { toFun := ρ.app X
      map_add' := (ρ.app X).map_add
      map_smul' := fun r g ↦ ρ.app_smul X r g }
    (fun g h ↦ ρ.app_mul X g h)

/-- The map on sections of the conormal presheaf induced by a restriction datum. -/
noncomputable def cotangentApp (ρ : IdealRestriction φ G) (X : Cᵒᵖ) :
    (kernelIdeal φ.hom X).Cotangent → ↥(G.val.obj X) :=
  fun x ↦ ρ.cotangentHom X x

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The map on conormal sections sends the class of `g` in `ℐ(U)/ℐ(U)²` to `ρ g`. -/
@[simp] theorem cotangentApp_toCotangent (ρ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal φ.hom X)) :
    ρ.cotangentApp X ((kernelIdeal φ.hom X).toCotangent g) = ρ.app X g :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The map on conormal sections induced by a restriction datum is additive. -/
theorem cotangentApp_add (ρ : IdealRestriction φ G) (X : Cᵒᵖ)
    (x y : (kernelIdeal φ.hom X).Cotangent) :
    ρ.cotangentApp X (x + y) = ρ.cotangentApp X x + ρ.cotangentApp X y :=
  map_add (ρ.cotangentHom X) x y

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The map on conormal sections induced by a restriction datum is linear over `𝒜(U)` acting
through the presentation. -/
theorem cotangentApp_smul (ρ : IdealRestriction φ G) (X : Cᵒᵖ) (r : ↥(A.obj.obj X))
    (x : (kernelIdeal φ.hom X).Cotangent) :
    ρ.cotangentApp X (r • x) = presentationScalar φ X r • ρ.cotangentApp X x :=
  (ρ.cotangentHom X).map_smul r x

end IdealRestriction

section Desc

variable [Presheaf.IsLocallySurjective J φ.hom]

/-- The morphism of sheaves of `ℬ`-modules `ℐ/ℐ² ⟶ 𝒢` determined by a restriction datum.

This is the map `ξ` of Step 1 of the proof of [Stacks 08U8], for the presentation whose ideal
the datum is defined on. -/
noncomputable def conormalDesc (ρ : IdealRestriction φ G) :
    conormalSheaf.{v, u, w, z} J A B φ ⟶ G := by
  refine sheafifyLiftDesc.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) G
    (fun X x ↦ ρ.cotangentApp X x) (fun X x y ↦ ρ.cotangentApp_add X x y) ?_ ?_
  · intro X r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ρ.cotangentApp_smul X r x
  · intro X Y f x
    obtain ⟨g, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective x
    exact ρ.app_map f g

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended morphism `ℐ/ℐ² ⟶ 𝒢` sends the image in the sheafification of the class of `g`
to `ρ g`. -/
@[simp] theorem conormalDesc_toAssociatedModule (ρ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal φ.hom X)) :
    ((conormalDesc φ G ρ).val.app X)
        (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
          ((kernelIdeal φ.hom X).toCotangent g)) =
      ρ.app X g :=
  sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) G _ _ _ _ X _

variable (R : Sheaf J CommRingCat.{w}) (a : R ⟶ A)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The descended morphism sends the conormal class of `g` to `ρ g`.** This formula determines
it, by `Stacks.Sites.Conormal.sheafify_hom_ext`. -/
theorem conormalDesc_conormalClass (ρ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal φ.hom X)) :
    ((conormalDesc φ G ρ).val.app X)
        (conormalClass.{v, u, w, z} J R A B a φ X g) = ρ.app X g :=
  conormalDesc_toAssociatedModule φ G ρ X g

end Desc

section Cocycle

variable [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms out of the conormal sheaf agreeing on all conormal classes are equal. -/
theorem conormal_hom_ext {g₁ g₂ : conormalSheaf.{v, u, w, z} J A B φ ⟶ G}
    (h : ∀ (X : Cᵒᵖ) (x : ↥(kernelIdeal φ.hom X)),
      g₁.val.app X (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
          ((kernelIdeal φ.hom X).toCotangent x)) =
        g₂.val.app X (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
          ((kernelIdeal φ.hom X).toCotangent x))) :
    g₁ = g₂ := by
  refine sheafify_hom_ext.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) G (fun X x ↦ ?_)
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective x
  exact h X x

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descent is additive in the restriction datum, in the form the cocycle identity needs:
the descents of `ρ₁ - ρ₂` and `ρ₂ - ρ₃` add up to the descent of `ρ₁ - ρ₃`. -/
theorem conormalDesc_sub (ρ₁ ρ₂ ρ₃ : IdealRestriction φ G) :
    conormalDesc φ G (IdealRestriction.sub ρ₁ ρ₂) +
        conormalDesc φ G (IdealRestriction.sub ρ₂ ρ₃) =
      conormalDesc φ G (IdealRestriction.sub ρ₁ ρ₃) := by
  refine conormal_hom_ext φ G (fun X x ↦ ?_)
  change ((conormalDesc φ G (IdealRestriction.sub ρ₁ ρ₂)).val.app X) _ +
      ((conormalDesc φ G (IdealRestriction.sub ρ₂ ρ₃)).val.app X) _ = _
  rw [conormalDesc_toAssociatedModule, conormalDesc_toAssociatedModule,
    conormalDesc_toAssociatedModule, IdealRestriction.sub_app, IdealRestriction.sub_app,
    IdealRestriction.sub_app, sub_add_sub_cancel]

/-- The morphism `ℐ/ℐ² ⟶ 𝒢` attached to an *ordered pair* of restriction data: the descent of
their difference.

This is the obstruction cocycle of Step 1 of the proof of [Stacks 08U8], as a function of the
two restriction data rather than of a pair of solutions; see the implementation notes of this
file for the step that separates the two. -/
noncomputable def conormalDifference (ρ σ : IdealRestriction φ G) :
    conormalSheaf.{v, u, w, z} J A B φ ⟶ G :=
  conormalDesc φ G (IdealRestriction.sub ρ σ)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The map attached to `(ρ, σ)` sends the image in the sheafification of the class of `g` to
`ρ g - σ g`. -/
@[simp] theorem conormalDifference_toAssociatedModule (ρ σ : IdealRestriction φ G) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal φ.hom X)) :
    ((conormalDifference φ G ρ σ).val.app X)
        (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
          ((kernelIdeal φ.hom X).toCotangent g)) =
      ρ.app X g - σ.app X g :=
  conormalDesc_toAssociatedModule φ G (IdealRestriction.sub ρ σ) X g

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The cocycle identity.** The map attached to `(ρ₁, ρ₂)` plus the map attached to `(ρ₂, ρ₃)`
is the map attached to `(ρ₁, ρ₃)`. This is the additivity of a telescoping difference, and it is
the identity `hxi` that the torsor formalism of [Stacks 08UC] consumes. -/
theorem conormalDifference_add_conormalDifference (ρ₁ ρ₂ ρ₃ : IdealRestriction φ G) :
    conormalDifference φ G ρ₁ ρ₂ + conormalDifference φ G ρ₂ ρ₃ =
      conormalDifference φ G ρ₁ ρ₃ :=
  conormalDesc_sub φ G ρ₁ ρ₂ ρ₃

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- There is no obstruction between a restriction datum and itself. -/
theorem conormalDifference_self (ρ : IdealRestriction φ G) :
    conormalDifference φ G ρ ρ = 0 := by
  have h := conormalDifference_add_conormalDifference φ G ρ ρ ρ
  simpa using h

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Reversing the pair negates the map. -/
theorem conormalDifference_symm (ρ σ : IdealRestriction φ G) :
    conormalDifference φ G σ ρ = -conormalDifference φ G ρ σ := by
  have h := conormalDifference_add_conormalDifference φ G ρ σ ρ
  rw [conormalDifference_self] at h
  exact (neg_eq_of_add_eq_zero_right h).symm

end Cocycle

end Stacks.Sites.Conormal

end
