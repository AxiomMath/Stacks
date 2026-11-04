module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineCokernelDescent

/-!
# Surjectivity on sections of a presenting morphism on the small étale site

Let `b : P ⟶ M` be an epimorphism of sheaves of modules on a slice of the small étale site of an
algebraic space, let `a : Q ⟶ P` present it, so that `b` is a cokernel of `a` and `P` and `Q` are
coproducts of copies of the structure sheaf, and let `W` be an object of the slice whose
underlying scheme is affine.  This file proves that `b` is surjective on the sections over `W`,
with no hypothesis beyond the presentation.

The reduction of surjectivity to a sheaf condition is site-independent.  Surjectivity of `b` over
an object is surjectivity there of the morphism `θ` out of the cokernel of `a.val` computed in
presheaves of modules, and
`CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows` reduces that to four
statements about one covering family of the object: local injectivity of `θ`,
the sheaf condition for the presheaf cokernel for the family, separatedness of the presheaf
cokernel over the pairwise fibre products of the family, and a lift of the section over each
member.  Local injectivity is free for a presentation, the lift comes from local surjectivity of
an epimorphism, and the fibre products of objects with affine underlying scheme over such an
object again have affine underlying scheme, so what is left is the sheaf condition and the
separatedness at the objects with affine underlying scheme.

The separatedness is
`AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`, and the sheaf
condition is what this file computes.  For a finite family whose image in schemes is a flat
covering family the sections of the presheaf cokernel over a member are the base change of its
sections over the object covered along the induced map of rings of global functions, the ring of
global functions on a fibre product of two members is the tensor product of their rings
(`AlgebraicGeometry.Space.SmallEtale.algebra_isPushout_gamma_of_isPullback`), and the product of
the rings of the members is faithfully flat over the ring of the object covered; so
`PresheafOfModules.exists_pairBaseChange` and `PresheafOfModules.exists_amitsurDiff₀_data`
assemble the degree-zero data of the Amitsur complex of that product and
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` concludes.  An arbitrary finite covering
family of objects with affine underlying scheme is reduced to that case by
`AlgebraicGeometry.Space.SmallEtale.isSheafFor_cokernel_affine_of_isSheafFor_fppf`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.hasPullbacks_over`: **a slice of the small étale site has
  fibre products**, named rather than left to instance search.
* `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_over` and
  `AlgebraicGeometry.Space.SmallEtale.isAffine_pullback`: **the fibre product of two objects of a
  slice with affine underlying scheme over one with affine underlying scheme again has affine
  underlying scheme**, for the objects the sheaves of modules on the slice are indexed by, with
  the square given and with it chosen.
* `AlgebraicGeometry.Space.SmallEtale.isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf` and
  `AlgebraicGeometry.Space.SmallEtale.isSheafFor_ofArrows_cokernel_of_fppf`: **the sheaf condition
  for a finite family of objects with affine underlying scheme whose image in schemes is a flat
  covering family, for the presheaf cokernel of a presentation over an object with affine
  underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.isSheafFor_cokernel_of_isAffineOver`: **the same for an
  arbitrary finite covering family of objects with affine underlying scheme**, flatness no longer
  being assumed.
* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_lift_cokernelDesc`: **a section
  of the target of an epimorphism of sheaves of modules lifts to the presheaf cokernel over the
  members of a finite covering family of objects with affine underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine`,
  `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine_of_injective_map` and
  `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine_of_isColimit`: **the
  presenting morphism is surjective on the sections over an object with affine underlying scheme**,
  given the sheaf condition for the presheaf cokernel and, in the three successively weaker forms,
  separatedness, injectivity of restriction, or nothing further.
* `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver`: **the
  presenting morphism of a presentation of a sheaf of modules on a slice of the small étale site is
  surjective on the sections over an object with affine underlying scheme**, with no hypothesis
  beyond the presentation.

## Implementation notes

The module structures over the rings of global functions are `let`-bound local definitions rather
than instance arguments of an auxiliary statement: an instance argument for the action of the ring
of global functions on a module of sections is opaque, and the sections of a presheaf of modules
carry their own action over the ring of sections of the coefficient sheaf of rings, which the two
being definitionally the same ring does not reconcile once one of them is a variable.  For the same
reason the underlying schemes are written out rather than abbreviated.  No instance is created.

They are bound *uniformly in the object*, as functions `∀ Z, Module Γ(Z) (N(Z))` rather than one
per object of the covering, so that the base-change comparison of the sections of the presheaf
cokernel can be taken once for an arbitrary morphism of the slice between two objects with affine
underlying scheme and then used both at the members of the covering family and at the fibre
products of pairs of members.  The algebra structure over the ring of the object covered cannot be
bound that way, since it depends on the morphism and not only on its source; it appears as a
`letI` in the statement of that comparison, which is how the instance the two call sites already
hold is the one the comparison is stated against.

The fibre products of pairs of members are obtained from an existential rather than written as the
chosen `CategoryTheory.Limits.pullback`, which makes them opaque local objects.  Written directly,
the `let`-bound module structures at them are reported as failing to compile for depending on the
`noncomputable` `CategoryTheory.Limits.pullback`, although they occur inside the proof of a
proposition; obtaining the square from an existential keeps that construction out of the types the
module structures are stated at.

The objects of the site are spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules are
indexed by.  `CategoryTheory.Limits.HasPullbacks` on a slice is not found by instance search at
that spelling, because instance search does not unfold the projection, so it is supplied by
`AlgebraicGeometry.Space.SmallEtale.hasPullbacks_over`, which is exactly that defect repaired once.

The two sheafification conditions on the slice are instance arguments rather than being produced
here.  They hold on every slice by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`, but only in the
universe of the schemes, whereas the statements below leave the universe of the module sections
free.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe z r m t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-! ### Fibre products in a slice, for the objects the sheaves are indexed by -/

section Pullbacks

/-- **A slice of the small étale site has fibre products.**  This is
`AlgebraicGeometry.Space.SmallEtale.instHasPullbacks` together with the fibre products of a slice
of a category which has them, named rather than left to instance search.

Naming it is what makes it usable below.  The sheaves of modules on a slice are indexed by the
objects of the site spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, and at that spelling instance search does not find
this instance, because it type-checks at a transparency which does not unfold the projection.
Applying this statement does, since an application is checked at full transparency. -/
theorem hasPullbacks_over (V : SmallEtale B S hS F) : HasPullbacks (Over V) := inferInstance

variable (hF : IsAlgebraicSpace B S hS F)

/-- **The fibre product of two objects of a slice of the small étale site whose underlying schemes
are affine, over an object whose underlying scheme is affine, again has affine underlying
scheme.**  This is `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback` for the objects the
sheaves of modules on the slice are indexed by, taking the fibre product square as a hypothesis
rather than choosing it. -/
theorem isAffine_of_isPullback_over {V : (smallEtaleRingedSite B S hS F hF).C}
    {W Y Z Pb : Over V} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Y.left)))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Pb.left)) :=
  isAffine_of_isPullback B S hS F h hW hY hZ

/-- **The fibre product of two objects of a slice of the small étale site whose underlying schemes
are affine, over an object whose underlying scheme is affine, again has affine underlying
scheme.**  This is `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback` at the chosen fibre
product, for the objects the sheaves of modules on the slice are indexed by.

It is the separatedness side of the surjectivity criterion: nothing is ever asked of the presheaf
cokernel at a non-affine object, because the pairwise fibre products of a covering family of
objects with affine underlying scheme are again of that kind. -/
theorem isAffine_pullback {V : (smallEtaleRingedSite B S hS F hF).C} [HasPullbacks (Over V)]
    {W Y Z : Over V} (f : Y ⟶ W) (g : Z ⟶ W)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Y.left)))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (CategoryTheory.Limits.pullback f g).left)) :=
  isAffine_of_isPullback B S hS F (IsPullback.of_hasPullback f g) hW hY hZ

end Pullbacks

/-! ### The sheaf condition for the presheaf cokernel of a presentation -/

section SheafCondition

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  {K I : Type z}
  {Q P : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  {N : PresheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V).obj}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P) (π : P.val ⟶ N) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)

include κ ι hQ hP hπ in
/-- **The sheaf condition for a finite family of objects of a slice of the small étale site with
affine underlying scheme whose image in schemes is a flat covering family, for the presheaf
cokernel of a presentation over an object with affine underlying scheme.**

Every ring in sight is a ring of global functions on an underlying scheme, every module of
sections is a module over the ring of sections of the coefficient sheaf of rings at the same
object, and the two are the same ring definitionally
(`AlgebraicGeometry.Space.SmallEtale.ringSheaf_over_obj_obj`).  Over a member of the family and
over a fibre product of two members the ring of global functions on the object covered acts
through the induced map of global functions, so the restriction maps are linear.

The three inputs are: the base-change comparison of the sections of the presheaf cokernel at each
member and at each fibre product of two members
(`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`, whose bases are
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`, the underlying scheme of a fibre
product being affine by
`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_over`); the identification of the ring
of global functions on a fibre product of two members with the tensor product of their rings
(`AlgebraicGeometry.Space.SmallEtale.algebra_isPushout_gamma_of_isPullback`); and faithful
flatness of the product of the rings of the members over the ring of the object covered
(`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).
`PresheafOfModules.exists_pairBaseChange` and `PresheafOfModules.exists_amitsurDiff₀_data` turn
the first two into the degree-zero data of the Amitsur complex of that product, and
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` concludes.

The base-change comparison is taken once, for an arbitrary morphism of the slice whose two objects
have affine underlying scheme, and then used both at the members and at the fibre products of
pairs of members, which is why only three module structures over the rings of global functions
occur rather than one per object of the covering.

No coproduct is formed inside the site and no cohomology occurs: the single faithfully flat
algebra of the descent is the finite product of the rings of global functions on the members, and
the double self-products of the covering are the fibre products of pairs of members. -/
theorem isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf {ιi : Type*} [Finite ιi] (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
      (Y : ιi → Over V) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
      i).left)))
    (hfppf : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S
      hS F).obj (Y i).left))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
        W.left))) :
    Presieve.IsSheafFor (N.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
      (Presieve.ofArrows Y g) := by
  have hpbs : HasPullbacks (Over V) := hasPullbacks_over B S hS F V
  obtain ⟨Pb, q₁, q₂, hpb⟩ : ∃ (Pb : ιi → ιi → Over V) (q₁ : ∀ i j, Pb i j ⟶ Y i)
      (q₂ : ∀ i j, Pb i j ⟶ Y j), ∀ i j, IsPullback (q₁ i j) (q₂ i j) (g i) (g j) :=
    ⟨fun i j ↦ pullback (g i) (g j), fun i j ↦ pullback.fst (g i) (g j),
      fun i j ↦ pullback.snd (g i) (g j), fun i j ↦ IsPullback.of_hasPullback (g i) (g j)⟩
  have hq : ∀ i j, q₁ i j ≫ g i = q₂ i j ≫ g j := fun i j ↦ (hpb i j).w
  have hPaff : ∀ i j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Pb i j).left)) := fun i j ↦
    isAffine_of_isPullback_over B S hS F hF (hpb i j) hW (hY i) (hY j)
  let algY : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
    W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) :=
    fun i ↦
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (g
        i).left)).appTop.hom
  let algP : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
    W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
    fun i j ↦
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (q₁ i j ≫ g
          i).left)).appTop.hom
  let mod : ∀ (M : PresheafOfModules.{max t u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over
        V).obj) (Z : Over V), Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (M.obj (op Z)) := fun M Z ↦
    inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op Z))
      (M.obj (op Z)))
  have hbc : ∀ (Z : Over V) (h : Z ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left)) →
      let : Algebra Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) :=
        RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map h.left)).appTop.hom
      ∃ e : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
          ⊗[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj W.left), ⊤)] (N.obj (op W))
          ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)] N.obj (op Z),
        ∀ n, e ((1 : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)) ⊗ₜ n) = N.restrictₛₗ h.op n := by
    intro Z h hZ
    let algZ : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) :=
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map h.left)).appTop.hom
    let mW : ∀ (M : Type (max t u)) [AddCommMonoid M] [Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) M],
        Module Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) M := fun M _ _ ↦
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z.left), ⊤))
    have tw : ∀ (M : Type (max t u)) [AddCommMonoid M] [Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) M],
        IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) M :=
      fun M _ _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let rest : ∀ M : PresheafOfModules.{max t u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over
          V).obj, M.obj (op W) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)] M.obj (op Z) := fun M ↦
      { toFun := fun c ↦ M.map h.op c
        map_add' := map_add (M.map h.op).hom
        map_smul' := fun c u ↦ (M.map_smul h.op c u).symm ▸ rfl }
    exact SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel (N := N) κ ι h
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ W hW
        (sectionRingEquivGamma B S hS F hF W) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ Z hZ
        (sectionRingEquivGamma B S hS F hF Z) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP W hW
        (sectionRingEquivGamma B S hS F hF W) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP Z hZ
        (sectionRingEquivGamma B S hS F hF Z) (fun _ _ ↦ rfl))
      (fun k ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ W hW _ _ k)
      (fun k ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ Z hZ _ _ k)
      (fun l ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP W hW _ _ l)
      (fun l ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP Z hZ _ _ l)
      (rest Q.val) (fun _ ↦ rfl)
      (rest P.val) (fun _ ↦ rfl)
      (rest N) (fun _ ↦ rfl) a π hπ
      (a.val.app (op W)).hom (fun _ ↦ rfl)
      (π.app (op W)).hom (fun _ ↦ rfl)
      (a.val.app (op Z)).hom (fun _ ↦ rfl)
      (π.app (op Z)).hom (fun _ ↦ rfl)
  choose ebc hebc using hbc
  have hpairf : ∀ i j, ∃ Φ : (Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
    F).obj (Y i).left), ⊤)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤))
            ⊗[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)]
              (N.obj (op W)) →+ N.obj (op
            (Pb i j)),
      Function.Injective Φ ∧
        (∀ (b : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left),
          ⊤)) (n),
          N.restrictₛₗ (q₁ i j).op (ebc (Y i) (g i) (hY i) (b ⊗ₜ n)) =
            Φ ((b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
              W.left), ⊤)]
                (1 : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
                  j).left), ⊤))) ⊗ₜ n)) ∧
          ∀ (b : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
            j).left), ⊤)) (n),
            N.restrictₛₗ (q₂ i j).op (ebc (Y j) (g j) (hY j) (b ⊗ₜ n)) =
              Φ (((1 : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
                i).left), ⊤))
                  ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
                    W.left), ⊤)] b) ⊗ₜ n) := fun i j ↦ by
    let a₁ : Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
      i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (q₁ i
          j).left)).appTop.hom
    let a₂ : Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
      j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (q₂ i
          j).left)).appTop.hom
    have t₁ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
      W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ by
        change (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (q₁ i j ≫ g
          i).left)).appTop) c = _
        exact (appTopGamma_comp_apply_of_eq B S hS F (q₁ i j).left (g i).left
          (q₁ i j ≫ g i).left rfl c).symm
    have t₂ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
      W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ by
        change (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (q₁ i j ≫ g
          i).left)).appTop) c = _
        exact (appTopGamma_comp_apply_of_eq B S hS F (q₂ i j).left (g j).left
          (q₁ i j ≫ g i).left (congrArg (fun m : Pb i j ⟶ W ↦ m.left) (hq i j).symm) c).symm
    have hpush : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
      F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) :=
      algebra_isPushout_gamma_of_isPullback B S hS F hF (hpb i j) hW (hY i) (hY j)
        rfl rfl rfl rfl
    exact PresheafOfModules.exists_pairBaseChange (g i) (g j) (q₁ i j) (q₂ i j) (hq i j)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤)
      (ebc (Y i) (g i) (hY i)) (hebc (Y i) (g i) (hY i)) (ebc (Y j) (g j) (hY j))
      (hebc (Y j) (g j) (hY j)) (ebc (Pb i j) (q₁ i j ≫ g i) (hPaff i j))
      (hebc (Pb i j) (q₁ i j ≫ g i) (hPaff i j))
      (fun b u ↦ N.map_smul (q₁ i j).op b u) (fun b u ↦ N.map_smul (q₂ i j).op b u)
  choose Φ hΦinj hnat₁ hnat₂ using hpairf
  obtain ⟨eW, eV, hbijW, honeW, hinjV, hd₀⟩ :=
    PresheafOfModules.exists_amitsurDiff₀_data (N := N) g q₁ q₂
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (fun i ↦ Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left),
        ⊤))
      (fun i ↦ (ebc (Y i) (g i) (hY i)).toAddEquiv)
      (fun i n ↦ hebc (Y i) (g i) (hY i) n) Φ hΦinj hnat₁ hnat₂
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
    F).obj W.left), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
        :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS F Y g hW hY hfppf fun _ ↦ rfl
  exact PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀ g
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
    (∀ i, Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
      Pb q₁ q₂ hq
    eW hbijW honeW eV hinjV hd₀

include κ ι hQ hP in
/-- **The same for the cokernel of the presenting morphism computed in presheaves of modules**,
whose projection is a presheaf cokernel by `PresheafOfModules.isPresheafCokernel_cokernelπ`.

The preceding statement is for a morphism with that property rather than for the categorical
cokernel because its proof introduces module structures on the sections, which a statement about a
`noncomputable` construction cannot carry inside a theorem. -/
theorem isSheafFor_ofArrows_cokernel_of_fppf {ιi : Type*} [Finite ιi] (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
      (Y : ιi → Over V) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
      i).left)))
    (hfppf : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S
      hS F).obj (Y i).left))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
        W.left))) :
    Presieve.IsSheafFor
      ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
      (Presieve.ofArrows Y g) :=
  isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf B S hS F hF κ ι hQ hP a (cokernel.π a.val)
    (PresheafOfModules.isPresheafCokernel_cokernelπ a.val) W hW Y g hY hfppf

include κ ι hQ hP in
/-- **The sheaf condition for the cokernel of a presenting morphism computed in presheaves of
modules, for every finite covering family of objects with affine underlying scheme of an object
with affine underlying scheme of a slice of the small étale site.**  No flatness of the family is
assumed.

This is the hypothesis `hsheaf` of
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine_of_isColimit`, in the
shape that statement asks for it.  The reduction to the flat case is
`AlgebraicGeometry.Space.SmallEtale.isSheafFor_cokernel_affine_of_isSheafFor_fppf`: a covering
sieve of such an object contains a finite family of objects with affine underlying scheme which is
flat in schemes, and the amalgamation produced over that refinement is identified with the one
asked for by separatedness at the members.  The flat case is
`AlgebraicGeometry.Space.SmallEtale.isSheafFor_ofArrows_cokernel_of_fppf`. -/
theorem isSheafFor_cokernel_of_isAffineOver (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left))) :
    ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
        i).left))) →
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
          (Presieve.ofArrows Y g) :=
  isSheafFor_cokernel_affine_of_isSheafFor_fppf B S hS F hF κ ι hQ hP a W hW
    fun _ Y' g' hY' _ hfp ↦
      isSheafFor_ofArrows_cokernel_of_fppf B S hS F hF κ ι hQ hP a W hW Y' g' hY' hfp


end SheafCondition

/-! ### Surjectivity of a presenting morphism over an object with affine underlying scheme -/

section Presentation

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  {R : Sheaf ((smallEtaleRingedSite B S hS F hF).J.over V) RingCat.{r}}
  [HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{m}]
  [((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective AddCommGrpCat.{m}]
  {Q P N : SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ N) [Epi b]
  (hab' : a.val ≫ b.val = 0)

/-- **A section of the target of an epimorphism of sheaves of modules lifts to the presheaf
cokernel over the members of a finite covering family of objects with affine underlying scheme.**

An epimorphism of sheaves of modules is locally surjective
(`Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi`), so the arrows along which a
given section of the target restricts into the image of `b` form a covering sieve of the object it
lives over; over an object with affine underlying scheme that sieve contains a finite covering
family of objects with affine underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_le_over`).  A lift through `b`
over a member is carried to a lift through the morphism out of the presheaf cokernel by the
projection onto that cokernel.

This is the one hypothesis of
`SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows` which asks nothing of the
presheaf cokernel beyond its construction, and it is discharged here outright. -/
theorem exists_finite_affine_ofArrows_lift_cokernelDesc (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
      (n : N.val.obj (op W)) :
    ∃ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
        i).left))) ∧
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W ∧
          ∀ i, ∃ s : (cokernel a.val).obj (op (Y i)),
            (cokernel.desc a.val b.val hab').app (op (Y i)) s = N.val.map (g i).op n := by
  have hls := Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi
    (J := (smallEtaleRingedSite B S hS F hF).J.over V) (R := R) b
  obtain ⟨k, Y, g, hYaff, hgS, hgcov, -⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF W hW
      (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map b.val) n)
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf R.obj).map b.val) (U := op W) n)
  refine ⟨k, Y, g, hYaff, hgcov, fun i ↦ ?_⟩
  obtain ⟨q, hq⟩ := hgS i
  exact ⟨(cokernel.π a.val).app (op (Y i)) q,
    (SheafOfModules.cokernelDesc_app_π_app a b hab' (op (Y i)) q).trans hq⟩

/-- **A presenting morphism of an epimorphism of sheaves of modules on a slice of the small étale
site is surjective on the sections over an object with affine underlying scheme**, given local
injectivity of the morphism from the cokernel of `a.val` computed in presheaves of modules to `N`,
the sheaf condition for that cokernel for the finite covering families of objects with affine
underlying scheme of the object in question, and its separatedness for the covering sieves of the
objects with affine underlying scheme.

Every object the two remaining hypotheses speak of has affine underlying scheme: the covering
family comes from
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_lift_cokernelDesc`, whose
members do, and the fibre product of two of them over the object they cover does by
`AlgebraicGeometry.Space.SmallEtale.isAffine_pullback`.  Nothing is asked of the presheaf cokernel
at an object whose underlying scheme is not affine, and nothing is asked of it at the object
itself beyond the sheaf condition for that one family. -/
theorem surjective_val_app_of_isSheafFor_affine (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    (hloc : ∀ (Z : Over V) (s t : (cokernel a.val).obj (op Z)),
      (cokernel.desc a.val b.val hab').app (op Z) s
          = (cokernel.desc a.val b.val hab').app (op Z) t →
        ∃ T : Sieve Z, T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z ∧
          ∀ ⦃V : Over V⦄ (f : V ⟶ Z), T f →
            (cokernel a.val).map f.op s = (cokernel a.val).map f.op t)
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
        i).left))) →
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hsep : ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
      F).obj Z.left)) →
      ∀ T : Sieve Z, T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
        Presieve.IsSeparatedFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (T : Presieve Z)) :
    Function.Surjective (b.val.app (op W)) := by
  have : HasPullbacks (Over V) := hasPullbacks_over B S hS F V
  refine SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows a b hab' hloc
    fun n ↦ ?_
  obtain ⟨k, Y, g, hYaff, hgcov, hn⟩ :=
    exists_finite_affine_ofArrows_lift_cokernelDesc B S hS F hF a b hab' W hW n
  exact ⟨Fin k, Y, g, inferInstance, hsheaf k Y g hYaff hgcov, hgcov,
    fun i j T hT ↦ hsep _ (isAffine_pullback B S hS F hF (g i) (g j) hW
      (hYaff i) (hYaff j)) T hT, hn⟩

/-- **The same with separatedness replaced by injectivity of restriction.**  The separatedness
hypothesis of `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine` is
supplied by `AlgebraicGeometry.Space.SmallEtale.isSeparatedFor_affine_of_injective_map`, which
asks instead that restriction to the members of a finite covering family of objects with affine
underlying scheme be injective on the sections of the presheaf cokernel.

This is the shape in which the two remaining hypotheses are statements about the sections of the
presheaf cokernel over two objects with affine underlying scheme and nothing else: `hinj` mentions
no sieve, and `hsheaf` mentions one covering family.  Both are what a base-change comparison for
the presheaf cokernel along a covering morphism supplies, through
`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`. -/
theorem surjective_val_app_of_isSheafFor_affine_of_injective_map (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    (hloc : ∀ (Z : Over V) (s t : (cokernel a.val).obj (op Z)),
      (cokernel.desc a.val b.val hab').app (op Z) s
          = (cokernel.desc a.val b.val hab').app (op Z) t →
        ∃ T : Sieve Z, T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z ∧
          ∀ ⦃V : Over V⦄ (f : V ⟶ Z), T f →
            (cokernel a.val).map f.op s = (cokernel a.val).map f.op t)
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
        i).left))) →
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hinj : ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
      F).obj Z.left)) →
      ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
          i).left))) →
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
          Function.Injective fun s : (cokernel a.val).obj (op Z) =>
            fun i ↦ (cokernel a.val).map (g i).op s) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine B S hS F hF a b hab' W hW hloc hsheaf
    (isSeparatedFor_affine_of_injective_map B S hS F hF
      ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) hinj)

include hab' in
/-- **The presenting morphism of a presentation of a sheaf of modules on a slice of the small
étale site is surjective on the sections over an object with affine underlying scheme**, given the
sheaf condition for the cokernel of `a.val` computed in presheaves of modules for the finite
covering families of objects with affine underlying scheme of that object, and injectivity of
restriction to the members of such a family.

This is
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine_of_injective_map`
with local injectivity of the comparison to `N` discharged by
`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`, which needs of the presentation
only that `b` is a cokernel of `a` in sheaves of modules.  So the two hypotheses which remain are
the whole of what the cokernel step of a global presentation asks for, and both are statements
about the sections of the presheaf cokernel over objects with affine underlying scheme. -/
theorem surjective_val_app_of_isSheafFor_affine_of_isColimit (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
        i).left))) →
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hinj : ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
      F).obj Z.left)) →
      ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y
          i).left))) →
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
          Function.Injective fun s : (cokernel a.val).obj (op Z) =>
            fun i ↦ (cokernel a.val).map (g i).op s) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine_of_injective_map B S hS F hF a b hab' W hW
    (SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq a b hab hN hab')
    hsheaf hinj

end Presentation

/-! ### The presenting morphism of a presentation, with no further hypothesis -/

section Target

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  {K I : Type z}
  {Q P : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P)
  [HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{max t u}]
  [((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
    AddCommGrpCat.{max t u}]
  {M : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  (b : P ⟶ M) [Epi b] (hab' : a.val ≫ b.val = 0)

include κ ι hQ hP hab' in
/-- **The presenting morphism of a presentation of a sheaf of modules on a slice of the small
étale site of an algebraic space is surjective on the sections over an object whose underlying
scheme is affine**, with no hypothesis beyond the presentation itself.

This is `AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isSheafFor_affine_of_isColimit`
with both of its hypotheses discharged: the sheaf condition for the presheaf cokernel by
`AlgebraicGeometry.Space.SmallEtale.isSheafFor_cokernel_of_isAffineOver`, and injectivity of
restriction to the members of a covering family by
`AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`.

It is the small étale counterpart of
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver`, and it is the
surjectivity half of the vanishing statement which Stacks 03DW rests on; no `@[stacks 03DW]` tag
is carried here, because that tag asserts the comparison of the cohomology of a quasi-coherent
module computed in the Zariski, the small étale and the big `τ` topologies, of which this is one
input.

The two coproducts of the presentation carry their tautological generators and the witnesses that
they are coproducts, because the base-change comparison for the presheaf cokernel uses the
generators of the relations as well as the generators of the module. -/
theorem surjective_val_app_of_isColimit_of_isAffineOver (hab : a ≫ b = 0)
    (hM : IsColimit (CokernelCofork.ofπ b hab)) (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left))) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine_of_isColimit B S hS F hF a b hab' hab hM W hW
    (isSheafFor_cokernel_of_isAffineOver B S hS F hF κ ι hQ hP a W hW)
    (injective_map_cokernel_of_isAffineOver B S hS F hF κ ι hQ hP a)

end Target

end SmallEtale

end AlgebraicGeometry.Space

end
