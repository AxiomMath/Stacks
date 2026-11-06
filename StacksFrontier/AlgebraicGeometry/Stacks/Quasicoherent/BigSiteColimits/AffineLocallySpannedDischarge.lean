module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocalSpanning

/-!
# The span condition at the affine objects, from a global presentation

On a slice of the fppf site associated with a category fibred in groupoids over a big fppf
category of schemes, at an *affine* object `x`, the terminal object is `x` itself and the affine
objects of the slice are those whose underlying scheme is affine.  This file composes the two
halves of the span condition there:

* `SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app` turns surjectivity of a
  presenting morphism on the sections over an affine object into the statement that the sections
  there are spanned by the restrictions of the sections over `x`, given bases of the sections of
  the presenting coproduct over both objects;
* `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit` supplies
  that surjectivity from the sheaf condition for the cokernel of the presenting morphism computed
  in presheaves of modules, together with injectivity of restriction to the members of a finite
  covering family of affine objects.

The bases come from `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` at the two
objects, the injectivity from
`AlgebraicGeometry.FibredSite.injective_map_cokernel_of_isAffineOver`, and the sheaf condition is
the one hypothesis which remains.  So the span condition at the affine objects of such a slice is
reduced to the sheaf condition for the presheaf cokernel of the presentation, and nothing else.

No instance is created for the module structures: the ring of global functions on the object
covered acts on the sections over an affine object of the slice through the induced map of global
functions, the algebra structure is the one that map defines, and the scalar towers hold by
`rfl`, so a consumer's own structures are not shadowed.

The relations half of a global presentation asks the same question for the kernel of a covering
of the module by a coproduct of copies of the structure sheaf.  Its module-theoretic content is
recorded here as `Module.BaseChange.mem_span_image_ker_of_liftBaseChange`: a section of the
coproduct over an affine object which the presenting morphism kills is a combination of the
restrictions of the sections it kills over the terminal object.  This is the exact counterpart,
for the relations, of `Module.BaseChange.surjective_liftBaseChange_of_generators`, and it needs
one thing more than that lemma does — injectivity, not merely surjectivity, of the base-change
comparison for the module presented — which is right exactness of the tensor product at work.

## Main results

* `AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_isColimit_cokernelCofork`: **the
  sections of a presented sheaf of modules over an affine object of the slice site at an affine
  object are spanned by the restrictions of its sections over that affine object**, given the
  sheaf condition for the cokernel of the presenting morphism computed in presheaves of modules
  for the finite covering families of affine objects.
* `AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_hasGlobalPresentation`: the same for a
  sheaf of modules which has a global presentation on that slice, with the presentation data
  consumed, which is the form the span condition of
  `AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_globalSectionSpan_eq_top` asks for.
* `Module.BaseChange.mem_span_image_ker_of_liftBaseChange`: **a relation among the sections of a
  coproduct over an affine object is a combination of the relations over the terminal object**, as
  soon as the base-change comparison of the presenting coproduct is surjective and that of the
  module presented is injective.

## Implementation notes

The commutative rings are the rings of global functions on the underlying schemes and the module
structures over them are the structures over the rings of sections of the coefficient sheaf of
rings, which are the same rings definitionally
(`AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj`).  They are introduced by
`inferInstanceAs` rather than by a global instance, and the action of the ring of global functions
on the object covered on the sections over a member is `Module.compHom` along the induced map, so
that both scalar towers are `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

The types of those rings are written out rather than abbreviated: a `let`-bound type in the proof
of a theorem is lifted to an auxiliary definition whose statement no longer mentions the ring of
sections, and the lifted statement then fails to typecheck against the one the consumer needs.

The two sheafification conditions on the slice are instance arguments of the first statement,
whose universe of module sections is free, and are produced inside the second from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, which apply because the
universe in which global presentations are taken is at least that of the objects and of the
morphisms of the slice.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe y v w u t

namespace Module.BaseChange

variable {A Bc : Type*} [CommRing A] [CommRing Bc] [Algebra A Bc]
  {PT NT PW NW : Type*} [AddCommGroup PT] [Module A PT] [AddCommGroup NT] [Module A NT]
  [AddCommGroup PW] [Module A PW] [Module Bc PW] [IsScalarTower A Bc PW]
  [AddCommGroup NW] [Module A NW] [Module Bc NW] [IsScalarTower A Bc NW]

/-- **A relation among the sections over an object is a combination of the relations over the
base.**  Let `bW` be the base change of `bT` along `A → Bc`, in the sense that the two squares of
restriction maps commute on elements, let the base-change comparison for the source be surjective
and that for the target injective, and let `bT` be surjective.  Then an element of `PW` which `bW`
kills lies in the `Bc`-span of the restrictions of the elements of `PT` which `bT` kills.

This is the relations counterpart of
`Module.BaseChange.surjective_liftBaseChange_of_generators`, and the one place where injectivity
of the comparison for the module presented is used rather than surjectivity: the element is
written as a base change, its image under `bT ⊗ 1` is seen to vanish, and right exactness of the
tensor product (`LinearMap.lTensor_exact` applied to the kernel of `bT`) exhibits it as coming
from the base change of that kernel. -/
theorem mem_span_image_ker_of_liftBaseChange (bT : PT →ₗ[A] NT) (bW : PW →ₗ[Bc] NW)
    (rP : PT →ₗ[A] PW) (rN : NT →ₗ[A] NW) (hsqb : ∀ p, rN (bT p) = bW (rP p))
    (hP : Function.Surjective (rP.liftBaseChange Bc))
    (hN : Function.Injective (rN.liftBaseChange Bc)) (hbT : Function.Surjective bT) {z : PW}
    (hz : bW z = 0) : z ∈ Submodule.span Bc (rP '' (LinearMap.ker bT : Set PT)) := by
  have key : ∀ u : Bc ⊗[A] LinearMap.ker bT,
      rP.liftBaseChange Bc (LinearMap.lTensor Bc (LinearMap.ker bT).subtype u) ∈
        Submodule.span Bc (rP '' (LinearMap.ker bT : Set PT)) := by
    intro u
    induction u with
    | tmul c k =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, k.2, rfl⟩)
    | add u u' hv hv' => rw [map_add, map_add]; exact add_mem hv hv'
  obtain ⟨y, rfl⟩ := hP z
  have h0 : LinearMap.lTensor Bc bT y = 0 := hN (by
    rw [liftBaseChange_comp_lTensor (A := A) (B := Bc) bT bW rP rN hsqb y, hz, map_zero])
  obtain ⟨u, hu⟩ :=
    (lTensor_exact Bc (LinearMap.exact_subtype_ker_map bT) hbT y).1 h0
  exact hu ▸ key u

end Module.BaseChange

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

section Presentation

variable
  [HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x) AddCommGrpCat.{max t u}]
  [((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
    AddCommGrpCat.{max t u}]
  {K I : Type y}
  {Q P N : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
    (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
    (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P) (b : P ⟶ N) [Epi b]

omit [HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
    AddCommGrpCat.{max t u}]
  [((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
    AddCommGrpCat.{max t u}] [Epi b] in
include hp ι hP in
/-- **The span condition at an affine object, once the presenting morphism is surjective on the
sections there.**  If `b : P ⟶ N` is surjective on the sections over an affine object `W` of the
slice, then every section of `N` over `W` is a combination, over the ring of sections of the
structure sheaf there, of restrictions of sections of `N` over the affine terminal object `x`.

This is `SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app`, whose two bases are
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` at the terminal object `x` and at `W`.
The module structures over the rings of global functions are the structures over the rings of
sections of the coefficient sheaf, which are the same rings definitionally, and the action of the
ring of global functions on `x` on the sections over `W` is `Module.compHom` along the induced map,
so that both scalar towers hold by `rfl`. -/
private theorem globalSectionSpan_eq_top_of_surjective_val_app_of_isAffineOver
    (hx : IsAffineOver B S hS (p.obj x)) (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left))
    (hsurj : Function.Surjective (b.val.app (op W))) :
    N.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  let mod : ∀ (M : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
      (V : Over x), Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤)
        (M.val.obj (op V)) := fun M V => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op V)) (M.val.obj (op V)))
  let mPT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P.val.obj (op (Over.mk (𝟙 x)))) := mod P (Over.mk (𝟙 x))
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := mod N (Over.mk (𝟙 x))
  let alg : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map
      (p.map (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x)).left)).appTop.hom
  let modW : ∀ M : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x),
      Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (M.val.obj (op W)) := fun M =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  have tw : ∀ M : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x),
      IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (M.val.obj (op W)) := fun M =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app
    (Over.mkIdTerminal (X := x)) ι b Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Over.mk (𝟙 x)) hx
      (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Over.mk (𝟙 x)) hx _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP W hW _ _ i)
    { toFun := fun q => P.val.map (Over.mkIdTerminal.from W).op q
      map_add' := map_add (P.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c q =>
        (P.val.map_smul (Over.mkIdTerminal.from W).op c q).symm ▸ rfl }
    (fun _ => rfl)
    { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
    (fun _ => rfl)
    { toFun := fun q => b.val.app (op (Over.mk (𝟙 x))) q
      map_add' := map_add (b.val.app (op (Over.mk (𝟙 x)))).hom
      map_smul' := fun c q => (b.val.app (op (Over.mk (𝟙 x)))).hom.map_smul c q }
    (fun _ => rfl)
    { toFun := fun q => b.val.app (op W) q
      map_add' := map_add (b.val.app (op W)).hom
      map_smul' := fun c q => (b.val.app (op W)).hom.map_smul c q }
    (fun _ => rfl) hsurj
    (sectionRingEquivGamma B S hS p hp .fppf W).symm.toRingHom (fun _ _ => rfl)

include hp κ ι hQ hP in
/-- **The sections of a presented sheaf of modules over an affine object of the slice site at an
affine object are spanned by the restrictions of its sections over that affine object.**

Let `b : P ⟶ N` be a cokernel of `a : Q ⟶ P` in sheaves of modules on the slice at an affine
object `x`, with `P` and `Q` coproducts of copies of the universe lift of the structure sheaf, and
let `W` be an affine object of the slice. Then every section of `N` over `W` is a combination, over
the ring of sections of the structure sheaf there, of restrictions of sections of `N` over `x`.

The two ingredients are
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit`, which makes
`b` surjective on the sections over `W` given the sheaf condition for the cokernel of `a.val`
computed in presheaves of modules — its injectivity hypothesis is discharged here by
`AlgebraicGeometry.FibredSite.injective_map_cokernel_of_isAffineOver` — and
`SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app`, whose two bases are
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` at the terminal object `x` and at
`W`.  The relations of the presentation and exactness of its sections play no part. -/
theorem globalSectionSpan_eq_top_of_isColimit_cokernelCofork (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (hx : IsAffineOver B S hS (p.obj x))
    (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left))
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
          (Presieve.ofArrows Y g)) :
    N.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  have hzero : ∀ {Y Z : SheafOfModules.{max t u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)}, (0 : Y ⟶ Z).val = 0 := rfl
  have hab' : a.val ≫ b.val = 0 := by rw [← SheafOfModules.comp_val, hab, hzero]
  exact globalSectionSpan_eq_top_of_surjective_val_app_of_isAffineOver B S hS p hp ι hP b hx W hW
    (surjective_val_app_of_isSheafFor_affine_of_isColimit B S hS p hp a b hab' hab hN
      W hW hsheaf (injective_map_cokernel_of_isAffineOver B S hS p hp κ ι hQ hP a))

end Presentation

include hp in
/-- **The span condition at the affine objects for a sheaf of modules with a global presentation
on the slice site at an affine object.**  This is
`AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_isColimit_cokernelCofork` with the
presentation data consumed, so that what remains is the sheaf condition for the cokernels of the
presenting morphisms computed in presheaves of modules, asked for at the finite covering families
of affine objects of each affine object of the slice.

The conclusion is the body of the hypothesis `hgen` of
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_globalSectionSpan_eq_top`, with
quasi-coherence of the module replaced by a global presentation on the slice itself.  The two are
not the same condition: `SheafOfModules.IsQuasicoherentOnSite` provides global presentations only
after restriction to the members of a covering family of an object, never over the object itself.

The two sheafification conditions are produced here rather than assumed, because the universe in
which global presentations are taken is at least that of the objects and that of the morphisms of
the slice. -/
theorem globalSectionSpan_eq_top_of_hasGlobalPresentation (hx : IsAffineOver B S hS (p.obj x))
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation)
    (hsheaf : ∀ {K I : Type (max v w u)}
      {Q P : SheafOfModules.{max v w u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
      (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u}
          (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ Q)
      (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u}
          (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P),
      IsColimit (Cofan.mk Q κ) → IsColimit (Cofan.mk P ι) → ∀ (a : Q ⟶ P) (V : Over x),
        IsAffineOver B S hS (p.obj V.left) →
        ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ V),
          (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
          Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) V →
            Presieve.IsSheafFor
              ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max v w u})
              (Presieve.ofArrows Y g))
    (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left)) :
    M.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hN⟩⟩ := hM
  have _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      AddCommGrpCat.{max v w u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max v w u, w, max v w} _
  have _ : ((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max v w u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max v w u, max v w, w} _
  have _ : Epi b := Cofork.IsColimit.epi hN
  refine Submodule.eq_top_iff'.2 fun n => ?_
  refine SheafOfModules.down_mem_globalSectionSpan_of_mem_uliftForPresentation
    (Over.mkIdTerminal (X := x)) M W (x := ULift.up n) ?_
  rw [globalSectionSpan_eq_top_of_isColimit_cokernelCofork B S hS p hp κ ι hQ hP a b hab hN hx
    W hW (hsheaf κ ι hQ hP a W hW)]
  exact Submodule.mem_top

end AlgebraicGeometry.FibredSite

end
