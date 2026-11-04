module

public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Global presentations and cokernels

A sheaf of modules on a site is quasi-coherent, in the sense of Stacks 03DL(6), when every
object of the site has a covering on whose members the restricted module has a global
presentation: it is the cokernel of a map between coproducts of copies of the structure sheaf.

This file develops the two things one needs in order to propagate that property along
cokernels.

The first is transport along isomorphisms.  Both `SheafOfModules.HasGlobalPresentation` and
`SheafOfModules.IsQuasicoherentOnSite` are stated about the universe lift
`SheafOfModules.uliftForPresentation` of the module, and that lift has no recorded action on
morphisms, so an isomorphism of modules cannot be moved through it.  The action is supplied
here by `SheafOfModules.uliftForPresentationMap`.

The second is the categorical step of the cokernel argument.  If `b : P ⟶ N` presents `N` as
the cokernel of `a : Q ⟶ P`, and the image of a map `f : M ⟶ N` is the image of a map out of a
further object `F` that lifts along `b`, then the cokernel of `f` is the cokernel of the map
`Q ⊞ F ⟶ P` assembled from `a` and that lift.  Taking `P`, `Q` and `F` to be coproducts of
copies of the structure sheaf, this is exactly the passage from presentations of `M` and `N` to
a presentation of the cokernel of `f`.

## Main definitions

* `SheafOfModules.uliftForPresentationMap` is the action of `SheafOfModules.uliftForPresentation`
  on a morphism.
* `SheafOfModules.uliftForPresentationMapIso` is its action on an isomorphism.

## Main results

* `SheafOfModules.HasGlobalPresentation.of_iso` and
  `SheafOfModules.IsQuasicoherentOnSite.of_iso` transport the two properties along an
  isomorphism of sheaves of modules; the second is also registered as an
  `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance for
  `SheafOfModules.isQuasicoherentOnSite`.
* `CategoryTheory.Limits.isColimitCokernelCoforkCompOfLift`: with `b` a cokernel of `a` and `π`
  a cokernel of `f`, the composite `b ≫ π` is a cokernel of `CategoryTheory.Limits.coprod.desc a l`
  as soon as `l` lifts along `b` a map whose image is the image of `f`.
* `SheafOfModules.isColimitCofanSumOfBinaryCofan`: a binary coproduct of two coproducts of
  copies of one object is a coproduct of copies of that object, indexed by the sum of the two
  index types.
* `SheafOfModules.HasGlobalPresentation.exists_epi_of_isColimit_cofan`: a module with a global
  presentation receives an epimorphism from a coproduct of copies of the structure sheaf.
* `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` assembles the
  previous three into the cokernel step: a cokernel of a morphism between modules with global
  presentations has a global presentation, once the generators of the source lift along the
  presentation of the target.

## Implementation notes

`SheafOfModules.uliftForPresentationMap` and the two transport lemmas belong with
`SheafOfModules.uliftForPresentation` itself, in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite`; they are here only to keep that
file untouched.

`CategoryTheory.Limits.isColimitCokernelCoforkCompOfLift` is stated for an arbitrary category
with zero morphisms and the one binary coproduct it uses, not for sheaves of modules, since
nothing about sheaves enters it.  Its hypothesis `h ≫ b = p ≫ f` with `p` an epimorphism says
that the image of `f` is the image of `h ≫ b`, which is what makes the two cokernels agree; the
epimorphism `p` is where a presentation of the source of `f` is used.

`SheafOfModules.isColimitCofanSumOfBinaryCofan` is proved directly rather than through
`CategoryTheory.Limits.Cofan.combPairIsColimit`, whose cofan is indexed by `Sum.elim` of two
constant families.  That family is only propositionally equal to the constant family on the sum
type, and `CategoryTheory.Limits.Cofan` depends on it, so citing the general version would
require transporting a colimit along an equality of families.

The three hypotheses of `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`
that are not formal consequences of the two presentations are, in order of depth: that the
universe lift of the cokernel projection is again a cokernel projection, that the generators of
the source lift along the presentation of the target, and the binary coproduct.  On the small
étale site of a scheme the coproduct is available, because the presentation universe
`max u v r m` of a site of `Scheme.{u}`-objects is `u + 1`, where sheafification of
`AddCommGrpCat`-valued presheaves exists; the other two are the mathematical content of Stacks
0GNB(3) and are not discharged in this reduction: the lift is the vanishing of the first étale
cohomology of a quasi-coherent module on an affine scheme (Stacks 03DW), which the Stacks proof
of 0GNB routes through the equivalence of Stacks 03DX between quasi-coherent modules on a scheme
and on its small étale site.

That route is the one taken, and 0GNB(3) itself is therefore a theorem on the small étale site
of a scheme, by a different argument than this reduction:
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit_cokernelCofork` and
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isLimit_kernelFork` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer`.  What
stays unavailable is the discharge of these three hypotheses, not the clause.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- The action of the universe lift `SheafOfModules.uliftForPresentation` on a morphism of
sheaves of modules: apply the morphism inside the lift. -/
noncomputable def uliftForPresentationMap {M N : SheafOfModules.{m} R} (f : M ⟶ N) :
    uliftForPresentation.{u, v, r, m, t} M ⟶ uliftForPresentation.{u, v, r, m, t} N where
  val :=
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ULift.up (f.val.app X x.down)
          map_add' := fun x y ↦ congrArg ULift.up (map_add (f.val.app X).hom x.down y.down)
          map_smul' := fun a x ↦ congrArg ULift.up (map_smul (f.val.app X).hom a x.down) }
      naturality := fun {X Y} g ↦ by
        apply ModuleCat.hom_ext
        ext x
        exact congrArg ULift.up
          (congrArg (fun k : ModuleCat.Hom (M.val.obj X) _ ↦ k.hom x.down)
            (f.val.naturality g)) }

/-- On sections over `X`, `uliftForPresentationMap f` sends `x` to the lift of
`f.val.app X x.down`. -/
@[simp]
theorem uliftForPresentationMap_val_app_apply {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (X : Cᵒᵖ) (x : ULift.{t} (M.val.obj X)) :
    (uliftForPresentationMap.{u, v, r, m, t} f).val.app X x =
      ULift.up (f.val.app X x.down) :=
  rfl

/-- `uliftForPresentationMap` sends the identity morphism to the identity morphism. -/
@[simp]
theorem uliftForPresentationMap_id (M : SheafOfModules.{m} R) :
    uliftForPresentationMap.{u, v, r, m, t} (𝟙 M) = 𝟙 _ := by
  ext X x
  exact ULift.ext _ _ rfl

/-- `uliftForPresentationMap` sends a composite to the composite of the images. -/
@[simp]
theorem uliftForPresentationMap_comp {M N P : SheafOfModules.{m} R} (f : M ⟶ N) (g : N ⟶ P) :
    uliftForPresentationMap.{u, v, r, m, t} (f ≫ g) =
      uliftForPresentationMap.{u, v, r, m, t} f ≫ uliftForPresentationMap.{u, v, r, m, t} g := by
  ext X x
  exact ULift.ext _ _ rfl

/-- The action of the universe lift `SheafOfModules.uliftForPresentation` on an isomorphism of
sheaves of modules. -/
@[simps]
noncomputable def uliftForPresentationMapIso {M N : SheafOfModules.{m} R} (e : M ≅ N) :
    uliftForPresentation.{u, v, r, m, t} M ≅ uliftForPresentation.{u, v, r, m, t} N where
  hom := uliftForPresentationMap.{u, v, r, m, t} e.hom
  inv := uliftForPresentationMap.{u, v, r, m, t} e.inv
  hom_inv_id := by rw [← uliftForPresentationMap_comp, e.hom_inv_id, uliftForPresentationMap_id]
  inv_hom_id := by rw [← uliftForPresentationMap_comp, e.inv_hom_id, uliftForPresentationMap_id]

/-- Having a global presentation is invariant under isomorphism: compose the presenting
cokernel map with the universe lift of the isomorphism. -/
theorem HasGlobalPresentation.of_iso {M N : SheafOfModules.{m} R} (e : M ≅ N)
    (h : HasGlobalPresentation M) : HasGlobalPresentation N := by
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, ⟨hb⟩⟩ := h
  refine ⟨I, K, P, Q, ι, κ, hP, hQ, a, b ≫ (uliftForPresentationMapIso e).hom, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, hab, zero_comp]
  · exact hb.ofIsoColimit (Cofork.ext (uliftForPresentationMapIso e) rfl)

/-- Quasi-coherence of a sheaf of modules on a site is invariant under isomorphism: restriction
to a slice site is a functor, so an isomorphism restricts to one on every member of a
covering. -/
theorem IsQuasicoherentOnSite.of_iso {M N : SheafOfModules.{m} R} (e : M ≅ N)
    (h : M.IsQuasicoherentOnSite) : N.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
    exact ⟨I, V, f, hcover,
      fun i ↦ .of_iso ((SheafOfModules.overFunctor R (V i)).mapIso e) (hpres i)⟩

/-- The class of quasi-coherent sheaves of modules on a site is closed under isomorphisms. -/
instance : (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderIsomorphisms where
  of_iso e h := IsQuasicoherentOnSite.of_iso e h

end SheafOfModules

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

/-- The map `Q ⊞ F ⟶ P` assembled from `a : Q ⟶ P` and a lift `l : F ⟶ P` of `p ≫ f` along a
cokernel `b : P ⟶ N` of `a` is killed by `b` followed by any map killing `f`. -/
theorem coprod_desc_comp_comp_eq_zero {Q P N M T F : D} {a : Q ⟶ P} {b : P ⟶ N} {f : M ⟶ N}
    {π : N ⟶ T} {p : F ⟶ M} {l : F ⟶ P} [HasBinaryCoproduct Q F] (hab : a ≫ b = 0)
    (hfπ : f ≫ π = 0) (hl : l ≫ b = p ≫ f) : coprod.desc a l ≫ b ≫ π = 0 := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc_assoc, ← Category.assoc, hab, zero_comp, comp_zero]
  · rw [coprod.inr_desc_assoc, ← Category.assoc, hl, Category.assoc, hfπ, comp_zero, comp_zero]

/-- Let `b : P ⟶ N` be a cokernel of `a : Q ⟶ P` and let `π : N ⟶ T` be a cokernel of
`f : M ⟶ N`.  If `p : F ⟶ M` is an epimorphism and `l : F ⟶ P` satisfies `l ≫ b = p ≫ f`,
then `b ≫ π` is a cokernel of the map `Q ⊞ F ⟶ P` assembled from `a` and `l`.

The hypothesis says that `l ≫ b` and `f` have the same image, so that killing the image of
`l ≫ b` in `N` is the same as killing the image of `f`; killing the image of `a` as well
recovers `T` from `P`. -/
noncomputable def isColimitCokernelCoforkCompOfLift {Q P N M T F : D} {a : Q ⟶ P} {b : P ⟶ N}
    {f : M ⟶ N} {π : N ⟶ T} {p : F ⟶ M} [Epi p] {l : F ⟶ P} [HasBinaryCoproduct Q F]
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (hfπ : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π hfπ))
    (hl : l ≫ b = p ≫ f) :
    IsColimit (CokernelCofork.ofπ (b ≫ π)
      (coprod_desc_comp_comp_eq_zero hab hfπ hl)) := by
  have hbepi : Epi b := Cofork.IsColimit.epi hb
  have hπepi : Epi π := Cofork.IsColimit.epi hπ
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_
  have ha : a ≫ k = 0 := by
    have h := coprod.inl ≫= hk
    rwa [coprod.inl_desc_assoc, comp_zero] at h
  have hlk : l ≫ k = 0 := by
    have h := coprod.inr ≫= hk
    rwa [coprod.inr_desc_assoc, comp_zero] at h
  obtain ⟨k₁, hk₁⟩ := CokernelCofork.IsColimit.desc' hb k ha
  have hk₁' : b ≫ k₁ = k := hk₁
  have hfk₁ : f ≫ k₁ = 0 := by
    rw [← cancel_epi p, ← Category.assoc, ← hl, Category.assoc, hk₁', hlk, comp_zero]
  obtain ⟨k₂, hk₂⟩ := CokernelCofork.IsColimit.desc' hπ k₁ hfk₁
  have hk₂' : π ≫ k₂ = k₁ := hk₂
  exact ⟨k₂, by rw [Category.assoc, hk₂', hk₁']⟩

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- A binary coproduct of two coproducts of copies of one object `O` is a coproduct of copies of
`O` indexed by the sum of the two index types. -/
noncomputable def isColimitCofanSumOfBinaryCofan {K I : Type t} {O P₁ P₂ : SheafOfModules.{m} R}
    {ι₁ : K → (O ⟶ P₁)} {ι₂ : I → (O ⟶ P₂)}
    (h₁ : IsColimit (Cofan.mk P₁ ι₁)) (h₂ : IsColimit (Cofan.mk P₂ ι₂))
    {bc : BinaryCofan P₁ P₂} (h : IsColimit bc) :
    IsColimit (Cofan.mk (f := fun _ : K ⊕ I ↦ O) bc.pt
      (Sum.elim (fun k ↦ ι₁ k ≫ bc.inl) (fun i ↦ ι₂ i ≫ bc.inr))) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ BinaryCofan.IsColimit.desc h
      (Cofan.IsColimit.desc h₁ fun k ↦ s.inj (.inl k))
      (Cofan.IsColimit.desc h₂ fun i ↦ s.inj (.inr i)))
    (fun s j ↦ ?_) (fun s n hn ↦ ?_)
  · cases j with
    | inl k =>
      change (ι₁ k ≫ bc.inl) ≫ _ = _
      rw [Category.assoc, BinaryCofan.IsColimit.inl_desc]
      simpa using Cofan.IsColimit.fac h₁ (fun k ↦ s.inj (.inl k)) k
    | inr i =>
      change (ι₂ i ≫ bc.inr) ≫ _ = _
      rw [Category.assoc, BinaryCofan.IsColimit.inr_desc]
      simpa using Cofan.IsColimit.fac h₂ (fun i ↦ s.inj (.inr i)) i
  · refine BinaryCofan.IsColimit.hom_ext h ?_ ?_
    · refine Cofan.IsColimit.hom_ext h₁ _ _ fun k ↦ ?_
      have hk : (ι₁ k ≫ bc.inl) ≫ n = s.inj (.inl k) := hn (.inl k)
      change ι₁ k ≫ bc.inl ≫ n = ι₁ k ≫ _
      rw [← Category.assoc, hk, BinaryCofan.IsColimit.inl_desc]
      exact (Cofan.IsColimit.fac h₁ (fun k ↦ s.inj (.inl k)) k).symm
    · refine Cofan.IsColimit.hom_ext h₂ _ _ fun i ↦ ?_
      have hi : (ι₂ i ≫ bc.inr) ≫ n = s.inj (.inr i) := hn (.inr i)
      change ι₂ i ≫ bc.inr ≫ n = ι₂ i ≫ _
      rw [← Category.assoc, hi, BinaryCofan.IsColimit.inr_desc]
      exact (Cofan.IsColimit.fac h₂ (fun i ↦ s.inj (.inr i)) i).symm

/-- A module with a global presentation is the target of an epimorphism from a coproduct of
copies of the structure sheaf: the presenting cokernel map is such an epimorphism. -/
theorem HasGlobalPresentation.exists_epi_of_isColimit_cofan {M : SheafOfModules.{m} R}
    (hM : HasGlobalPresentation M) :
    ∃ (I : Type (max u v r m)) (F : SheafOfModules.{max u v r m} R)
      (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ F),
      Nonempty (IsColimit (Cofan.mk F ι)) ∧
        ∃ p : F ⟶ uliftForPresentation.{u, v, r, m, max u v r} M, Epi p := by
  obtain ⟨I, _, P, _, ι, _, hP, _, _, b, _, ⟨hb⟩⟩ := hM
  exact ⟨I, P, ι, hP, b, Cofork.IsColimit.epi hb⟩

/-- **The cokernel step of a global presentation.**  Let `π : N ⟶ T` exhibit `T` as the cokernel
of `f : M ⟶ N`, let `N` be presented as the cokernel of `a : Q ⟶ P` with `P` and `Q` coproducts
of copies of the structure sheaf, and let `p : F ⟶ M` be an epimorphism with `F` such a
coproduct.  If `π` stays a cokernel of `f` after the universe lift, and if `p ≫ f` lifts to a
map `l : F ⟶ P` along the presentation of `N`, then `T` has a global presentation: it is the
cokernel of the map `Q ⊞ F ⟶ P` assembled from `a` and `l`, and `Q ⊞ F` is again a coproduct of
copies of the structure sheaf, indexed by the sum of the two index types.

This is the passage, in the proof of Stacks 0GNB(3), from presentations of the source and target
of a morphism to a presentation of its cokernel.  Everything in the conclusion except the
existence of the lift `l` is formal; the lift is the arithmetic content, and over an affine
object of a scheme site it comes from the surjectivity on sections of a presentation of `N`. -/
theorem HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift
    {M N T : SheafOfModules.{m} R} {f : M ⟶ N} {π : N ⟶ T}
    {I K I' : Type (max u v r m)} {P Q F : SheafOfModules.{max u v r m} R}
    {ι : ∀ _ : I,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ P}
    {κ : ∀ _ : K,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ Q}
    {ν : ∀ _ : I',
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ F}
    (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
    (hF : IsColimit (Cofan.mk F ν)) [HasBinaryCoproduct Q F]
    {a : Q ⟶ P} {b : P ⟶ uliftForPresentation.{u, v, r, m, max u v r} N}
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    {p : F ⟶ uliftForPresentation.{u, v, r, m, max u v r} M} [Epi p] {l : F ⟶ P}
    (hl : l ≫ b = p ≫ uliftForPresentationMap.{u, v, r, m, max u v r} f)
    (hfπ : uliftForPresentationMap.{u, v, r, m, max u v r} f ≫
      uliftForPresentationMap.{u, v, r, m, max u v r} π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ
      (uliftForPresentationMap.{u, v, r, m, max u v r} π) hfπ)) :
    HasGlobalPresentation T :=
  ⟨I, K ⊕ I', P, Q ⨿ F, ι,
    Sum.elim (fun k ↦ κ k ≫ coprod.inl) (fun i ↦ ν i ≫ coprod.inr), ⟨hP⟩,
    ⟨isColimitCofanSumOfBinaryCofan hQ hF
      (bc := BinaryCofan.mk coprod.inl coprod.inr) (coprodIsCoprod Q F)⟩,
    coprod.desc a l, b ≫ uliftForPresentationMap.{u, v, r, m, max u v r} π,
    coprod_desc_comp_comp_eq_zero hab hfπ hl,
    ⟨isColimitCokernelCoforkCompOfLift hab hb hfπ hπ hl⟩⟩

end SheafOfModules

end
