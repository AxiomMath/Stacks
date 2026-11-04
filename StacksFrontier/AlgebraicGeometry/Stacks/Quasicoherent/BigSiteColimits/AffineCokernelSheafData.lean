module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffinePresentationExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSheafCondition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.SheafifiedCokernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts

/-!
# Surjectivity on sections of a presenting morphism from the sheaf condition at one affine object

Let `b : P ⟶ N` be an epimorphism of sheaves of modules on a slice of the fppf site associated
with a category fibred in groupoids over a big fppf category of schemes, let `a : Q ⟶ P` satisfy
`a.val ≫ b.val = 0`, and let `θ` be the morphism from the cokernel of `a.val` computed in
presheaves of modules to `N` which the universal property produces.  Surjectivity of `b` on the
sections over an object is equivalent to surjectivity of `θ` there, the projection onto a
presheaf cokernel being surjective on sections by construction, and
`CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows` reduces surjectivity
of `θ` over an object to four statements: local injectivity of `θ`, the sheaf condition for the
presheaf cokernel for one covering family of that object, separatedness of the presheaf cokernel
over the pairwise fibre products of that family, and a lift of the section over each member of
the family.

This file discharges the last of the four and assembles the other three, in a form in which every
object they speak of is affine.  The family is produced from local surjectivity of an epimorphism
of sheaves of modules, refined to a finite family of affine objects inside the sieve over whose
arrows the section lifts; the fibre product of two affine objects over an affine object of a slice
is again affine, so separatedness is only ever asked for at affine objects; and the target of `θ`
is a sheaf, so separatedness for it is free.  What is left over is exactly the sheaf condition and
the separatedness, both at affine objects, which is where the Amitsur complex of a faithfully flat
ring map computes everything.

## Main results

* `CategoryTheory.Presieve.isSeparatedFor_ofArrows_of_injective`: **separatedness for a family of
  arrows is injectivity of the joint restriction map.**
* `SheafOfModules.cokernelDesc_app_π_app`: the composite of the projection onto the presheaf
  cokernel with the induced morphism is the presenting morphism, on sections.
* `SheafOfModules.surjective_val_app_of_surjective_app_cokernelDesc`: **the presenting morphism
  is surjective on the sections over an object as soon as the morphism out of the presheaf
  cokernel is.**
* `SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows`: the same reduction
  carried through `CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows`, so
  that what is asked for is one covering family per section.
* `AlgebraicGeometry.FibredSite.isAffineOver_pullback`: **the fibre product of two affine objects
  of a slice of the associated fppf site over an affine object is affine.**
* `AlgebraicGeometry.FibredSite.isSeparatedFor_affine_of_injective_map`: **separatedness of a
  presheaf for every covering sieve of an affine object follows from injectivity of restriction to
  the members of the finite covering families of affine objects.**
* `AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_lift_cokernelDesc`: **a section of
  the target of an epimorphism of sheaves of modules lifts to the presheaf cokernel over the
  members of a finite covering family of affine objects.**
* `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine`: **the presenting
  morphism of an epimorphism of sheaves of modules is surjective on the sections over an affine
  object**, given local injectivity of the morphism out of the presheaf cokernel, the sheaf
  condition for that presheaf cokernel for the finite covering families of affine objects of that
  object, and its separatedness for the covering sieves of the affine objects.
* `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_injective_map`: the
  same with separatedness replaced by injectivity of restriction, which leaves two hypotheses
  mentioning no sieve beyond one covering family of affine objects.
* `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit`: the same
  with local injectivity discharged as well, so that **the presenting morphism of a presentation
  is surjective on the sections over an affine object as soon as the presheaf cokernel satisfies
  the sheaf condition for the finite covering families of affine objects and restriction to the
  members of such a family is injective on its sections over an affine object.**

## Implementation notes

Local injectivity of the morphism out of the presheaf cokernel is taken in the explicit
`∃ T ∈ J Z, ∀ f, T f → …` shape of the corresponding hypothesis of
`CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows`, rather than through
`CategoryTheory.Presheaf.IsLocallyInjective`, so that the statements here are independent of
which of the two a caller holds; it is a hypothesis of the intermediate statements and is
discharged in the last one by
`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`.

The covering family is indexed by `Fin k`: it comes from
`AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over`, which cuts a covering sieve
of an affine object down to a finite family of affine objects, and finiteness is what makes the
index type that small.  The index universe of the family of
`CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows` is free, so no
universe lift is involved.

The two sheafification conditions on the slice are instance arguments rather than being produced
here.  They hold on every slice of the associated site by
`AlgebraicGeometry.FibredSite.hasWeakSheafify_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_over`, but only in the universe of the
schemes, whereas the statements below leave the universe of the module sections free.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' z w v u r m

namespace CategoryTheory.Presieve

/-- **Separatedness for a family of arrows is injectivity of the joint restriction map.**  Two
amalgamations of a family of elements have the same restriction along each arrow of the family,
namely the element the family assigns to it, so a presheaf whose joint restriction map to the
members is injective has at most one amalgamation.

For the sections of a presheaf of modules composed with the forgetful functor to sets the joint
restriction map is the one of `SheafOfModules.injective_restrict`, so this is the translation
between separatedness for a covering family and injectivity of restriction to its members. -/
theorem isSeparatedFor_ofArrows_of_injective {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {X : C} {I : Type w'} {Y : I → C} (g : ∀ i, Y i ⟶ X)
    (hinj : Function.Injective fun s : F.obj (Opposite.op X) => fun i => F.map (g i).op s) :
    IsSeparatedFor F (Presieve.ofArrows Y g) := fun _ _t₁ _t₂ ht₁ ht₂ =>
  hinj (funext fun i => (ht₁ (g i) (ofArrows.mk i)).trans (ht₂ (g i) (ofArrows.mk i)).symm)

end CategoryTheory.Presieve

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {Q P N : SheafOfModules.{m} R}

/-- The projection onto the cokernel of `a.val` computed in presheaves of modules, followed by
the morphism to `N` which the universal property produces, is `b.val` on the sections over every
object.  This is the definitional equation behind both statements below, named so that it can be
rewritten with. -/
theorem cokernelDesc_app_π_app (a : Q ⟶ P) (b : P ⟶ N) (hab' : a.val ≫ b.val = 0) (X : Cᵒᵖ)
    (q : P.val.obj X) :
    (cokernel.desc a.val b.val hab').app X ((cokernel.π a.val).app X q) = b.val.app X q := by
  have h : ((cokernel.π a.val ≫ cokernel.desc a.val b.val hab').app X) q = b.val.app X q := by
    conv_lhs => rw [cokernel.π_desc]
  rwa [PresheafOfModules.comp_app] at h

/-- **A presenting morphism is surjective on the sections over an object as soon as the morphism
out of the presheaf cokernel is.**  The projection onto a cokernel of presheaves of modules is
surjective on the sections over every object, being an epimorphism computed object by object, and
the presenting morphism is its composite with the morphism out of the cokernel. -/
theorem surjective_val_app_of_surjective_app_cokernelDesc (a : Q ⟶ P) (b : P ⟶ N)
    (hab' : a.val ≫ b.val = 0) (X : Cᵒᵖ)
    (h : Function.Surjective ((cokernel.desc a.val b.val hab').app X)) :
    Function.Surjective (b.val.app X) := fun n => by
  obtain ⟨s, hs⟩ := h n
  obtain ⟨q, hq⟩ := PresheafOfModules.surjective_of_epi (cokernel.π a.val) X s
  exact ⟨q, by rw [← cokernelDesc_app_π_app a b hab' X q, hq]; exact hs⟩

/-- **Surjectivity of a presenting morphism on the sections over an object from one covering
family per section.**  For each section of `N` over `W` a covering family of `W` is required,
carrying the sheaf condition for the cokernel of `a.val` computed in presheaves of modules,
separatedness of that cokernel over the pairwise fibre products of the family, and a lift of the
section to the cokernel over each member; together with local injectivity of the morphism from the
cokernel to `N`, this makes `b` surjective on the sections over `W`.

This is `CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows` for the
morphism out of the presheaf cokernel, read back through
`SheafOfModules.surjective_val_app_of_surjective_app_cokernelDesc`; separatedness of `N` for the
family is free because `N` is a sheaf, so it is not a hypothesis. -/
theorem surjective_val_app_of_forall_exists_isSheafFor_arrows (a : Q ⟶ P) (b : P ⟶ N)
    (hab' : a.val ≫ b.val = 0) {W : C}
    (hloc : ∀ (Z : C) (s t : (cokernel a.val).obj (op Z)),
      (cokernel.desc a.val b.val hab').app (op Z) s
          = (cokernel.desc a.val b.val hab').app (op Z) t →
        ∃ T : Sieve Z, T ∈ J Z ∧ ∀ ⦃V : C⦄ (f : V ⟶ Z), T f →
          (cokernel a.val).map f.op s = (cokernel a.val).map f.op t)
    (h : ∀ n : N.val.obj (op W), ∃ (I : Type w') (Y : I → C) (g : ∀ i, Y i ⟶ W),
      ∃ _ : (Presieve.ofArrows Y g).HasPairwisePullbacks,
        Presieve.IsSheafFor
            ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
            (Presieve.ofArrows Y g) ∧
          Sieve.ofArrows Y g ∈ J W ∧
          (∀ (i j : I) (T : Sieve (CategoryTheory.Limits.pullback (g i) (g j))),
              T ∈ J (CategoryTheory.Limits.pullback (g i) (g j)) →
            Presieve.IsSeparatedFor
              ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
              (T : Presieve (CategoryTheory.Limits.pullback (g i) (g j)))) ∧
          ∀ i, ∃ s : (cokernel a.val).obj (op (Y i)),
            (cokernel.desc a.val b.val hab').app (op (Y i)) s = N.val.map (g i).op n) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_surjective_app_cokernelDesc a b hab' (op W)
    (Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows
      (F := (cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (G := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map
        (cokernel.desc a.val b.val hab')) (CategoryTheory.forget AddCommGrpCat.{m})) J
      (fun Z s t hst => hloc Z s t hst)
      fun n => by
        obtain ⟨I, Y, g, hpb, hsh, hcov, hsep, hn⟩ := h n
        exact ⟨I, Y, g, hpb, hsh, (N.isSheafFor_ofArrows g hcov).isSeparatedFor, hsep, hn⟩)

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **The fibre product of two affine objects of a slice of the associated fppf site over an
affine object is affine.**  A category fibred in groupoids over the big fppf category of schemes
has fibre products, hence so does each of its slices; the projection of a slice and the structure
functor both carry the fibre product square to a fibre product square, the first because a cospan
is a connected shape and the second because every morphism of a category fibred in groupoids is
strongly cartesian; and the functor to schemes preserves fibre products.  So the scheme underlying
the fibre product is the fibre product of three affine schemes, which is affine. -/
theorem isAffineOver_pullback (hp : p.IsFiberedInGroupoids) {x : 𝒳} {W Y Z : Over x}
    (f : Y ⟶ W) (g : Z ⟶ W) (hW : IsAffineOver B S hS (p.obj W.left))
    (hY : IsAffineOver B S hS (p.obj Y.left)) (hZ : IsAffineOver B S hS (p.obj Z.left)) :
    haveI : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
    IsAffineOver B S hS (p.obj (CategoryTheory.Limits.pullback f g).left) := by
  have : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have h1 : IsPullback (CategoryTheory.Limits.pullback.fst f g).left
      (CategoryTheory.Limits.pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map (Over.forget x)
  have h2 := (Functor.IsFiberedInGroupoids.map_isPullback p hp f.left g.left _ _ h1).map
    (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj W.left)) := hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left)) := hY
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Z.left)) := hZ
  exact IsAffine.of_isIso h2.isoPullback.hom

/-- **Separatedness of a presheaf for every covering sieve of an affine object of a slice of the
associated fppf site follows from injectivity of restriction to the members of the finite
covering families of affine objects.**

A covering sieve of an affine object contains a finite covering family of affine objects
(`AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over`); separatedness for a family
of arrows of a sieve gives separatedness for the sieve
(`CategoryTheory.Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le`); and separatedness for a
family of arrows is injectivity of restriction to its members
(`CategoryTheory.Presieve.isSeparatedFor_ofArrows_of_injective`).

This is the form in which separatedness of a presheaf cokernel is proved: there are no sieves and
no topology left in the hypothesis, only injectivity of a restriction map between the sections
over two affine objects, which is what a base-change comparison along a faithfully flat covering
morphism supplies. -/
theorem isSeparatedFor_affine_of_injective_map (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (F : (Over x)ᵒᵖ ⥤ Type z)
    (hinj : ∀ (Z : Over x), IsAffineOver B S hS (p.obj Z.left) →
      ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
        Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z →
          Function.Injective fun s : F.obj (op Z) => fun i => F.map (g i).op s)
    (Z : Over x) (hZ : IsAffineOver B S hS (p.obj Z.left)) (T : Sieve Z)
    (hT : T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z) :
    Presieve.IsSeparatedFor F (T : Presieve Z) := by
  obtain ⟨k, Y, g, hYaff, hgT, hgcov⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS p hp Z.hom hZ T hT
  exact Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le F T g hgT
    (Presieve.isSeparatedFor_ofArrows_of_injective g (hinj Z hZ k Y g hYaff hgcov))

section Presentation

variable (hp : p.IsFiberedInGroupoids) {x : 𝒳}
  {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
  [HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x) AddCommGrpCat.{m}]
  [((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
    AddCommGrpCat.{m}]
  {Q P N : SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ N) [Epi b]
  (hab' : a.val ≫ b.val = 0)

include hp in
/-- **A section of the target of an epimorphism of sheaves of modules lifts to the presheaf
cokernel over the members of a finite covering family of affine objects.**

An epimorphism of sheaves of modules is locally surjective
(`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`), so the arrows along which
a given section of the target restricts into the image of `b` form a covering sieve of the object
it lives over; at an affine object that sieve contains a finite covering family of affine objects
(`AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over`).  A lift through `b` over a
member is carried to a lift through the morphism out of the presheaf cokernel by the projection
onto that cokernel.

This is the one hypothesis of
`SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows` which asks nothing of the
presheaf cokernel beyond its construction, and it is discharged here outright. -/
theorem exists_finite_affine_ofArrows_lift_cokernelDesc (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) (n : N.val.obj (op W)) :
    ∃ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) ∧
        Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W ∧
          ∀ i, ∃ s : (cokernel a.val).obj (op (Y i)),
            (cokernel.desc a.val b.val hab').app (op (Y i)) s = N.val.map (g i).op n := by
  have hls := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    (J := (BigFppfOver.associatedTopology B S hS p .fppf).over x) (R := R) b
  obtain ⟨k, Y, g, hYaff, hgS, hgcov⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS p hp W.hom hW
      (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map b.val) n)
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf R.obj).map b.val) (U := op W) n)
  refine ⟨k, Y, g, hYaff, hgcov, fun i => ?_⟩
  obtain ⟨q, hq⟩ := hgS i
  exact ⟨(cokernel.π a.val).app (op (Y i)) q,
    (SheafOfModules.cokernelDesc_app_π_app a b hab' (op (Y i)) q).trans hq⟩

include hp in
/-- **A presenting morphism of an epimorphism of sheaves of modules on a slice of the associated
fppf site is surjective on the sections over an affine object**, given local injectivity of the
morphism from the cokernel of `a.val` computed in presheaves of modules to `N`, the sheaf
condition for that cokernel for the finite covering families of affine objects of the object in
question, and its separatedness for the covering sieves of the affine objects.

Every object the two remaining hypotheses speak of is affine: the covering family comes from
`AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_lift_cokernelDesc`, whose members are
affine, and the fibre product of two of them over the affine object they cover is affine by
`AlgebraicGeometry.FibredSite.isAffineOver_pullback`.  Nothing is asked of the presheaf cokernel
at a non-affine object, and nothing is asked of it at the object itself beyond the sheaf condition
for that one family. -/
theorem surjective_val_app_of_isSheafFor_affine (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left))
    (hloc : ∀ (Z : Over x) (s t : (cokernel a.val).obj (op Z)),
      (cokernel.desc a.val b.val hab').app (op Z) s
          = (cokernel.desc a.val b.val hab').app (op Z) t →
        ∃ T : Sieve Z, T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z ∧
          ∀ ⦃V : Over x⦄ (f : V ⟶ Z), T f →
            (cokernel a.val).map f.op s = (cokernel a.val).map f.op t)
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hsep : ∀ Z : Over x, IsAffineOver B S hS (p.obj Z.left) →
      ∀ T : Sieve Z, T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z →
        Presieve.IsSeparatedFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (T : Presieve Z)) :
    Function.Surjective (b.val.app (op W)) := by
  have : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  refine SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows a b hab' hloc
    fun n => ?_
  obtain ⟨k, Y, g, hYaff, hgcov, hn⟩ :=
    exists_finite_affine_ofArrows_lift_cokernelDesc B S hS p hp a b hab' W hW n
  exact ⟨Fin k, Y, g, inferInstance, hsheaf k Y g hYaff hgcov, hgcov,
    fun i j T hT => hsep _ (isAffineOver_pullback B S hS p hp (g i) (g j) hW
      (hYaff i) (hYaff j)) T hT, hn⟩

include hp in
/-- **The same with separatedness replaced by injectivity of restriction.**  The separatedness
hypothesis of `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine` is supplied
by `AlgebraicGeometry.FibredSite.isSeparatedFor_affine_of_injective_map`, which asks instead that
restriction to the members of a finite covering family of affine objects be injective on the
sections of the presheaf cokernel over an affine object.

This is the shape in which the two remaining hypotheses are statements about the sections of the
presheaf cokernel over two affine objects and nothing else: `hinj` mentions no sieve, and `hsheaf`
mentions one covering family.  Both are what a base-change comparison for the presheaf cokernel
along a covering morphism of affine objects produces, through
`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel` together with
`PresheafOfModules.injective_restrictₛₗ_of_bijective_baseChange` and
`PresheafOfModules.isSheafFor_ofArrows_of_cechDiff₀`. -/
theorem surjective_val_app_of_isSheafFor_affine_of_injective_map (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left))
    (hloc : ∀ (Z : Over x) (s t : (cokernel a.val).obj (op Z)),
      (cokernel.desc a.val b.val hab').app (op Z) s
          = (cokernel.desc a.val b.val hab').app (op Z) t →
        ∃ T : Sieve Z, T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z ∧
          ∀ ⦃V : Over x⦄ (f : V ⟶ Z), T f →
            (cokernel a.val).map f.op s = (cokernel a.val).map f.op t)
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hinj : ∀ Z : Over x, IsAffineOver B S hS (p.obj Z.left) →
      ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
        Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z →
          Function.Injective fun s : (cokernel a.val).obj (op Z) =>
            fun i => (cokernel a.val).map (g i).op s) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine B S hS p hp a b hab' W hW hloc hsheaf
    fun Z hZ T hT => isSeparatedFor_affine_of_injective_map B S hS p hp
      ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) hinj Z hZ T hT

include hp hab' in
/-- **The presenting morphism of a presentation of a sheaf of modules on a slice of the associated
fppf site is surjective on the sections over an affine object**, given the sheaf condition for the
cokernel of `a.val` computed in presheaves of modules for the finite covering families of affine
objects of that object, and injectivity of restriction to the members of such a family on its
sections over an affine object.

This is `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_injective_map`
with local injectivity of the comparison to `N` discharged by
`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`, which needs of the presentation
only that `b` is a cokernel of `a` in sheaves of modules.  So the two hypotheses which remain are
the whole of what the cokernel step of a global presentation asks for, and both are statements
about the sections of the presheaf cokernel over affine objects. -/
theorem surjective_val_app_of_isSheafFor_affine_of_isColimit (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left))
    (hsheaf : ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
          (Presieve.ofArrows Y g))
    (hinj : ∀ Z : Over x, IsAffineOver B S hS (p.obj Z.left) →
      ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
        Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z →
          Function.Injective fun s : (cokernel a.val).obj (op Z) =>
            fun i => (cokernel a.val).map (g i).op s) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine_of_injective_map B S hS p hp a b hab' W hW
    (fun Z s t hst =>
      SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq a b hab hN hab' Z s t hst)
    hsheaf hinj

end Presentation

end AlgebraicGeometry.FibredSite

end
