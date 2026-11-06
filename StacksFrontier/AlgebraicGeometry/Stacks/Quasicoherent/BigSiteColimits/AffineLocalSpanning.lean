module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.SheafBaseChange

/-!
# Generation by global sections is an affine condition

A sheaf of modules on a site is locally spanned by its sections over a terminal object when every
section lies, after restriction along the arrows of some covering sieve, in the span of those
global sections.  The condition is local, so it may be tested on one covering family of each
object; on a slice of the fppf site associated with a category fibred in groupoids over a big
fppf category of schemes every object carries a covering family by *affine* objects, and the
condition therefore only has to be checked at affine objects, where the span is asked to be
everything.

This is the reduction that confines the question to the affine objects.  Nothing in it is about
modules over schemes: the index type of the affine covering family lives one universe above the
morphisms of the site and the testing criterion leaves that universe free, so the two fit, and
the statements below hold for an arbitrary sheaf of rings on the slice and an arbitrary sheaf of
modules over it.

The relations half of a global presentation is reduced in the same way.  Its conclusion is the
span condition for the kernel of an arbitrary covering of the module by a coproduct of copies of
the structure sheaf, so the reduction is the same criterion applied to that kernel, and the
hypothesis which remains is `SheafOfModules.HasSpannedRelationsOn`: the same quantification with
the span over the affine objects demanded outright.

What makes the span everything at one object is a comparison exhibiting the sections there as a
base change of the global sections: the base change is spanned over the larger ring by the pure
tensors `1 ⊗ n`, which the comparison carries to the restrictions of the global sections.  Only
surjectivity of the comparison is used, and surjectivity of the comparison for a presented
module needs nothing from the relations of the presentation — so the span condition at an object
follows from a presentation whose generators have their sections a base change there, which a
basis supplies, together with surjectivity of the presenting morphism on the sections over that
object.

## Main definitions

* `SheafOfModules.HasSpannedRelationsOn`: the relations half of a global presentation with the
  span of the global sections demanded at the objects of a prescribed class.

## Main results

* `Module.BaseChange.surjective_liftBaseChange_of_generators`: **surjectivity of the base-change
  comparison passes from the generators of a presentation to the module they generate**, with no
  hypothesis on the relations.
* `SheafOfModules.globalSectionSpan_eq_top_of_baseChangeEquiv`: **the global sections span at an
  object whose sections are a base change of them.**
* `SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app`: **the global sections span at
  an object over which a presenting morphism is surjective on sections.**
* `AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine`: **a sheaf of
  modules on a slice of the associated fppf site whose global sections span at every affine
  object is locally spanned by its global sections.**
* `AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_over_of_hasSpannedRelationsOn`: the
  same reduction for the relations half.
* `AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_globalSectionSpan_eq_top`: **the span
  condition on the affine slice sites follows from its affine-object form**, which is the
  hypothesis of `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules` with both
  occurrences of "locally" removed.

## Implementation notes

`SheafOfModules.HasSpannedRelationsOn` repeats the binders of
`SheafOfModules.HasLocallySpannedRelations` verbatim, including their explicit universe
arguments, so that the two are quantifications over the same data and the reduction between them
is the criterion applied pointwise.

The criterion is stated as a hypothesis on an arbitrary sheaf of modules rather than specialised
to the kernels, because the kernel of a covering is at the universe in which global
presentations are taken, which is above the universe of the module presented.

`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_globalSectionSpan_eq_top` is stated in
the unfolded form of the span condition rather than through the abbreviation of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure`, which is a
consumer of this file.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w v u r m t

namespace Module.BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {PT NT PW NW : Type*} [AddCommGroup PT] [Module A PT] [AddCommGroup NT] [Module A NT]
  [AddCommGroup PW] [Module A PW] [Module B PW] [IsScalarTower A B PW]
  [AddCommGroup NW] [Module A NW] [Module B NW] [IsScalarTower A B NW]

/-- **Surjectivity of the base-change comparison needs only the generators of a presentation.**
If a map `bW` out of the generators is surjective and the generators have surjective base-change
comparison, then so does the module they generate.  Nothing is asked of the relations, of the
exactness of the sections, or of injectivity: this is the half of
`Module.BaseChange.bijective_liftBaseChange_of_presentation` which a span condition consumes. -/
theorem surjective_liftBaseChange_of_generators (bT : PT →ₗ[A] NT) (bW : PW →ₗ[B] NW)
    (rP : PT →ₗ[A] PW) (rN : NT →ₗ[A] NW) (hsqb : ∀ p, rN (bT p) = bW (rP p))
    (hP : Function.Surjective (rP.liftBaseChange B)) (hbW : Function.Surjective bW) :
    Function.Surjective (rN.liftBaseChange B) := fun n => by
  obtain ⟨p, hp⟩ := hbW n
  obtain ⟨x, hx⟩ := hP p
  exact ⟨LinearMap.lTensor B bT x, by
    rw [liftBaseChange_comp_lTensor (A := A) (B := B) bT bW rP rN hsqb x, hx, hp]⟩

end Module.BaseChange

namespace SheafOfModules

section Generic

universe uC vC

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The relations half of a global presentation with the span of the global sections demanded
outright at the objects satisfying `Q`, rather than locally.  The quantification is that of
`SheafOfModules.HasLocallySpannedRelations`, so a criterion turning the span condition at the
objects satisfying `Q` into `SheafOfModules.IsLocallySpannedBySections` carries this to that. -/
def HasSpannedRelationsOn {T : C} (hT : IsTerminal T) (M : SheafOfModules.{m} R)
    (Q : C → Prop) : Prop :=
  ∀ (I : Type (max uC vC r m)) (P : SheafOfModules.{max uC vC r m} R)
    (ι : ∀ _ : I, uliftForPresentation.{uC, vC, r, r, max uC vC m} (unit R) ⟶ P),
    IsColimit (Cofan.mk P ι) →
    ∀ b : P ⟶ uliftForPresentation.{uC, vC, r, m, max uC vC r} M, Epi b →
    ∀ (Z : SheafOfModules.{max uC vC r m} R) (k : Z ⟶ P) (hk : k ≫ b = 0),
      IsLimit (KernelFork.ofι k hk) → ∀ W : C, Q W → Z.globalSectionSpan hT W = ⊤

/-- **The relations half from its unlocalised form.**  A criterion which turns the span condition
at the objects satisfying `Q` into being locally spanned by global sections carries
`SheafOfModules.HasSpannedRelationsOn` to
`SheafOfModules.HasLocallySpannedRelations`. -/
theorem hasLocallySpannedRelations_of_hasSpannedRelationsOn {T : C} (hT : IsTerminal T)
    (M : SheafOfModules.{m} R) (Q : C → Prop)
    (hQ : ∀ Z : SheafOfModules.{max uC vC r m} R,
      (∀ W : C, Q W → Z.globalSectionSpan hT W = ⊤) → Z.IsLocallySpannedBySections hT)
    (h : M.HasSpannedRelationsOn hT Q) : M.HasLocallySpannedRelations hT :=
  fun I P ι hP b hb Z k hk hZ => hQ Z (h I P ι hP b hb Z k hk hZ)

/-- **The global sections span at an object whose sections are a base change of them.**  Let the
sections of `N` over `W` be identified, as a module over a commutative ring `B` acting through
the ring of sections of the structure sheaf there, with the base change along `A → B` of the
sections of `N` over a terminal object, in such a way that `1 ⊗ n` is the restriction of `n`.
Then every section over `W` is a `B`-combination, hence a combination over the sections of the
structure sheaf, of restrictions of global sections.

This is the step from a comparison of the shape
`SheafOfModules.exists_baseChangeEquiv_of_presentation` produces to the span condition at one
object.  Only surjectivity of the comparison is used. -/
theorem globalSectionSpan_eq_top_of_baseChangeEquiv {T W : C} (hT : IsTerminal T)
    (N : SheafOfModules.{m} R) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (N.val.obj (op T))] [Module B (N.val.obj (op W))]
    (ψ : B →+* R.obj.obj (op W))
    (hψ : ∀ (b : B) (n : N.val.obj (op W)), b • n = ψ b • n)
    (e : B ⊗[A] N.val.obj (op T) →ₗ[B] N.val.obj (op W)) (he : Function.Surjective e)
    (hone : ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.val.restrictₛₗ (hT.from W).op n) :
    N.globalSectionSpan hT W = ⊤ := by
  rw [globalSectionSpan_eq_span_range]
  refine Submodule.eq_top_iff'.2 fun n => ?_
  obtain ⟨y, rfl⟩ := he n
  induction y with
  | tmul b x =>
    rw [show b ⊗ₜ[A] x = b • ((1 : B) ⊗ₜ[A] x) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, hψ, hone]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'

/-- **The global sections span at an object over which a presenting morphism is surjective on
sections.**  Let `b : P ⟶ N` be surjective on the sections over `W`, with `P` a coproduct of
copies of the structure sheaf whose tautological generators are a basis of its sections both over
a terminal object `T` and over `W`.  Then the sections of `N` over `W` are spanned by the
restrictions of its sections over `T`.

The relations of the presentation play no part, and neither does exactness of its sections over
`T`: the sections of `N` over `W` are only shown to be a quotient of a base change of its
sections over `T`, which is all a span condition needs.  The bases are
`SheafOfModules.tautBasis` at the two objects, available when each has the finite subcovering
property, and surjectivity over `W` is the vanishing of the first cohomology of the kernel of `b`
there. -/
theorem globalSectionSpan_eq_top_of_surjective_val_app {T W : C} (hT : IsTerminal T)
    {I : Type w} {P N : SheafOfModules.{max t r} R}
    (ι : ∀ _ : I, uliftForPresentation.{uC, vC, r, r, t} (unit R) ⟶ P) (b : P ⟶ N)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (P.val.obj (op T))] [Module A (N.val.obj (op T))]
    [Module A (P.val.obj (op W))] [Module B (P.val.obj (op W))]
    [IsScalarTower A B (P.val.obj (op W))]
    [Module A (N.val.obj (op W))] [Module B (N.val.obj (op W))]
    [IsScalarTower A B (N.val.obj (op W))]
    (basPT : Module.Basis I A (P.val.obj (op T))) (basPW : Module.Basis I B (P.val.obj (op W)))
    (hbasPT : ∀ i, basPT i = tautGen ι i (op T))
    (hbasPW : ∀ i, basPW i = tautGen ι i (op W))
    (rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W))
    (hrP : ∀ x, rP x = P.val.restrictₛₗ (hT.from W).op x)
    (rN : N.val.obj (op T) →ₗ[A] N.val.obj (op W))
    (hrN : ∀ x, rN x = N.val.restrictₛₗ (hT.from W).op x)
    (bT : P.val.obj (op T) →ₗ[A] N.val.obj (op T))
    (hbT : ∀ x, bT x = b.val.app (op T) x)
    (bW : P.val.obj (op W) →ₗ[B] N.val.obj (op W))
    (hbW : ∀ x, bW x = b.val.app (op W) x)
    (hsurj : Function.Surjective (b.val.app (op W)))
    (ψ : B →+* R.obj.obj (op W))
    (hψ : ∀ (c : B) (n : N.val.obj (op W)), c • n = ψ c • n) :
    N.globalSectionSpan hT W = ⊤ := by
  refine globalSectionSpan_eq_top_of_baseChangeEquiv hT N A B ψ hψ (rN.liftBaseChange B) ?_
    fun n => by rw [LinearMap.liftBaseChange_tmul, one_smul, hrN]
  refine Module.BaseChange.surjective_liftBaseChange_of_generators bT bW rP rN (fun x => ?_)
    (bijective_liftBaseChange_of_tautBasis ι (hT.from W) A B basPT basPW hbasPT hbasPW rP hrP).2
    fun n => ?_
  · rw [hbT, hrN, hbW, hrP]
    exact (PresheafOfModules.naturality_apply b.val (hT.from W).op x).symm
  · obtain ⟨x, hx⟩ := hsurj n
    exact ⟨x, by rw [hbW]; exact hx⟩

end Generic

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Being locally spanned by global sections is a condition at the affine objects.**  Every
object of a slice of the associated fppf site carries a covering family by affine objects
(`AlgebraicGeometry.FibredSite.exists_affine_ofArrows_over`), and being locally spanned by global
sections may be tested on one covering family of each object
(`SheafOfModules.isLocallySpannedBySections_of_forall_exists_cover`), whose index universe is
free; so a sheaf of modules whose global sections span at every affine object of the slice is
locally spanned by its global sections.

Nothing is assumed of the sheaf of rings or of the sheaf of modules: the statement is the
locality of the span condition, with the affine objects as the testing family. -/
theorem isLocallySpannedBySections_over_of_forall_affine (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    (h : ∀ W : Over x, IsAffineOver B S hS (p.obj W.left) → N.globalSectionSpan hT W = ⊤) :
    N.IsLocallySpannedBySections hT := by
  refine SheafOfModules.isLocallySpannedBySections_of_forall_exists_cover.{u + 1} hT N ?_
  intro V
  obtain ⟨I, Y, a, hYaff, hcov⟩ := exists_affine_ofArrows_over B S hS p hp x V
  exact ⟨I, Y, a, hcov, fun j => h (Y j) (hYaff j)⟩

/-- **The relations half of a global presentation is a condition at the affine objects.**  This is
`AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine` used as the
criterion of `SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn` for the class of
affine objects of a slice of the associated fppf site. -/
theorem hasLocallySpannedRelations_over_of_hasSpannedRelationsOn (hp : p.IsFiberedInGroupoids)
    (x : 𝒳)
    {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (M : SheafOfModules.{m} R)
    (h : M.HasSpannedRelationsOn hT fun W => IsAffineOver B S hS (p.obj W.left)) :
    M.HasLocallySpannedRelations hT :=
  SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn hT M _
    (fun Z hZ => isLocallySpannedBySections_over_of_forall_affine B S hS p hp x hT Z hZ) h

/-- **The span condition on the affine slice sites from its affine-object form.**  This is the
hypothesis `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules` and
`AlgebraicGeometry.FibredSite.inclusion_preservesColimits` carry, with both occurrences of
"locally" removed: what has to be supplied is that the sections of a quasi-coherent module over
an *affine* object of the slice site at an affine object are spanned by the restrictions of its
sections over that affine object, and the same for the relations between its generators.

The conclusion is stated unfolded because
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure`, where the
abbreviation for it is defined, is a consumer of this file. -/
theorem isAffineLocallySpanned_of_globalSectionSpan_eq_top (hp : p.IsFiberedInGroupoids)
    (hgen : ∀ (i : AffineObjects B S hS p)
      (N : SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i))),
      N.IsQuasicoherentOnSite →
        ∀ W : Over (affineObj B S hS p i), IsAffineOver B S hS (p.obj W.left) →
          N.globalSectionSpan (Over.mkIdTerminal (X := affineObj B S hS p i)) W = ⊤)
    (hrel : ∀ (i : AffineObjects B S hS p)
      (N : SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i))),
      N.IsQuasicoherentOnSite →
        N.HasSpannedRelationsOn (Over.mkIdTerminal (X := affineObj B S hS p i))
          fun W => IsAffineOver B S hS (p.obj W.left)) :
    ∀ (i : AffineObjects B S hS p)
      (N : SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i))),
      N.IsQuasicoherentOnSite →
        N.IsLocallySpannedBySections (Over.mkIdTerminal (X := affineObj B S hS p i)) ∧
          N.HasLocallySpannedRelations (Over.mkIdTerminal (X := affineObj B S hS p i)) :=
  fun i N hN =>
    ⟨isLocallySpannedBySections_over_of_forall_affine B S hS p hp (affineObj B S hS p i)
      Over.mkIdTerminal N (hgen i N hN),
      hasLocallySpannedRelations_over_of_hasSpannedRelationsOn B S hS p hp
        (affineObj B S hS p i) Over.mkIdTerminal N (hrel i N hN)⟩

end AlgebraicGeometry.FibredSite

end
