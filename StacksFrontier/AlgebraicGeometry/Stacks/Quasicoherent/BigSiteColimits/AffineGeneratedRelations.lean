module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition

/-!
# The relations half of a global presentation follows from the presentation

A global presentation of a sheaf of modules on the slice site at an affine object exhibits it as
the cokernel of a map between coproducts of copies of the structure sheaf.  The *relations*
condition `SheafOfModules.HasGeneratedRelations` asks more: that the kernel of **every** covering
of the module by a coproduct of copies of the structure sheaf be again a quotient of such a
coproduct.  This file proves that the one implies the other, so that on those slice sites the two
halves of a global presentation are consequences of having one.

The module-theoretic core is already available.  A relation over an object `W` is a combination of
the restrictions of the relations over the base as soon as the base-change comparison of the
covering coproduct is surjective and that of the module presented is *injective*
(`Module.BaseChange.mem_span_image_ker_of_liftBaseChange`, right exactness of the tensor product
at the kernel).  Three things remain, and they are what this file supplies.

*The comparison for the module presented must be bijective, not merely surjective.*  That needs
the fourth exactness condition on the sections of the presentation — over an affine object a
section killed by the presenting morphism is a value of the presenting map — which a presentation
does not give away, because the sections of a cokernel in sheaves are not the cokernel of the
sections.  It is proved here from separatedness of the presheaf cokernel at the affine objects.

*The covering must be surjective on the sections over the base.*  This is the one statement which
is neither formal nor an instance of the surjectivity of a presenting morphism: the covering is an
arbitrary epimorphism, and
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver` needs it to be a
cokernel of a morphism out of a coproduct, which is the conclusion being proved.  It is proved by
faithfully flat descent along a finite covering family of affine objects which is fppf in schemes:
the product of the rings of global functions on the members is faithfully flat over the ring of the
base, and membership in the image descends along it.  It is also indispensable — without it the
conclusion is false already for modules, since `ℤ --2--> ℤ` tensored with `ℤ/2` has a kernel which
the base change of the kernel does not reach.

*The kernel must be computed on sections.*  Evaluation at an object preserves finite limits, so a
limit kernel fork of sheaves of modules is one of modules over each object.

## Main results

* `Module.Descent.mem_range_of_mem_range_of_baseChangeHom`: **membership in the image descends
  along a faithfully flat base change presented by additive maps**, a surjection for the source
  and an injection for the target being all that is used.
* `Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange`: **joint detection of images
  by a finite family of base changes whose product of rings is faithfully flat.**
* `SheafOfModules.bijective_liftBaseChange_of_exact_sections`: the sections of a presented sheaf of
  modules over a covering object as a base change, in the named rather than existential form.
* `SheafOfModules.injective_val_app_of_isLimit_kernelFork` and
  `SheafOfModules.mem_range_val_app_of_isLimit_kernelFork`: a kernel of a morphism of sheaves of
  modules is a kernel on the sections over every object.
* `AlgebraicGeometry.FibredSite.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`:
  **the sections of a presentation over an affine object are exact.**
* `AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_ker_of_isColimit_cokernelCofork`: **the
  relations among the sections of a covering of a presented sheaf of modules over an affine object
  are combinations of the relations over the base.**
* `AlgebraicGeometry.FibredSite.surjective_val_app_mkId_of_epi_of_isColimit_cokernelCofork`: **an
  epimorphism onto a presented sheaf of modules from a coproduct of copies of the structure sheaf
  is surjective on the sections over the affine object the slice is taken at.**
* `AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_of_hasGlobalPresentation` and
  `AlgebraicGeometry.FibredSite.hasGeneratedRelations_of_hasGlobalPresentation`: **the relations
  half of a global presentation follows from the global presentation.**
* `AlgebraicGeometry.FibredSite`'s
  `isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasGlobalPresentation`: both
  halves of the span condition on such a slice site.

## Implementation notes

The rings are the rings of global functions on the underlying schemes and the modules of sections
are modules over the rings of sections of the coefficient sheaf of rings, which are the same rings
definitionally (`AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj`).  They are
introduced by `inferInstanceAs`, the action of the ring of the base on the sections over a member
is `Module.compHom` along the induced map, and both scalar towers are then
`IsScalarTower.of_algebraMap_smul fun _ _ => rfl`; no instance is created.  The underlying schemes
are written out rather than abbreviated, because a `let`-bound scheme is lifted into an auxiliary
definition together with the module structures mentioning it and the lifting does not survive the
kernel.

The algebra structure along the arrow to the terminal object is needed in two syntactic forms, at
`p.obj x` and at `p.obj (Over.mk (𝟙 x)).left`: instance search does not identify them, so the
second is introduced as a second local definition with the same value.

`SheafOfModules.bijective_liftBaseChange_of_exact_sections` duplicates the hypotheses of
`SheafOfModules.exists_baseChangeEquiv_of_exact_sections` rather than being derived from it,
because an existentially quantified equivalence cannot be handed to a later hypothesis which must
speak of the same map: what the two descent statements consume is bijectivity of the base change
of the given restriction map itself.

The comparison for the base change along the product of the rings of the members of a covering
family is assembled from the member-wise comparisons additively, by
`Module.BaseChange.exists_piAddEquiv`: the base change along the product is a module over the
product while each member's is a module over that member, so no single ring is available over
which one linear comparison could be stated.  This is why
`Module.Descent.mem_range_of_mem_range_of_baseChangeHom` is stated for additive maps.

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

namespace Module.Descent

variable (A Sa : Type*) [CommRing A] [CommRing Sa] [Algebra A Sa] [Module.FaithfullyFlat A Sa]

/-- **Membership in the image descends along a faithfully flat base change presented by additive
maps.**  This is `Module.Descent.mem_range_of_mem_range_of_baseChangeEquiv` with the two linear
equivalences weakened to a surjection for the source and an injection for the target: those are
the only two properties its proof uses, and the base change along a finite product of rings is
compared with a product of base changes additively only. -/
theorem mem_range_of_mem_range_of_baseChangeHom
    {M M' MS M'S : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup MS] [AddCommGroup M'S] (f : M →ₗ[A] M') (fS : MS →+ M'S)
    (eM : Sa ⊗[A] M →+ MS) (heM : Function.Surjective eM)
    (eM' : Sa ⊗[A] M' →+ M'S) (heM' : Function.Injective eM')
    (hsq : ∀ z, fS (eM z) = eM' (LinearMap.lTensor Sa f z))
    {m' : M'} (hm : ∃ q, fS q = eM' ((1 : Sa) ⊗ₜ[A] m')) :
    m' ∈ LinearMap.range f := by
  obtain ⟨q, hq⟩ := hm
  obtain ⟨z, rfl⟩ := heM q
  exact mem_range_of_one_tmul_mem_range A Sa f ⟨z, heM' ((hsq z).symm.trans hq)⟩

end Module.Descent

namespace Module.BaseChange

variable (A : Type*) [CommRing A] {ιi : Type*} [Finite ιi] (Bi : ιi → Type*)
  [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]

/-- **Joint detection of images by a finite family of base changes.**  Let `bT` be a map of
`A`-modules and let, for each member `i` of a finite family, the base change along `A → Bᵢ` of the
source be surjective onto a module `PW i` and that of the target inject into a module `NW i`, the
two squares commuting.  If the product of the `Bᵢ` is faithfully flat over `A`, then an element of
the target whose image in each `NW i` is a value of `bW i` is itself a value of `bT`.

This is the module-theoretic content of surjectivity on global sections of an epimorphism of
sheaves of modules over an affine base: the family is a covering family of affine objects, the
`Bᵢ` are the rings of functions on its members, and no member need be faithfully flat on its own.
The comparison for the product is assembled from those of the members by
`Module.BaseChange.exists_piAddEquiv`, and the descent is
`Module.Descent.mem_range_of_mem_range_of_baseChangeHom`. -/
theorem mem_range_of_forall_mem_range_of_liftBaseChange
    [Module.FaithfullyFlat A (∀ i, Bi i)]
    {PT NT : Type*} [AddCommGroup PT] [Module A PT] [AddCommGroup NT] [Module A NT]
    {PW NW : ιi → Type*} [∀ i, AddCommGroup (PW i)] [∀ i, Module A (PW i)]
    [∀ i, Module (Bi i) (PW i)] [∀ i, IsScalarTower A (Bi i) (PW i)]
    [∀ i, AddCommGroup (NW i)] [∀ i, Module A (NW i)]
    [∀ i, Module (Bi i) (NW i)] [∀ i, IsScalarTower A (Bi i) (NW i)]
    (bT : PT →ₗ[A] NT) (bW : ∀ i, PW i →ₗ[Bi i] NW i)
    (rP : ∀ i, PT →ₗ[A] PW i) (rN : ∀ i, NT →ₗ[A] NW i)
    (hsq : ∀ (i) (q : PT), rN i (bT q) = bW i (rP i q))
    (hP : ∀ i, Function.Surjective ((rP i).liftBaseChange (Bi i)))
    (hN : ∀ i, Function.Injective ((rN i).liftBaseChange (Bi i)))
    {n : NT} (hn : ∀ i, rN i n ∈ LinearMap.range (bW i)) :
    n ∈ LinearMap.range bT := by
  obtain ⟨EP, hEP⟩ := exists_piAddEquiv A PT Bi (fun i => Bi i ⊗[A] PT) fun _ => AddEquiv.refl _
  obtain ⟨EN, hEN⟩ := exists_piAddEquiv A NT Bi (fun i => Bi i ⊗[A] NT) fun _ => AddEquiv.refl _
  have hEP' : ∀ (s : ∀ i, Bi i) (m : PT) (i : ιi), EP (s ⊗ₜ[A] m) i = s i ⊗ₜ[A] m := hEP
  have hEN' : ∀ (s : ∀ i, Bi i) (m : NT) (i : ιi), EN (s ⊗ₜ[A] m) i = s i ⊗ₜ[A] m := hEN
  let eP : (∀ i, Bi i) ⊗[A] PT →+ (∀ i, PW i) :=
    (AddMonoidHom.piMap fun i => ((rP i).liftBaseChange (Bi i) : _ →+ _)).comp EP.toAddMonoidHom
  let eN : (∀ i, Bi i) ⊗[A] NT →+ (∀ i, NW i) :=
    (AddMonoidHom.piMap fun i => ((rN i).liftBaseChange (Bi i) : _ →+ _)).comp EN.toAddMonoidHom
  let fS : (∀ i, PW i) →+ (∀ i, NW i) := AddMonoidHom.piMap fun i => (bW i : _ →+ _)
  have heP : Function.Surjective eP := fun q => by
    choose z hz using fun i => hP i (q i)
    refine ⟨EP.symm z, funext fun i => ?_⟩
    show (rP i).liftBaseChange (Bi i) (EP (EP.symm z) i) = q i
    rw [EP.apply_symm_apply]
    exact hz i
  have heN : Function.Injective eN := fun z z' hzz' =>
    EN.injective (funext fun i => hN i (congrFun hzz' i))
  have hsqS : ∀ z, fS (eP z) = eN (LinearMap.lTensor (∀ i, Bi i) bT z) := fun z => by
    induction z with
    | zero =>
      rw [map_zero eP, map_zero fS, map_zero (LinearMap.lTensor (∀ i, Bi i) bT), map_zero eN]
    | add z z' hz hz' =>
      rw [map_add eP, map_add fS, hz, hz', map_add (LinearMap.lTensor (∀ i, Bi i) bT),
        map_add eN]
    | tmul s q =>
      refine funext fun i => ?_
      show bW i ((rP i).liftBaseChange (Bi i) (EP (s ⊗ₜ[A] q) i)) =
        (rN i).liftBaseChange (Bi i) (EN (LinearMap.lTensor (∀ i, Bi i) bT (s ⊗ₜ[A] q)) i)
      rw [hEP' s q i, LinearMap.lTensor_tmul, hEN' s (bT q) i, LinearMap.liftBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, map_smul, hsq i q]
  refine Module.Descent.mem_range_of_mem_range_of_baseChangeHom A (∀ i, Bi i) bT fS eP heP eN heN
    hsqS ?_
  choose q hq using hn
  refine ⟨fun i => q i, funext fun i => ?_⟩
  show bW i (q i) = (rN i).liftBaseChange (Bi i) (EN ((1 : ∀ i, Bi i) ⊗ₜ[A] n) i)
  rw [hEN' (1 : ∀ i, Bi i) n i, LinearMap.liftBaseChange_tmul, Pi.one_apply, one_smul, hq i]

end Module.BaseChange

namespace SheafOfModules

section Generic

universe uC vC rr tt ww

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{rr}}
  {T W : C} {K I : Type ww} {Q P N : SheafOfModules.{max tt rr} R}
  (κ : ∀ _ : K, uliftForPresentation.{uC, vC, rr, rr, tt} (unit R) ⟶ Q)
  (ι : ∀ _ : I, uliftForPresentation.{uC, vC, rr, rr, tt} (unit R) ⟶ P)
  (h : W ⟶ T) (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
  [Module A (Q.val.obj (op T))] [Module A (P.val.obj (op T))] [Module A (N.val.obj (op T))]
  [Module A (Q.val.obj (op W))] [Module Bc (Q.val.obj (op W))]
  [IsScalarTower A Bc (Q.val.obj (op W))]
  [Module A (P.val.obj (op W))] [Module Bc (P.val.obj (op W))]
  [IsScalarTower A Bc (P.val.obj (op W))]
  [Module A (N.val.obj (op W))] [Module Bc (N.val.obj (op W))]
  [IsScalarTower A Bc (N.val.obj (op W))]
  (basQT : Module.Basis K A (Q.val.obj (op T))) (basQW : Module.Basis K Bc (Q.val.obj (op W)))
  (basPT : Module.Basis I A (P.val.obj (op T))) (basPW : Module.Basis I Bc (P.val.obj (op W)))
  (hbasQT : ∀ k, basQT k = tautGen κ k (op T)) (hbasQW : ∀ k, basQW k = tautGen κ k (op W))
  (hbasPT : ∀ i, basPT i = tautGen ι i (op T)) (hbasPW : ∀ i, basPW i = tautGen ι i (op W))
  (rQ : Q.val.obj (op T) →ₗ[A] Q.val.obj (op W)) (hrQ : ∀ y, rQ y = Q.val.restrictₛₗ h.op y)
  (rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W)) (hrP : ∀ y, rP y = P.val.restrictₛₗ h.op y)
  (rN : N.val.obj (op T) →ₗ[A] N.val.obj (op W)) (hrN : ∀ y, rN y = N.val.restrictₛₗ h.op y)

include hbasQT hbasQW hbasPT hbasPW hrQ hrP hrN in
/-- **The sections of a presented sheaf of modules over a covering object are the base change of
its sections over the base, in the form of the canonical comparison.**  This is
`SheafOfModules.exists_baseChangeEquiv_of_exact_sections` with the conclusion named rather than
existentially quantified: what is asserted is bijectivity of the base change of the given
restriction map `rN` itself, which is what the two descent statements of this file consume — an
existentially quantified equivalence cannot be handed on to a hypothesis speaking of the same
map.

The hypotheses are those of that statement: the two coproducts of the presentation have the
tautological generators as bases of their sections over both objects, the presenting morphism is
surjective on the sections over both, it kills the composite with `a` over the base, and over the
covering object a section it kills is a value of `a`.  The two commuting squares are the
naturality of `a` and of `b`. -/
theorem bijective_liftBaseChange_of_exact_sections (a : Q ⟶ P) (b : P ⟶ N)
    (aT : Q.val.obj (op T) →ₗ[A] P.val.obj (op T)) (haT : ∀ q, aT q = a.val.app (op T) q)
    (bT : P.val.obj (op T) →ₗ[A] N.val.obj (op T)) (hbT : ∀ q, bT q = b.val.app (op T) q)
    (aW : Q.val.obj (op W) →ₗ[Bc] P.val.obj (op W)) (haW : ∀ q, aW q = a.val.app (op W) q)
    (bW : P.val.obj (op W) →ₗ[Bc] N.val.obj (op W)) (hbW : ∀ q, bW q = b.val.app (op W) q)
    (hab : ∀ q, b.val.app (op T) (a.val.app (op T) q) = 0)
    (hsurjT : Function.Surjective (b.val.app (op T)))
    (hsurjW : Function.Surjective (b.val.app (op W)))
    (hkerW : ∀ y, b.val.app (op W) y = 0 → y ∈ LinearMap.range (a.val.app (op W)).hom) :
    Function.Bijective (rN.liftBaseChange Bc) := by
  refine Module.BaseChange.bijective_liftBaseChange_of_presentation aT bT aW bW rQ rP rN
    (fun q => ?_) (fun q => ?_)
    (bijective_liftBaseChange_of_tautBasis κ h A Bc basQT basQW hbasQT hbasQW rQ hrQ)
    (bijective_liftBaseChange_of_tautBasis ι h A Bc basPT basPW hbasPT hbasPW rP hrP)
    (fun n => ?_) (fun n => ?_) (fun q => ?_) fun q hq => ?_
  · rw [haT, hrP, haW, hrQ]
    exact (PresheafOfModules.naturality_apply a.val h.op q).symm
  · rw [hbT, hrN, hbW, hrP]
    exact (PresheafOfModules.naturality_apply b.val h.op q).symm
  · obtain ⟨q, hq⟩ := hsurjT n
    exact ⟨q, by rw [hbT]; exact hq⟩
  · obtain ⟨q, hq⟩ := hsurjW n
    exact ⟨q, by rw [hbW]; exact hq⟩
  · rw [hbT, haT]
    exact hab q
  · obtain ⟨y, hy⟩ := hkerW q (by rw [← hbW]; exact hq)
    exact ⟨y, by rw [haW]; exact hy⟩

end Generic

section Kernel

universe uK vK rK mK

variable {C : Type uK} [Category.{vK} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{rK}}
  {P N Z : SheafOfModules.{mK} R} {b : P ⟶ N} {k : Z ⟶ P} {hk : k ≫ b = 0}

/-- **A kernel of a morphism of sheaves of modules is a kernel on the sections over every
object.**  Evaluation at an object preserves finite limits
(`SheafOfModules.Finite.evaluationPreservesFiniteLimits`), so it carries a limit kernel fork to a
limit kernel fork of modules, whose inclusion is a monomorphism, that is, injective.

The kernel is taken as a limit fork rather than as `CategoryTheory.Limits.kernel` because that is
the form in which `SheafOfModules.HasGeneratedRelations` quantifies over it. -/
theorem injective_val_app_of_isLimit_kernelFork (hZ : IsLimit (KernelFork.ofι k hk)) (X : Cᵒᵖ) :
    Function.Injective (k.val.app X) := by
  have _ : (evaluation R X).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.mono_iff_injective _).1
    (mono_of_isLimit_fork (KernelFork.mapIsLimit _ hZ (evaluation R X)))

/-- **A section killed by a morphism of sheaves of modules is a value of its kernel inclusion.**
The companion of `SheafOfModules.injective_val_app_of_isLimit_kernelFork`: evaluation at an
object carries the limit kernel fork to one of modules, where the kernel inclusion is exact. -/
theorem mem_range_val_app_of_isLimit_kernelFork (hZ : IsLimit (KernelFork.ofι k hk)) (X : Cᵒᵖ)
    {q : P.val.obj X} (hq : b.val.app X q = 0) :
    q ∈ LinearMap.range (k.val.app X).hom := by
  have _ : (evaluation R X).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hz : (evaluation R X).map k ≫ (evaluation R X).map b = 0 := by
    rw [← Functor.map_comp, hk, Functor.map_zero]
  have hex := (ShortComplex.mk _ _ hz).exact_of_f_is_kernel
    (KernelFork.mapIsLimit _ hZ (evaluation R X))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  exact hex q hq

/-- A section of a source over an object is sent to zero by a composite of morphisms of sheaves of
modules which vanishes. -/
private theorem app_comp_eq_zero {M₁ M₂ M₃ : SheafOfModules.{mK} R} {f : M₁ ⟶ M₂} {g : M₂ ⟶ M₃}
    (h : f ≫ g = 0) (X : Cᵒᵖ) (q : M₁.val.obj X) : g.val.app X (f.val.app X q) = 0 := by
  have h' := congr($(h).val.app X q)
  rwa [SheafOfModules.comp_val] at h'

end Kernel

end SheafOfModules

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
  (a : Q ⟶ P) (b : P ⟶ N)

include hp κ ι hQ hP in
/-- **The sections of a presentation over an affine object are exact.**  Let `b : P ⟶ N` be a
cokernel of `a : Q ⟶ P` in sheaves of modules on the slice site at an object `x`, with `P` and `Q`
coproducts of copies of the universe lift of the structure sheaf, and let `W` be an affine object
of the slice.  Then a section of `P` over `W` which `b` kills is a value of `a` there.

This is the hypothesis `hexW` of `Module.BaseChange.bijective_liftBaseChange_of_presentation`, and
the one of the four exactness conditions on the sections of a presentation which a presentation
does not give away: the sections of a cokernel in sheaves are not the cokernel of the sections.
The comparison from the cokernel of `a.val` computed in presheaves of modules to `N` is locally
injective (`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`) and the presheaf
cokernel is separated for the covering sieves of an affine object
(`AlgebraicGeometry.FibredSite.isSeparatedFor_affine_of_injective_map`, whose injectivity
hypothesis is `AlgebraicGeometry.FibredSite.injective_map_cokernel_of_isAffineOver`), so that
comparison is injective on the sections over `W`
(`CategoryTheory.Presheaf.injective_app_of_isSeparatedFor`); and a section of the presheaf
cokernel which it kills is zero, hence the section it comes from is a value of `a`. -/
theorem mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver (hab : a ≫ b = 0)
    (hab' : a.val ≫ b.val = 0) (hN : IsColimit (CokernelCofork.ofπ b hab)) (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) {z : P.val.obj (op W)}
    (hz : b.val.app (op W) z = 0) :
    z ∈ LinearMap.range (a.val.app (op W)).hom := by
  have hinj := CategoryTheory.Presheaf.injective_app_of_isSeparatedFor
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf
        ((ringStructureSheafCore B S hS p hp .fppf).over x).obj).map
      (cokernel.desc a.val b.val hab')) (CategoryTheory.forget AddCommGrpCat.{max t u}))
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W
    (fun s t hst => SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq a b hab hN
      hab' W s t hst)
    (fun T hT => isSeparatedFor_affine_of_injective_map B S hS p hp _
      (injective_map_cokernel_of_isAffineOver B S hS p hp κ ι hQ hP a) W hW T hT)
  refine (PresheafOfModules.isPresheafCokernel_cokernelπ a.val).mem_range_of_app_eq_zero (op W) ?_
  exact hinj ((SheafOfModules.cokernelDesc_app_π_app a b hab' (op W) z).trans
    (hz.trans (map_zero ((cokernel.desc a.val b.val hab').app (op W)).hom).symm))

include hp κ ι hQ hP in
/-- **The sections of the kernel of a covering of a presented sheaf of modules over an affine
object of the slice site at an affine object are spanned by the restrictions of its sections over
that affine object.**

Let `N` be the cokernel of `a : Q ⟶ P` with `P` and `Q` coproducts of copies of the universe lift
of the structure sheaf, let `b₂ : P₂ ⟶ N` be any morphism from such a coproduct which is
surjective on the sections over the affine object `x` itself, and let `k : Z ⟶ P₂` be a kernel of
`b₂`.  Then the sections of `Z` over an affine object `W` of the slice are combinations, over the
ring of sections of the structure sheaf there, of restrictions of its sections over `x`.

This is the relations counterpart of
`AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_isColimit_cokernelCofork`.  Its
module-theoretic content is `Module.BaseChange.mem_span_image_ker_of_liftBaseChange`, whose
injectivity hypothesis for the comparison of `N` is
`SheafOfModules.bijective_liftBaseChange_of_exact_sections` — the presentation of `N` enters only
through that, and through nothing else.  The sections of `Z` are read off from the limit fork by
`SheafOfModules.injective_val_app_of_isLimit_kernelFork` and
`SheafOfModules.mem_range_val_app_of_isLimit_kernelFork`, so that a relation over `W` is a
combination of restrictions of relations over `x` precisely because `b₂` is surjective on the
sections over `x`: without that surjectivity the tensor product is not right exact at the kernel
and the conclusion fails already for modules. -/
theorem globalSectionSpan_eq_top_ker_of_isColimit_cokernelCofork (hab : a ≫ b = 0)
    (hab' : a.val ≫ b.val = 0) (hcok : IsColimit (CokernelCofork.ofπ b hab))
    (hx : IsAffineOver B S hS (p.obj x)) {I₂ : Type y}
    {P₂ Z : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
      (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N)
    (hsurj₂ : Function.Surjective (b₂.val.app (op (Over.mk (𝟙 x)))))
    (k : Z ⟶ P₂) (hk : k ≫ b₂ = 0) (hZ : IsLimit (KernelFork.ofι k hk))
    (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left)) :
    Z.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  have hepi : Epi b := Cofork.IsColimit.epi hcok
  let mQT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (Q.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (Q.val.obj (op (Over.mk (𝟙 x)))))
  let mPT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P.val.obj (op (Over.mk (𝟙 x)))))
  let mP₂T : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P₂.val.obj (op (Over.mk (𝟙 x)))))
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mQW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (Q.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (Q.val.obj (op W)))
  let mPW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (P.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (P.val.obj (op W)))
  let mP₂W : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (P₂.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (P₂.val.obj (op W)))
  let mNW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.val.obj (op W)))
  let mZW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (Z.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (Z.val.obj (op W)))
  let alg : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map
      (p.map (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x)).left)).appTop.hom
  let mQW' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (Q.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  let mPW' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (P.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  let mP₂W' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (P₂.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  let mNW' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (N.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  have twQ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (Q.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (P.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP₂ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (P₂.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let rP₂ : P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
      P₂.val.obj (op W) :=
    { toFun := fun q => P₂.val.map (Over.mkIdTerminal.from W).op q
      map_add' := map_add (P₂.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c q =>
        (P₂.val.map_smul (Over.mkIdTerminal.from W).op c q).symm ▸ rfl }
  let rN : N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
      N.val.obj (op W) :=
    { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
  have hP₂bij := SheafOfModules.bijective_liftBaseChange_of_tautBasis ι₂
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x))
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx
      (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ W hW
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ W hW _ _ i) rP₂
    (fun _ => rfl)
  have hNinj := SheafOfModules.bijective_liftBaseChange_of_exact_sections κ ι
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x))
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ (Over.mk (𝟙 x)) hx
      (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ W hW
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Over.mk (𝟙 x)) hx
      (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ (Over.mk (𝟙 x)) hx _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ W hW _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Over.mk (𝟙 x)) hx _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP W hW _ _ i)
    { toFun := fun q => Q.val.map (Over.mkIdTerminal.from W).op q
      map_add' := map_add (Q.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c q =>
        (Q.val.map_smul (Over.mkIdTerminal.from W).op c q).symm ▸ rfl }
    (fun _ => rfl)
    { toFun := fun q => P.val.map (Over.mkIdTerminal.from W).op q
      map_add' := map_add (P.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c q =>
        (P.val.map_smul (Over.mkIdTerminal.from W).op c q).symm ▸ rfl }
    (fun _ => rfl)
    rN
    (fun _ => rfl) a b
    (a.val.app (op (Over.mk (𝟙 x)))).hom
    (fun _ => rfl)
    (b.val.app (op (Over.mk (𝟙 x)))).hom
    (fun _ => rfl)
    (a.val.app (op W)).hom
    (fun _ => rfl)
    (b.val.app (op W)).hom
    (fun _ => rfl)
    (SheafOfModules.app_comp_eq_zero hab _)
    (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
      (Over.mk (𝟙 x)) hx)
    (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
      W hW)
    (fun q hq => mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver B S hS p hp κ ι
      hQ hP a b hab hab' hcok W hW hq)
  refine Submodule.eq_top_iff'.2 fun z => ?_
  have hzk : b₂.val.app (op W) (k.val.app (op W) z) = 0 := SheafOfModules.app_comp_eq_zero hk _ z
  let bT₂ : P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
      N.val.obj (op (Over.mk (𝟙 x))) :=
    (b₂.val.app (op (Over.mk (𝟙 x)))).hom
  have hkey := Module.BaseChange.mem_span_image_ker_of_liftBaseChange
    (A := Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤))
    (Bc := Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 x)))) (NT := N.val.obj (op (Over.mk (𝟙 x))))
    (PW := P₂.val.obj (op W)) (NW := N.val.obj (op W)) bT₂
    (by exact (b₂.val.app (op W)).hom)
    rP₂
    rN
    (fun q => (PresheafOfModules.naturality_apply b₂.val
      (Over.mkIdTerminal.from W).op q).symm)
    hP₂bij.2 hNinj.1 hsurj₂ hzk
  have hspan : ∀ q ∈ Submodule.span Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (rP₂ '' (LinearMap.ker bT₂ : Set (P₂.val.obj (op (Over.mk (𝟙 x)))))),
      ∃ ζ ∈ Z.globalSectionSpan (Over.mkIdTerminal (X := x)) W, k.val.app (op W) ζ = q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      obtain ⟨ζ₀, hζ₀⟩ := SheafOfModules.mem_range_val_app_of_isLimit_kernelFork hZ
        (op (Over.mk (𝟙 x))) (show b₂.val.app (op (Over.mk (𝟙 x))) q₀ = 0 from hq₀)
      refine ⟨Z.val.map (Over.mkIdTerminal.from W).op ζ₀,
        Submodule.subset_span ⟨ζ₀, rfl⟩, ?_⟩
      exact (PresheafOfModules.naturality_apply k.val (Over.mkIdTerminal.from W).op ζ₀).trans
        (congrArg (fun y => P₂.val.map (Over.mkIdTerminal.from W).op y) hζ₀)
    | zero => exact ⟨0, zero_mem _, map_zero (k.val.app (op W)).hom⟩
    | add q q' _ _ hζ hζ' =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      obtain ⟨ζ', hζm', hζe'⟩ := hζ'
      exact ⟨ζ + ζ', add_mem hζm hζm', by
        rw [map_add (k.val.app (op W)).hom, hζe, hζe']⟩
    | smul c q _ hζ =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      exact ⟨c • ζ, Submodule.smul_mem _ c hζm, by rw [map_smul, hζe]⟩
  obtain ⟨ζ, hζm, hζe⟩ := hspan _ hkey
  exact SheafOfModules.injective_val_app_of_isLimit_kernelFork hZ (op W) hζe ▸ hζm

include hp κ ι hQ hP in
/-- **An epimorphism onto a presented sheaf of modules from a coproduct of copies of the universe
lift of the structure sheaf is surjective on the sections over an affine object the slice site is
taken at.**

This is the one statement about the relations half of a global presentation which is neither
formal nor an instance of the surjectivity of a *presenting* morphism: `b₂` is an arbitrary
epimorphism from a coproduct of copies of the structure sheaf, not one whose kernel is known to be
such a coproduct, so
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver` does not apply —
that statement needs `b₂` to be a cokernel of a morphism out of a coproduct, which is the
conclusion of the relations condition itself.

It is proved by faithfully flat descent instead.  An epimorphism of sheaves of modules is locally
surjective, so a section over the affine object becomes a value of `b₂` on a covering sieve;
that sieve contains a finite family of affine objects whose image in schemes is an fppf covering
family (`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le_over`), for which the
product of the rings of global functions on the members is faithfully flat over the ring of the
object covered
(`AlgebraicGeometry.FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).  The
sections of the coproduct over a member are the base change of its sections over the affine object
by `SheafOfModules.bijective_liftBaseChange_of_tautBasis`, and those of the presented module by
`SheafOfModules.bijective_liftBaseChange_of_exact_sections`; so
`Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange` descends membership in the
image from the members to the object covered, which is
`SheafOfModules.JointlyDetectsRange`, and
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` concludes. -/
theorem surjective_val_app_mkId_of_epi_of_isColimit_cokernelCofork (hab : a ≫ b = 0)
    (hab' : a.val ≫ b.val = 0) (hcok : IsColimit (CokernelCofork.ofπ b hab))
    (hx : IsAffineOver B S hS (p.obj x)) {I₂ : Type y}
    {P₂ : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
      (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N) [Epi b₂] :
    Function.Surjective (b₂.val.app (op (Over.mk (𝟙 x)))) := by
  have hepi : Epi b := Cofork.IsColimit.epi hcok
  refine SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange.{0} b₂ fun Sv hSv => ?_
  obtain ⟨m, Y, g, hYaff, hmem, hcov, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le_over B S hS p hp (𝟙 x) hx Sv hSv
  refine ⟨Fin m, Y, g, hmem, fun nn hnn => ?_⟩
  let mQT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (Q.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (Q.val.obj (op (Over.mk (𝟙 x)))))
  let mPT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P.val.obj (op (Over.mk (𝟙 x)))))
  let mP₂T : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P₂.val.obj (op (Over.mk (𝟙 x)))))
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mQY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (Q.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (Q.val.obj (op (Y i))))
  let mPY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (P.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (P.val.obj (op (Y i))))
  let mP₂Y : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (P₂.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (P₂.val.obj (op (Y i))))
  let mNY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (N.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (N.val.obj (op (Y i))))
  let alg : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := fun i => RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map (p.map (g i).left)).appTop.hom
  let alg' : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := alg
  let mQY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (Q.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mPY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mP₂Y' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mNY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  have twQ : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (Q.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (P.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP₂ : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (P₂.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (N.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS p Y g hx hYaff hfppf
      fun _ => rfl
  let rP₂ : ∀ i, P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] P₂.val.obj (op (Y i)) := fun i =>
    { toFun := fun q => P₂.val.map (g i).op q
      map_add' := map_add (P₂.val.map (g i).op).hom
      map_smul' := fun c q => (P₂.val.map_smul (g i).op c q).symm ▸ rfl }
  let rN : ∀ i, N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] N.val.obj (op (Y i)) := fun i =>
    { toFun := fun n => N.val.map (g i).op n
      map_add' := map_add (N.val.map (g i).op).hom
      map_smul' := fun c n => (N.val.map_smul (g i).op c n).symm ▸ rfl }
  have hP₂bij : ∀ i, Function.Bijective ((rP₂ i).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := fun i =>
    SheafOfModules.bijective_liftBaseChange_of_tautBasis ι₂ (g i)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx
        (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Y i) (hYaff i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Y i) (hYaff i) _ _ j)
      (rP₂ i) fun _ => rfl
  have hNbij : ∀ i, Function.Bijective ((rN i).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := fun i =>
    SheafOfModules.bijective_liftBaseChange_of_exact_sections κ ι (g i)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ (Over.mk (𝟙 x)) hx
        (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ (Y i) (hYaff i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Over.mk (𝟙 x)) hx
        (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Y i) (hYaff i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ (Over.mk (𝟙 x)) hx _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ (Y i) (hYaff i) _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Over.mk (𝟙 x)) hx _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Y i) (hYaff i) _ _ j)
      { toFun := fun q => Q.val.map (g i).op q
        map_add' := map_add (Q.val.map (g i).op).hom
        map_smul' := fun c q => (Q.val.map_smul (g i).op c q).symm ▸ rfl }
      (fun _ => rfl)
      { toFun := fun q => P.val.map (g i).op q
        map_add' := map_add (P.val.map (g i).op).hom
        map_smul' := fun c q => (P.val.map_smul (g i).op c q).symm ▸ rfl }
      (fun _ => rfl) (rN i) (fun _ => rfl) a b
      (a.val.app (op (Over.mk (𝟙 x)))).hom
      (fun _ => rfl)
      (b.val.app (op (Over.mk (𝟙 x)))).hom
      (fun _ => rfl)
      (a.val.app (op (Y i))).hom
      (fun _ => rfl)
      (b.val.app (op (Y i))).hom
      (fun _ => rfl)
      (SheafOfModules.app_comp_eq_zero hab _)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
        (Over.mk (𝟙 x)) hx)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
        (Y i) (hYaff i))
      (fun q hq => mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver B S hS p hp κ ι
        hQ hP a b hab hab' hcok (Y i) (hYaff i) hq)
  exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    (fun i => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 x)))) (NT := N.val.obj (op (Over.mk (𝟙 x))))
    (PW := fun i => P₂.val.obj (op (Y i))) (NW := fun i => N.val.obj (op (Y i)))
    (b₂.val.app (op (Over.mk (𝟙 x)))).hom
    (fun i =>
      (b₂.val.app (op (Y i))).hom)
    rP₂ rN
    (fun i q => (PresheafOfModules.naturality_apply b₂.val (g i).op q).symm)
    (fun i => (hP₂bij i).2) (fun i => (hNbij i).1)
    fun i => by obtain ⟨q, hq⟩ := hnn i; exact ⟨q, hq⟩

end Presentation

include hp in
/-- **The relations half of a global presentation follows from the global presentation.**  On the
slice site at an affine object `x`, a sheaf of modules with a global presentation satisfies
`SheafOfModules.HasLocallySpannedRelations` at the terminal object `x`: the kernel of every
covering of its universe lift by a coproduct of copies of the structure sheaf is locally spanned
by its sections over `x`.

The two inputs are
`AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_ker_of_isColimit_cokernelCofork`, which is
that span condition at the affine objects of the slice, and
`AlgebraicGeometry.FibredSite.surjective_val_app_mkId_of_epi_of_isColimit_cokernelCofork`, which
discharges its hypothesis that the covering be surjective on the sections over `x`; the passage
from the affine objects to all objects is
`AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_over_of_hasSpannedRelationsOn`.

The quantification is over *every* coproduct covering of the universe lift, not just the one the
presentation provides, which is what `SheafOfModules.HasGeneratedRelations` asks for and what
makes the statement more than a restatement of the presentation. -/
theorem hasLocallySpannedRelations_of_hasGlobalPresentation
    (hx : IsAffineOver B S hS (p.obj x))
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation) :
    M.HasLocallySpannedRelations (Over.mkIdTerminal (X := x)) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hM
  have hzero : ∀ {Y Z : SheafOfModules.{max v w u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)}, (0 : Y ⟶ Z).val = 0 := rfl
  have hab' : a.val ≫ b.val = 0 := by rw [← SheafOfModules.comp_val, hab, hzero]
  have _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      AddCommGrpCat.{max v w u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max v w u, w, max v w} _
  have _ : ((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max v w u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max v w u, max v w, w} _
  refine hasLocallySpannedRelations_over_of_hasSpannedRelationsOn B S hS p hp x
    (Over.mkIdTerminal (X := x)) M fun I₂ P₂ ι₂ hP₂ b₂ hb₂ Z k hk hZ W hW => ?_
  exact globalSectionSpan_eq_top_ker_of_isColimit_cokernelCofork B S hS p hp κ ι hQ hP a b
    hab hab' hcok hx ι₂ hP₂ b₂
    (surjective_val_app_mkId_of_epi_of_isColimit_cokernelCofork B S hS p hp κ ι hQ hP a b hab
      hab' hcok hx ι₂ hP₂ b₂) k hk hZ W hW

include hp in
/-- **A globally presented sheaf of modules on the slice site at an affine object has generated
relations.**  This is
`AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_of_hasGlobalPresentation` in the
categorical form: the kernel of every covering of the universe lift of `M` by a coproduct of
copies of the structure sheaf is again a quotient of such a coproduct.

Together with `SheafOfModules.HasGlobalPresentation.isGeneratedByUnit` this says that the two
halves of a global presentation are consequences of having one, which is the content the
recombination `SheafOfModules.HasGlobalPresentation.of_isGeneratedByUnit` cannot supply: that
statement needs the relations of an arbitrary covering, while a presentation provides only one. -/
theorem hasGeneratedRelations_of_hasGlobalPresentation
    (hx : IsAffineOver B S hS (p.obj x))
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation) :
    M.HasGeneratedRelations :=
  SheafOfModules.hasGeneratedRelations_of_isLocallySpannedBySections (Over.mkIdTerminal (X := x))
    M (hasLocallySpannedRelations_of_hasGlobalPresentation B S hS p hp hx M hM)

include hp in
/-- **Both halves of the span condition on the slice site at an affine object, from a global
presentation there.**  The generators half is
`SheafOfModules.HasGlobalPresentation.isLocallySpannedBySections`, which is formal; the relations
half is `AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_of_hasGlobalPresentation`.

This is the body of `AlgebraicGeometry.FibredSite.IsAffineLocallySpanned` at an affine object,
with quasi-coherence of the module replaced by a global presentation on the slice itself.  The two
are not the same hypothesis: `SheafOfModules.IsQuasicoherentOnSite` provides global presentations
only after restriction to the members of a covering family, never over the object itself. -/
theorem isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasGlobalPresentation
    (hx : IsAffineOver B S hS (p.obj x))
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation) :
    M.IsLocallySpannedBySections (Over.mkIdTerminal (X := x)) ∧
      M.HasLocallySpannedRelations (Over.mkIdTerminal (X := x)) :=
  ⟨hM.isLocallySpannedBySections (Over.mkIdTerminal (X := x)),
    hasLocallySpannedRelations_of_hasGlobalPresentation B S hS p hp hx M hM⟩

end AlgebraicGeometry.FibredSite

end
