module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffinePresentationSurjectivity
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineMemberBaseChange

/-!
# The sections over an affine object of a slice of the small étale site as a base change

Let `M` be a sheaf of modules with a global presentation on a slice of the small étale site of an
algebraic space, and let `h : W ⟶ T` be a morphism between two objects of that slice whose
underlying schemes are affine.  This file proves that the sections of `M` over `W` are the base
change, along the induced map of the rings of global functions, of its sections over `T`, with no
hypothesis beyond the presentation.

The reduction is site-independent: `SheafOfModules.bijective_liftBaseChange_of_exact_sections`
asks for four conditions on the sections of the presentation over the two objects, and all four
are available here.  The two coproducts of the presentation have the tautological generators as a
basis over either object
(`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`), the presenting morphism is
surjective on the sections over either object
(`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver`), and a
section it kills over `W` is a value of the presenting map, which is what this file supplies first.

That last condition is the one a presentation does not give away, because the sections of a
cokernel in sheaves are not the cokernel of the sections.  The comparison from the cokernel of
`a.val` computed in presheaves of modules to the module presented is locally injective, and the
presheaf cokernel is separated for the covering sieves of an object whose underlying scheme is
affine (`AlgebraicGeometry.Space.SmallEtale.isSeparatedFor_affine_of_injective_map`, whose
injectivity hypothesis is
`AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`), so that comparison
is injective on the sections over `W`; a section of the presheaf cokernel which it kills is
therefore zero, and the section it comes from is a value of `a`.

Nothing is assumed of the object the slice is taken at, in particular not that its underlying
scheme is affine: the two objects compared have affine underlying scheme and that is all the
sheaf condition for the presheaf cokernel needs.

## Main results

* `AlgebraicGeometry.Space.SmallEtale`'s
  `mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`: **the sections of a presentation
  over an object with affine underlying scheme are exact.**
* `AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation`: **the
  sections of a globally presented sheaf of modules over an object of a slice of the small étale
  site with affine underlying scheme are the base change of its sections over another such
  object**, with no hypothesis beyond the presentation.
* `AlgebraicGeometry.Space.SmallEtale`'s
  `bijective_liftBaseChange_of_hasGlobalPresentation_chart`: **the same for a sheaf of modules on
  the whole small étale site, presented after restriction to a chart**, the two objects compared
  being charts mapping to that one, and
  `bijective_liftBaseChange_of_hasGlobalPresentation_overChart`: **the same read on the slice at
  an arbitrary chart**, which is the form a descent along a covering family of that slice
  consumes.

## Implementation notes

A global presentation presents the universe lift of the module, whose sections are the sections of
the module lifted, so the conclusion for the module itself is the conclusion for the lift
transported along that identification by
`Module.BaseChange.bijective_liftBaseChange_of_comm`.

The commutative rings acting on the modules of sections are taken as explicit data together with
ring identifications with the rings of sections of the coefficient sheaf of rings, as in
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`: the sections of a sheaf of modules
over a `Sheaf J RingCat` carry a ring and nothing more, while a base change needs a commutative
ring, and a caller already holds the module structures its own consumers are stated for.  No
instance is created: every ring acting on a module of sections is either an instance argument of
the statement or a local definition built by `Module.compHom` along the given ring identification,
and the scalar towers are `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

For a module given on the whole small étale site no iterated slice occurs.  The sections of a
restriction `M.over V` at an object of the slice are the sections of `M` at the underlying chart,
and the restriction maps agree likewise, so the comparison between two charts mapping to a third
is the comparison on the slice at that third chart read at the canonical objects; this is why
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation_chart` is a
restatement and not a transport.  The counterpart for a module given only on a slice is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over`, which has
to cross `CategoryTheory.Over.iteratedSliceEquiv`.

The objects of the site are spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules are
indexed by; instance search does not unfold that projection, so the two spellings are not mixed
inside a single declaration.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe z m t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-! ### Exactness of the sections of a presentation over an object with affine underlying scheme -/

section Exactness

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  [HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{max t u}]
  [((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective AddCommGrpCat.{max t u}]
  {K I : Type z}
  {Q P N : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P) (b : P ⟶ N)

include κ ι hQ hP in
/-- **The sections of a presentation over an object of a slice of the small étale site with affine
underlying scheme are exact.**  Let `b : P ⟶ N` be a cokernel of `a : Q ⟶ P` in sheaves of modules
on the slice at an object `V`, with `P` and `Q` coproducts of copies of the universe lift of the
structure sheaf, and let `W` be an object of the slice whose underlying scheme is affine.  Then a
section of `P` over `W` which `b` kills is a value of `a` there.

This is the hypothesis `hkerW` of
`SheafOfModules.bijective_liftBaseChange_of_exact_sections`, and the one of its four exactness
conditions which a presentation does not give away: the sections of a cokernel in sheaves are not
the cokernel of the sections.  The comparison from the cokernel of `a.val` computed in presheaves
of modules to `N` is locally injective
(`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`) and the presheaf cokernel is
separated for the covering sieves of an object with affine underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.isSeparatedFor_affine_of_injective_map`, whose injectivity
hypothesis is
`AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`), so that comparison
is injective on the sections over `W`
(`CategoryTheory.Presheaf.injective_app_of_isSeparatedFor`); and a section of the presheaf
cokernel which it kills is zero, hence the section it comes from is a value of `a`.

It is the small étale counterpart of
`AlgebraicGeometry.FibredSite.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`. -/
theorem mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver (hab : a ≫ b = 0)
    (hab' : a.val ≫ b.val = 0) (hN : IsColimit (CokernelCofork.ofπ b hab)) (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    {n₀ : P.val.obj (op W)} (hn₀ : b.val.app (op W) n₀ = 0) :
    n₀ ∈ LinearMap.range (a.val.app (op W)).hom := by
  have hinj := CategoryTheory.Presheaf.injective_app_of_isSeparatedFor
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf
        (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).over V).obj).map
      (cokernel.desc a.val b.val hab')) (CategoryTheory.forget AddCommGrpCat.{max t u}))
    ((smallEtaleRingedSite B S hS F hF).J.over V) W
    (fun s s' hss' => SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq a b hab hN
      hab' W s s' hss')
    (fun T hT => isSeparatedFor_affine_of_injective_map B S hS F hF _
      (injective_map_cokernel_of_isAffineOver B S hS F hF κ ι hQ hP a) W hW T hT)
  exact (PresheafOfModules.isPresheafCokernel_cokernelπ a.val).mem_range_of_app_eq_zero (op W)
    (hinj ((SheafOfModules.cokernelDesc_app_π_app a b hab' (op W) n₀).trans
      (hn₀.trans (map_zero ((cokernel.desc a.val b.val hab').app (op W)).hom).symm)))

end Exactness

/-! ### The sections over an object with affine underlying scheme as a base change -/

section BaseChange

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}

/-- Scalars of `A` act through the inverse of a ring identification `R ≃+* A` of the ring acting
on a module. -/
private theorem smul_eq_symm_smul {R A X : Type*} [Semiring R] [Semiring A] [AddCommMonoid X]
    [Module R X] [Module A X] (f : R ≃+* A) (hf : ∀ (c : R) (n : X), f c • n = c • n)
    (c : A) (n : X) : c • n = f.symm c • n := by
  rw [← hf (f.symm c) n, f.apply_symm_apply]

/-- For the module structure transported along `f.symm`, `f c` acts as `c`. -/
private theorem ringEquiv_smul_compHom {R A : Type*} (X : Type*) [Semiring R] [Semiring A]
    [AddCommMonoid X] [Module R X] (f : R ≃+* A) (c : R) (n : X) :
    letI := Module.compHom X f.symm.toRingHom
    f c • n = c • n :=
  congrArg (· • n) (f.symm_apply_apply c)

/-- Bijectivity of a base change passes along additive identifications of the source and target
which commute with the scalars and the map. -/
private theorem bijective_liftBaseChange_of_addEquiv {A Bc : Type*} [CommRing A] [CommRing Bc]
    [Algebra A Bc] {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y]
    [AddCommGroup Y'] [Module A X] [Module A X'] [Module A Y] [Module Bc Y]
    [IsScalarTower A Bc Y] [Module A Y'] [Module Bc Y'] [IsScalarTower A Bc Y']
    (r : X →ₗ[A] Y) (r' : X' →ₗ[A] Y') (δ : X ≃+ X') (ε : Y ≃+ Y')
    (hδ : ∀ (c : A) n, δ (c • n) = c • δ n) (hε : ∀ (c : Bc) n, ε (c • n) = c • ε n)
    (hcomm : ∀ n, ε (r n) = r' (δ n)) (hbij : Function.Bijective (r'.liftBaseChange Bc)) :
    Function.Bijective (r.liftBaseChange Bc) :=
  Module.BaseChange.bijective_liftBaseChange_of_comm r r' { δ with map_smul' := hδ }
    { ε with map_smul' := hε } hcomm hbij

/-- **The sections of a globally presented sheaf of modules over an object of a slice of the small
étale site whose underlying scheme is affine are the base change of its sections over another such
object.**

Let `M` be a sheaf of modules on the slice at an object `V` with a global presentation, and let
`h : W ⟶ T` be a morphism between two objects of that slice whose underlying schemes are affine.
Then the comparison from the base change of the sections over `T` to the sections over `W` is
bijective.

This is `SheafOfModules.bijective_liftBaseChange_of_exact_sections` with every hypothesis
discharged.  The four bases are
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`, the presenting morphism is
surjective on the sections over either object by
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver`, and a
section it kills over `W` is a value of the presenting map by
`AlgebraicGeometry.Space.SmallEtale.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`;
neither has an open hypothesis.  Nothing is assumed of the object the slice is taken at, in
particular not that its underlying scheme is affine.

A global presentation presents the universe lift of the module, whose sections are the sections of
the module lifted, so the conclusion for the module itself is the conclusion for the lift
transported along that identification by
`Module.BaseChange.bijective_liftBaseChange_of_comm`.

It is the small étale counterpart of
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation`. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation
    (M : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (hM : M.HasGlobalPresentation)
    {T W : Over V} (h : W ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T.left)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (M.val.obj (op T))] [Module A (M.val.obj (op W))] [Module Bc (M.val.obj (op W))]
    [IsScalarTower A Bc (M.val.obj (op W))]
    (fA : ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
      (op T) : Type u) ≃+* A)
    (hfA : ∀ (c : ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op T) : Type u))
      (n : M.val.obj (op T)), fA c • n = c • n)
    (fB : ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
      (op W) : Type u) ≃+* Bc)
    (hfB : ∀ (c : ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op W) : Type u))
      (n : M.val.obj (op W)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB (((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.map h.op).hom
        (fA.symm c)))
    (r : M.val.obj (op T) →ₗ[A] M.val.obj (op W))
    (hr : ∀ n, r n = M.val.restrictₛₗ h.op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hM
  have _ : HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V)
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : ((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : Epi b := Cofork.IsColimit.epi hcok
  have hzero : ∀ {Y Z : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)},
      (0 : Y ⟶ Z).val = 0 := rfl
  have hab' : a.val ≫ b.val = 0 := by rw [← SheafOfModules.comp_val, hab, hzero]
  -- the `A`-module structures at `T`
  let mQT : Module A (Q.val.obj (op T)) := Module.compHom _ fA.symm.toRingHom
  let mPT : Module A (P.val.obj (op T)) := Module.compHom _ fA.symm.toRingHom
  let mNT : Module A
      ((SheafOfModules.uliftForPresentation.{u + 1, u, u, m, max (u + 1) u} M).val.obj (op T)) :=
    Module.compHom _ fA.symm.toRingHom
  -- the `Bc`-module structures at `W`
  let mQWB : Module Bc (Q.val.obj (op W)) := Module.compHom _ fB.symm.toRingHom
  let mPWB : Module Bc (P.val.obj (op W)) := Module.compHom _ fB.symm.toRingHom
  let mNWB : Module Bc
      ((SheafOfModules.uliftForPresentation.{u + 1, u, u, m, max (u + 1) u} M).val.obj (op W)) :=
    Module.compHom _ fB.symm.toRingHom
  let mQWA : Module A (Q.val.obj (op W)) := Module.compHom _ (algebraMap A Bc)
  let mPWA : Module A (P.val.obj (op W)) := Module.compHom _ (algebraMap A Bc)
  let mNWA : Module A
      ((SheafOfModules.uliftForPresentation.{u + 1, u, u, m, max (u + 1) u} M).val.obj (op W)) :=
    Module.compHom _ (algebraMap A Bc)
  have twQ : IsScalarTower A Bc (Q.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP : IsScalarTower A Bc (P.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : IsScalarTower A Bc
      ((SheafOfModules.uliftForPresentation.{u + 1, u, u, m, max (u + 1) u} M).val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let NU := SheafOfModules.uliftForPresentation.{u + 1, u, u, m, max (u + 1) u} M
  have hfQT : ∀ (c) (n : Q.val.obj (op T)), fA c • n = c • n := fun c n =>
    ringEquiv_smul_compHom _ fA c n
  have hfPT : ∀ (c) (n : P.val.obj (op T)), fA c • n = c • n := fun c n =>
    ringEquiv_smul_compHom _ fA c n
  have hfQW : ∀ (c) (n : Q.val.obj (op W)), fB c • n = c • n := fun c n =>
    ringEquiv_smul_compHom _ fB c n
  have hfPW : ∀ (c) (n : P.val.obj (op W)), fB c • n = c • n := fun c n =>
    ringEquiv_smul_compHom _ fB c n
  have hid : ∀ c : A,
      ((((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.map h.op)).hom
        (fA.symm c)) = fB.symm (algebraMap A Bc c) := fun c => by rw [halg c, fB.symm_apply_apply]
  let rQ : Q.val.obj (op T) →ₗ[A] Q.val.obj (op W) :=
    { toFun := fun q => Q.val.map h.op q
      map_add' := map_add (Q.val.map h.op).hom
      map_smul' := fun c q => (Q.val.map_smul h.op (fA.symm c) q).trans (by rw [hid c]; rfl) }
  let rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W) :=
    { toFun := fun q => P.val.map h.op q
      map_add' := map_add (P.val.map h.op).hom
      map_smul' := fun c q => (P.val.map_smul h.op (fA.symm c) q).trans (by rw [hid c]; rfl) }
  let rNU : NU.val.obj (op T) →ₗ[A] NU.val.obj (op W) :=
    { toFun := fun q => NU.val.map h.op q
      map_add' := map_add (NU.val.map h.op).hom
      map_smul' := fun c q => (NU.val.map_smul h.op (fA.symm c) q).trans (by rw [hid c]; rfl) }
  let aT : Q.val.obj (op T) →ₗ[A] P.val.obj (op T) :=
    { toFun := fun q => a.val.app (op T) q
      map_add' := map_add (a.val.app (op T)).hom
      map_smul' := fun c q => (a.val.app (op T)).hom.map_smul (fA.symm c) q }
  let bT : P.val.obj (op T) →ₗ[A] NU.val.obj (op T) :=
    { toFun := fun q => b.val.app (op T) q
      map_add' := map_add (b.val.app (op T)).hom
      map_smul' := fun c q => (b.val.app (op T)).hom.map_smul (fA.symm c) q }
  let aW : Q.val.obj (op W) →ₗ[Bc] P.val.obj (op W) :=
    { toFun := fun q => a.val.app (op W) q
      map_add' := map_add (a.val.app (op W)).hom
      map_smul' := fun c q => (a.val.app (op W)).hom.map_smul (fB.symm c) q }
  let bW : P.val.obj (op W) →ₗ[Bc] NU.val.obj (op W) :=
    { toFun := fun q => b.val.app (op W) q
      map_add' := map_add (b.val.app (op W)).hom
      map_smul' := fun c q => (b.val.app (op W)).hom.map_smul (fB.symm c) q }
  have hbijU : Function.Bijective (rNU.liftBaseChange Bc) :=
    SheafOfModules.bijective_liftBaseChange_of_exact_sections κ ι h A Bc
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ T hT fA hfQT)
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ W hW fB hfQW)
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP T hT fA hfPT)
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP W hW fB hfPW)
      (fun k => tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ T hT fA hfQT k)
      (fun k => tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ W hW fB hfQW k)
      (fun i => tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP T hT fA hfPT i)
      (fun i => tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP W hW fB hfPW i)
      rQ (fun _ => rfl) rP (fun _ => rfl) rNU (fun _ => rfl) a b aT (fun _ => rfl) bT
      (fun _ => rfl) aW (fun _ => rfl) bW (fun _ => rfl)
      (fun q => by
        have hz := congr($(hab).val.app (op T) q)
        rwa [SheafOfModules.comp_val] at hz)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS F hF κ ι hQ hP a b hab' hab hcok
        T hT)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS F hF κ ι hQ hP a b hab' hab hcok
        W hW)
      (fun y hy => mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver B S hS F hF
        κ ι hQ hP a b hab hab' hcok W hW hy)
  exact bijective_liftBaseChange_of_addEquiv r rNU AddEquiv.ulift.symm AddEquiv.ulift.symm
    (fun c n => by rw [smul_eq_symm_smul fA hfA c n]; rfl)
    (fun c n => by rw [smul_eq_symm_smul fB hfB c n]; rfl)
    (fun n => congrArg ULift.up (hr n)) hbijU

/-- **The sections of a sheaf of modules on the small étale site over a chart with affine
underlying scheme are the base change of its sections over another such chart it maps to**, given
a global presentation of the module restricted to a chart both of them lie over.

Let `M` be a sheaf of modules on the small étale ringed site of an algebraic space, let `V'` be a
chart on whose restriction the module has a global presentation, let `cT : TL ⟶ V'` and
`cW : WL ⟶ V'` with `TL` and `WL` having affine underlying scheme, and let `hl : WL ⟶ TL` be
compatible with them.  Then the sections over `WL` are the base change of the sections over `TL`
along the induced map of the rings of global functions.

This is
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation` on the
slice at `V'`, read at the canonical objects `CategoryTheory.Over.mk cT` and
`CategoryTheory.Over.mk cW`.  Nothing has to be transported: the sections of a restriction at an
object of a slice are the sections of the module at the underlying chart, and the restriction maps
agree likewise, so the two statements are the same statement.  This is what replaces the passage
through `CategoryTheory.Over.iteratedSliceEquiv` which
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over` needs for a
module given only on a slice. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation_chart
    (M : SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)))
    {V' : (smallEtaleRingedSite B S hS F hF).C} (hM : (M.over V').HasGlobalPresentation)
    {TL WL : (smallEtaleRingedSite B S hS F hF).C} (cT : TL ⟶ V') (cW : WL ⟶ V') (hl : WL ⟶ TL)
    (hcl : hl ≫ cT = cW)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj TL)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj WL)))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (M.val.obj (op TL))] [Module A (M.val.obj (op WL))] [Module Bc (M.val.obj (op WL))]
    [IsScalarTower A Bc (M.val.obj (op WL))]
    (fA : (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj
      (op TL) : Type u) ≃+* A)
    (hfA : ∀ (c : (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj
        (op TL) : Type u))
      (n : M.val.obj (op TL)), fA c • n = c • n)
    (fB : (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj
      (op WL) : Type u) ≃+* Bc)
    (hfB : ∀ (c : (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj
        (op WL) : Type u))
      (n : M.val.obj (op WL)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.map hl.op).hom
        (fA.symm c)))
    (r : M.val.obj (op TL) →ₗ[A] M.val.obj (op WL))
    (hr : ∀ n, r n = M.val.restrictₛₗ hl.op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  let gh : (Over.mk cW : Over V') ⟶ Over.mk cT := Over.homMk hl hcl
  let fA0 : ((((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS F hF).O)).over V').obj.obj
    (op (Over.mk cT : Over V')) : Type u) ≃+* A := fA
  let fB0 : ((((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS F hF).O)).over V').obj.obj
    (op (Over.mk cW : Over V')) : Type u) ≃+* Bc := fB
  let mAT0 : Module A ((M.over V').val.obj (op (Over.mk cT : Over V'))) :=
    Module.compHom (R := ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V').obj.obj
      (op (Over.mk cT : Over V')) : Type u)) _ fA0.symm.toRingHom
  let mBW0 : Module Bc ((M.over V').val.obj (op (Over.mk cW : Over V'))) :=
    Module.compHom (R := ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V').obj.obj
      (op (Over.mk cW : Over V')) : Type u)) _ fB0.symm.toRingHom
  let mAW0 : Module A ((M.over V').val.obj (op (Over.mk cW : Over V'))) :=
    Module.compHom _ (algebraMap A Bc)
  have twW0 : IsScalarTower A Bc ((M.over V').val.obj (op (Over.mk cW : Over V'))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hid0 : ∀ c : A,
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V').obj.map gh.op).hom (fA0.symm c) =
        fB0.symm (algebraMap A Bc c) := fun c => by
    rw [halg c]
    exact (fB0.symm_apply_apply _).symm
  let r0 : (M.over V').val.obj (op (Over.mk cT : Over V')) →ₗ[A]
      (M.over V').val.obj (op (Over.mk cW : Over V')) :=
    { toFun := fun n => (M.over V').val.map gh.op n
      map_add' := map_add ((M.over V').val.map gh.op).hom
      map_smul' := fun c n =>
        ((M.over V').val.map_smul gh.op (fA0.symm c) n).trans (by rw [hid0 c]; rfl) }
  have hbij0 : Function.Bijective (r0.liftBaseChange Bc) :=
    bijective_liftBaseChange_of_hasGlobalPresentation B S hS F hF (M.over V') hM gh hT hW A Bc fA0
      (fun c n => congrArg (· • n) (fA0.symm_apply_apply c))
      fB0 (fun c n => congrArg (· • n) (fB0.symm_apply_apply c))
      halg r0 (fun _ => rfl)
  exact bijective_liftBaseChange_of_addEquiv r r0 (AddEquiv.refl _) (AddEquiv.refl _)
    (smul_eq_symm_smul fA hfA) (smul_eq_symm_smul fB hfB) hr hbij0


/-- **The sections of a sheaf of modules on the small étale site over an object of a slice with
affine underlying scheme are the base change of its sections over another such object it maps
to**, given a global presentation of the module restricted to a chart both of them lie over.

This is
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation_chart` read
for the restriction of the module to the slice at an arbitrary chart `V`.  The sections of that
restriction at an object of the slice are the sections of the module at the underlying chart and
its restriction maps are those of the module, so the two statements are the same statement; they
are not the same *term*, because the module structure the restriction carries is restriction of
scalars along an identity, which instance search does not undo.  The identification is therefore
carried out once here, by `Module.BaseChange.bijective_liftBaseChange_of_comm` along the identity,
and the descent along a covering family of the slice uses this form throughout.

The restriction is taken as a module `N` together with an equation identifying it, rather than
written out: `SheafOfModules.over` is a `noncomputable` construction, and the module structures a
descent argument binds on its sections are reported as failing to compile for depending on it even
though they occur inside the proof of a proposition.  Naming the restriction keeps that
construction out of the types those structures are stated at. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation_overChart
    (M : SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)))
    {V V' : (smallEtaleRingedSite B S hS F hF).C} (hM : (M.over V').HasGlobalPresentation)
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)) (hN : N = M.over V)
    {T W : Over V} (cT : T.left ⟶ V') (cW : W.left ⟶ V') (h : W ⟶ T)
    (hcl : h.left ≫ cT = cW)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T.left)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left)))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (N.val.obj (op T))] [Module A (N.val.obj (op W))]
    [Module Bc (N.val.obj (op W))]
    [IsScalarTower A Bc (N.val.obj (op W))]
    (fA : ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
      (op T) : Type u) ≃+* A)
    (hfA : ∀ (c : ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op T) : Type u))
      (n : N.val.obj (op T)), fA c • n = c • n)
    (fB : ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
      (op W) : Type u) ≃+* Bc)
    (hfB : ∀ (c : ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op W) : Type u))
      (n : N.val.obj (op W)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB (((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.map h.op).hom
        (fA.symm c)))
    (r : N.val.obj (op T) →ₗ[A] N.val.obj (op W))
    (hr : ∀ n, r n = N.val.restrictₛₗ h.op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  subst hN
  let fA0 : (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj
    (op T.left) : Type u) ≃+* A := fA
  let fB0 : (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.obj
    (op W.left) : Type u) ≃+* Bc := fB
  let mAT0 : Module A (M.val.obj (op T.left)) :=
    Module.compHom (R := (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj
      (op T.left) : Type u)) _ fA0.symm.toRingHom
  let mBW0 : Module Bc (M.val.obj (op W.left)) :=
    Module.compHom (R := (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj
      (op W.left) : Type u)) _ fB0.symm.toRingHom
  let mAW0 : Module A (M.val.obj (op W.left)) := Module.compHom _ (algebraMap A Bc)
  have twW0 : IsScalarTower A Bc (M.val.obj (op W.left)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hid0 : ∀ c : A,
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.map h.left.op).hom (fA0.symm c) =
        fB0.symm (algebraMap A Bc c) := fun c => by
    rw [halg c]
    exact (fB0.symm_apply_apply _).symm
  let r0 : M.val.obj (op T.left) →ₗ[A] M.val.obj (op W.left) :=
    { toFun := fun n => M.val.map h.left.op n
      map_add' := map_add (M.val.map h.left.op).hom
      map_smul' := fun c n =>
        (M.val.map_smul h.left.op (fA0.symm c) n).trans (by rw [hid0 c]; rfl) }
  have hbij0 : Function.Bijective (r0.liftBaseChange Bc) :=
    bijective_liftBaseChange_of_hasGlobalPresentation_chart B S hS F hF M hM cT cW h.left hcl
      hT hW A Bc fA0
      (fun c n => congrArg (· • n) (fA0.symm_apply_apply c))
      fB0 (fun c n => congrArg (· • n) (fB0.symm_apply_apply c))
      halg r0 (fun _ => rfl)
  exact bijective_liftBaseChange_of_addEquiv r r0 (AddEquiv.refl _) (AddEquiv.refl _)
    (smul_eq_symm_smul fA hfA) (smul_eq_symm_smul fB hfB) hr hbij0

end BaseChange

end SmallEtale

end AlgebraicGeometry.Space

end
