module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineEssentialSurjectivityProof
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations

/-!
# The sections over an affine object are a base change of the sections over a member it lies over

The two base-change comparisons a family descent datum consumes are *member-wise*: the sections
over the double overlap of the `i`-th and the `j`-th member of a covering family are the base
change of the sections over the `j`-th member, and the sections over a triple overlap are the base
change of the sections over a double overlap.  Neither compares the sections over an overlap with
the sections over the object covered, so neither follows from a presentation of the module on the
site the covering lives in: what they need is a presentation on the slice at the *member*, which
is exactly what quasi-coherence supplies.

A global presentation on the slice at a member `V` is a presentation of the restricted module on
the *iterated* slice at `V`, while every statement about affine objects of a slice of an fppf site
is about a slice at an object of the fibred category.  The two sites are equivalent
(`CategoryTheory.Over.iteratedSliceEquiv`) and
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft` carries the presentation across;
on the slice at the underlying object the base change is then
`SheafOfModules.bijective_liftBaseChange_of_exact_sections`, whose four exactness conditions are
discharged with no open hypothesis by
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver` and
`AlgebraicGeometry.FibredSite.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`.

Reading the result back is not an identity.  The object of the ambient slice which
`CategoryTheory.Over.iteratedSliceBackward` produces from `CategoryTheory.Over.mk a.left` is
`CategoryTheory.Over.mk (a.left ≫ V.hom)` and not the source of `a`, the two being equal only by
`CategoryTheory.Over.w a`, a proof field.  They are isomorphic by an isomorphism which is the
identity on underlying objects, and bijectivity of a base change is transported along a pair of
such identifications by `Module.BaseChange.bijective_liftBaseChange_of_comm`.

## Main results

* `Module.BaseChange.bijective_liftBaseChange_of_comm`: **bijectivity of a base change is carried
  by a commuting square of linear equivalences**, the one on the source linear over the base ring
  and the one on the target over the ring base changed to.
* `Module.linearEquivOfRingEquivComp`: an additive identification which is semilinear along a ring
  identification is linear over a ring identified with both of them.
* `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv`: **the sections of the iterated-slice
  reading of a module at a canonical object are the sections of the module itself**, together with
  `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv_smul` and
  `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv_restrictₛₗ` for its compatibility with
  the action of the sections of the structure sheaf and with restriction.
* `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation`: **the sections
  of a globally presented sheaf of modules over an affine object of a slice of the associated fppf
  site are the base change of its sections over another affine object**, with no hypothesis beyond
  the presentation.
* `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over`: **the
  sections over an affine object lying over a member of a covering family are the base change of
  the sections over an affine object it maps to over that member**, from a global presentation on
  the iterated slice at the member.  This is the hypothesis `hbij₃` of
  `SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange`.
* `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_self`: the same
  with the member itself as the base, which is the hypothesis `hbij₂` of that statement.

## Implementation notes

The commutative rings acting on the modules of sections are taken as explicit data together with
ring identifications with the rings of sections of the structure sheaf, as in
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs`: the sections of a sheaf of modules
over a `Sheaf J RingCat` carry a ring and nothing more, while a base change needs a commutative
ring, and a caller already holds the module structures its own consumers are stated for.

Each identification of the sections of the iterated-slice reading with the sections of the module
is isolated in its own declaration, over an arbitrary sheaf of rings.  Both spellings denote the
same module, but unfolding the restriction along the equivalence of the two sites is expensive
once the sheaf of rings is the structure sheaf of a slice of an associated fppf site, and the
statements which use the identification are elaborated against the spelling they are stated in
rather than against the other one.

No instance is created.  Every ring acting on a module of sections is either an instance argument
of the statement or a local definition built by `Module.compHom` along the given ring
identification, and the scalar towers are `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Module.BaseChange

/-- **Bijectivity of a base change is carried by a commuting square of linear equivalences.**

Let `r : MT →ₗ[A] MW` and `r' : MT' →ₗ[A] MW'` be intertwined by an `A`-linear identification of
the two sources and a `Bc`-linear identification of the two targets.  Then the base change of `r`
along `A → Bc` is bijective as soon as the base change of `r'` is.

The identification of the targets is asked to be `Bc`-linear and not merely `A`-linear because the
base change is a map of `Bc`-modules; the one of the sources is `A`-linear, which is all that is
needed to base change it. -/
theorem bijective_liftBaseChange_of_comm
    {A Bc : Type*} [CommRing A] [CommRing Bc] [Algebra A Bc]
    {MT MT' MW MW' : Type*}
    [AddCommGroup MT] [Module A MT] [AddCommGroup MT'] [Module A MT']
    [AddCommGroup MW] [Module A MW] [Module Bc MW] [IsScalarTower A Bc MW]
    [AddCommGroup MW'] [Module A MW'] [Module Bc MW'] [IsScalarTower A Bc MW']
    (r : MT →ₗ[A] MW) (r' : MT' →ₗ[A] MW')
    (δ : MT ≃ₗ[A] MT') (ε : MW ≃ₗ[Bc] MW')
    (hcomm : ∀ n, ε (r n) = r' (δ n))
    (hbij : Function.Bijective (r'.liftBaseChange Bc)) :
    Function.Bijective (r.liftBaseChange Bc) := by
  set d : Bc ⊗[A] MT ≃ₗ[Bc] Bc ⊗[A] MT' := LinearEquiv.baseChange A Bc MT MT' δ with hd
  have key : ∀ z, ε (r.liftBaseChange Bc z) = r'.liftBaseChange Bc (d z) := by
    intro z
    induction z with
    | zero => simp
    | tmul b n =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, hcomm, hd]
      simp [LinearMap.liftBaseChange_tmul]
    | add z z' hz hz' => simp only [map_add, hz, hz']
  refine ⟨fun z z' hzz' => d.injective (hbij.1 ?_), fun m => ?_⟩
  · rw [← key, ← key, hzz']
  · obtain ⟨y, hy⟩ := hbij.2 (ε m)
    refine ⟨d.symm y, ε.injective ?_⟩
    rw [key, d.apply_symm_apply, hy]

end Module.BaseChange

namespace Module

/-- **An additive identification which is semilinear along a ring identification is linear over a
ring identified with both of them.**

Let `X` be a module over `R₁` and `Y` a module over `R₂`, let `e₀` be an additive identification
carrying the action of `c` to the action of `ρ c`, and let a commutative ring `A` act on both
through ring identifications `fA` and `fA'` compatible with `ρ`.  Then `e₀` is `A`-linear. -/
noncomputable def linearEquivOfRingEquivComp {R₁ R₂ : Type*} [Ring R₁] [Ring R₂]
    {X Y : Type*} [AddCommGroup X] [Module R₁ X] [AddCommGroup Y] [Module R₂ Y]
    (ρ : R₁ ≃+* R₂) (e₀ : X ≃+ Y) (he : ∀ (c : R₁) (n : X), e₀ (c • n) = ρ c • e₀ n)
    (A : Type*) [CommRing A] [Module A X] [Module A Y]
    (fA : R₁ ≃+* A) (hfA : ∀ (c : R₁) (n : X), fA c • n = c • n)
    (fA' : R₂ ≃+* A) (hfA' : ∀ (c : R₂) (n : Y), fA' c • n = c • n)
    (hρ : ∀ c : R₁, fA' (ρ c) = fA c) : X ≃ₗ[A] Y :=
  { e₀ with
    map_smul' := fun c n => by
      have h1 : (c • n : X) = fA.symm c • n := by rw [← hfA (fA.symm c) n, fA.apply_symm_apply]
      have h2 : ∀ y : Y, (c • y : Y) = fA'.symm c • y := fun y => by
        rw [← hfA' (fA'.symm c) y, fA'.apply_symm_apply]
      have h3 : ρ (fA.symm c) = fA'.symm c :=
        fA'.injective (by rw [hρ, fA.apply_symm_apply, fA'.apply_symm_apply])
      change e₀ (c • n) = c • e₀ n
      rw [h1, he, h3, h2] }

/-- `Module.linearEquivOfRingEquivComp` is the given additive identification; the equation is
definitional and is stated so that a consumer may rewrite with it. -/
lemma linearEquivOfRingEquivComp_apply {R₁ R₂ : Type*} [Ring R₁] [Ring R₂]
    {X Y : Type*} [AddCommGroup X] [Module R₁ X] [AddCommGroup Y] [Module R₂ Y]
    (ρ : R₁ ≃+* R₂) (e₀ : X ≃+ Y) (he : ∀ (c : R₁) (n : X), e₀ (c • n) = ρ c • e₀ n)
    (A : Type*) [CommRing A] [Module A X] [Module A Y]
    (fA : R₁ ≃+* A) (hfA : ∀ (c : R₁) (n : X), fA c • n = c • n)
    (fA' : R₂ ≃+* A) (hfA' : ∀ (c : R₂) (n : Y), fA' c • n = c • n)
    (hρ : ∀ c : R₁, fA' (ρ c) = fA c) (n : X) :
    linearEquivOfRingEquivComp ρ e₀ he A fA hfA fA' hfA' hρ n = e₀ n := rfl

end Module

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The ring of sections of the structure sheaf of a slice at an object, identified with the one
of the slice at the ambient object at the corresponding canonical object.**  The sections of a
restricted sheaf at an object of a slice are its sections at the underlying object and the two
canonical objects have the same underlying object, so the two rings are the same ring and the
identification is the identity. -/
def iteratedSliceLeftRingEquiv (R : Sheaf J RingCat.{w}) {x : C} (V : Over x) {TL : C}
    (ct : TL ⟶ V.left) :
    (((R.over x).obj.obj (op (Over.mk (ct ≫ V.hom) : Over x))) : Type w) ≃+*
      (((R.over V.left).obj.obj (op (Over.mk ct))) : Type w) :=
  RingEquiv.refl _

/-- **The sections of the iterated-slice reading of a module at a canonical object are the
sections of the module at the corresponding canonical object of the ambient slice.**

The object which `CategoryTheory.Over.iteratedSliceBackward` produces from
`CategoryTheory.Over.mk ct` has underlying object `CategoryTheory.Over.mk (ct ≫ V.hom)`, so the
two modules of sections are the same module and the identification is the identity.  It is named
because the module structures the two spellings carry are not literally the same term, and a
consumer transporting a statement from one to the other needs a map it can rewrite along. -/
def iteratedSliceLeftSectionAddEquiv (R : Sheaf J RingCat.{w}) {x : C} (V : Over x)
    (N : _root_.SheafOfModules.{m} (R.over x)) {TL : C} (ct : TL ⟶ V.left) :
    N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x)) ≃+
      (iteratedSliceLeft R x V (N.over V)).val.obj (op (Over.mk ct)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv` carries the action of a section of
the structure sheaf to the action of its image under
`Stacks.SheafOfModules.iteratedSliceLeftRingEquiv`; a definitional identity. -/
lemma iteratedSliceLeftSectionAddEquiv_smul (R : Sheaf J RingCat.{w}) {x : C} (V : Over x)
    (N : _root_.SheafOfModules.{m} (R.over x)) {TL : C} (ct : TL ⟶ V.left)
    (c : (((R.over x).obj.obj (op (Over.mk (ct ≫ V.hom) : Over x))) : Type w))
    (n : N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x))) :
    iteratedSliceLeftSectionAddEquiv R V N ct (c • n) =
      iteratedSliceLeftRingEquiv R V ct c • iteratedSliceLeftSectionAddEquiv R V N ct n := rfl

/-- `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv` intertwines restriction along a
morphism of the slice at the underlying object with restriction along the induced morphism of the
canonical objects of the ambient slice; a definitional identity. -/
lemma iteratedSliceLeftSectionAddEquiv_restrictₛₗ (R : Sheaf J RingCat.{w}) {x : C} (V : Over x)
    (N : _root_.SheafOfModules.{m} (R.over x)) {TL WL : C} (ct : TL ⟶ V.left) (cw : WL ⟶ V.left)
    (h' : (Over.mk cw : Over V.left) ⟶ Over.mk ct)
    (n : N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x))) :
    iteratedSliceLeftSectionAddEquiv R V N cw
        (N.val.restrictₛₗ (Over.homMk h'.left (by
          change h'.left ≫ ct ≫ V.hom = cw ≫ V.hom
          rw [← Category.assoc, show h'.left ≫ ct = cw from Over.w h']) :
            (Over.mk (cw ≫ V.hom) : Over x) ⟶ Over.mk (ct ≫ V.hom)).op n) =
      (iteratedSliceLeft R x V (N.over V)).val.restrictₛₗ h'.op
        (iteratedSliceLeftSectionAddEquiv R V N ct n) := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.FibredSite

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

/-- A module over a ring identified with `R` acts as `R` does, through the identification. -/
private theorem smul_eq_symm_smul {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module R M]
    [Module A M] (f : R ≃+* A) (hf : ∀ (c : R) (n : M), f c • n = c • n) (c : A) (n : M) :
    c • n = f.symm c • n := by
  rw [← hf (f.symm c) n, f.apply_symm_apply]

/-- If `algebraMap A Bc` is `σ` read through identifications, `σ` carries `fA.symm c` to
`fB.symm (algebraMap A Bc c)`. -/
private theorem map_symm_eq_symm_algebraMap {R₁ R₂ A Bc : Type*} [Ring R₁] [Ring R₂] [CommRing A]
    [CommRing Bc] [Algebra A Bc] (σ : R₁ →+* R₂) (fA : R₁ ≃+* A) (fB : R₂ ≃+* Bc)
    (halg : ∀ c : A, algebraMap A Bc c = fB (σ (fA.symm c))) (c : A) :
    σ (fA.symm c) = fB.symm (algebraMap A Bc c) := by
  rw [halg c, fB.symm_apply_apply]

/-- A semilinear map is linear over a ring `A` acting through `s` at the source and through `g` at
the target, when `s` and `g` are intertwined by the ring map. -/
private def linearMapOfSemilinear {R₁ R₂ A M₂ M : Type*} [Semiring R₁] [Semiring R₂] [CommRing A]
    [AddCommGroup M] [AddCommGroup M₂] [Module R₁ M] [Module R₂ M₂] [Module A M] [Module A M₂]
    {σ : R₁ →+* R₂} (φ : M →ₛₗ[σ] M₂) (s : A → R₁) (g : A → R₂) (hσ : ∀ c, σ (s c) = g c)
    (hs : ∀ (c : A) (n : M), c • n = s c • n := by intros; rfl)
    (hg : ∀ (c : A) (n : M₂), c • n = g c • n := by intros; rfl) : M →ₗ[A] M₂ where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c n := by rw [hs, hg, φ.map_smulₛₗ, hσ]; rfl

/-- The module structure pulled back along the inverse of `f` makes `f` act as the identity. -/
private theorem apply_smul_compHom {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M]
    [Module R M] (f : R ≃+* A) (c : R) (n : M) :
    letI := Module.compHom M f.symm.toRingHom
    f c • n = c • n :=
  congrArg (· • n) (f.symm_apply_apply c)

include hp in
/-- **The sections of a globally presented sheaf of modules over an affine object of a slice of
the associated fppf site are the base change of its sections over another affine object.**

Let `M` be a sheaf of modules on the slice at an object `x` with a global presentation, and let
`h : W ⟶ T` be a morphism between two affine objects of that slice.  Then the comparison from the
base change of the sections over `T` to the sections over `W` is bijective.

This is `SheafOfModules.bijective_liftBaseChange_of_exact_sections` with every hypothesis
discharged.  The four bases are
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs`, the presenting morphism is
surjective on the sections over either object by
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver`, and a section it
kills over `W` is a value of the presenting map by
`AlgebraicGeometry.FibredSite.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`;
neither has an open hypothesis.  Nothing is assumed of the object the slice is taken at, in
particular not that it is affine: the two objects compared are affine and that is all the sheaf
condition for the presheaf cokernel needs.

A global presentation presents the universe lift of the module, whose sections are the sections of
the module lifted, so the conclusion for the module itself is the conclusion for the lift
transported along that identification by
`Module.BaseChange.bijective_liftBaseChange_of_comm`. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation)
    {T W : Over x} (h : W ⟶ T)
    (hT : IsAffineOver B S hS (p.obj T.left)) (hW : IsAffineOver B S hS (p.obj W.left))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (M.val.obj (op T))] [Module A (M.val.obj (op W))] [Module Bc (M.val.obj (op W))]
    [IsScalarTower A Bc (M.val.obj (op W))]
    (fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u) ≃+* A)
    (hfA : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u))
      (n : M.val.obj (op T)), fA c • n = c • n)
    (fB : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u) ≃+* Bc)
    (hfB : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : M.val.obj (op W)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB ((((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map h.op).hom (fA.symm c)))
    (r : M.val.obj (op T) →ₗ[A] M.val.obj (op W))
    (hr : ∀ n, r n = M.val.restrictₛₗ h.op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hM
  have _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      AddCommGrpCat.{max v w u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max v w u, w, max v w} _
  have _ : ((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max v w u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max v w u, max v w, w} _
  have _ : Epi b := Cofork.IsColimit.epi hcok
  have hzero : ∀ {Y Z : SheafOfModules.{max v w u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)}, (0 : Y ⟶ Z).val = 0 := rfl
  have hab' : a.val ≫ b.val = 0 := by rw [← SheafOfModules.comp_val, hab, hzero]
  -- the `A`-module structures at `T`
  let mQT : Module A (Q.val.obj (op T)) := Module.compHom _ fA.symm.toRingHom
  let mPT : Module A (P.val.obj (op T)) := Module.compHom _ fA.symm.toRingHom
  let mNT : Module A
      ((SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M).val.obj (op T)) :=
    Module.compHom _ fA.symm.toRingHom
  -- the `Bc`-module structures at `W`
  let mQWB : Module Bc (Q.val.obj (op W)) := Module.compHom _ fB.symm.toRingHom
  let mPWB : Module Bc (P.val.obj (op W)) := Module.compHom _ fB.symm.toRingHom
  let mNWB : Module Bc
      ((SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M).val.obj (op W)) :=
    Module.compHom _ fB.symm.toRingHom
  let mQWA : Module A (Q.val.obj (op W)) := Module.compHom _ (algebraMap A Bc)
  let mPWA : Module A (P.val.obj (op W)) := Module.compHom _ (algebraMap A Bc)
  let mNWA : Module A
      ((SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M).val.obj (op W)) :=
    Module.compHom _ (algebraMap A Bc)
  have twQ : IsScalarTower A Bc (Q.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP : IsScalarTower A Bc (P.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : IsScalarTower A Bc
      ((SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M).val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let NU := SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M
  have hfQT : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u))
      (n : Q.val.obj (op T)), fA c • n = c • n := fun c n =>
    apply_smul_compHom fA c n
  have hfPT : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u))
      (n : P.val.obj (op T)), fA c • n = c • n := fun c n =>
    apply_smul_compHom fA c n
  have hfQW : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : Q.val.obj (op W)), fB c • n = c • n := fun c n =>
    apply_smul_compHom fB c n
  have hfPW : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : P.val.obj (op W)), fB c • n = c • n := fun c n =>
    apply_smul_compHom fB c n
  have hid := map_symm_eq_symm_algebraMap _ fA fB halg
  let rQ : Q.val.obj (op T) →ₗ[A] Q.val.obj (op W) :=
    linearMapOfSemilinear (Q.val.restrictₛₗ h.op) fA.symm _ hid
  let rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W) :=
    linearMapOfSemilinear (P.val.restrictₛₗ h.op) fA.symm _ hid
  let rNU : NU.val.obj (op T) →ₗ[A] NU.val.obj (op W) :=
    linearMapOfSemilinear (NU.val.restrictₛₗ h.op) fA.symm _ hid
  let aT : Q.val.obj (op T) →ₗ[A] P.val.obj (op T) :=
    linearMapOfSemilinear (a.val.app (op T)).hom fA.symm _ fun _ => rfl
  let bT : P.val.obj (op T) →ₗ[A] NU.val.obj (op T) :=
    linearMapOfSemilinear (b.val.app (op T)).hom fA.symm _ fun _ => rfl
  let aW : Q.val.obj (op W) →ₗ[Bc] P.val.obj (op W) :=
    linearMapOfSemilinear (a.val.app (op W)).hom fB.symm _ fun _ => rfl
  let bW : P.val.obj (op W) →ₗ[Bc] NU.val.obj (op W) :=
    linearMapOfSemilinear (b.val.app (op W)).hom fB.symm _ fun _ => rfl
  have hbijU : Function.Bijective (rNU.liftBaseChange Bc) :=
    SheafOfModules.bijective_liftBaseChange_of_exact_sections κ ι h A Bc
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ T hT fA hfQT)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ W hW fB hfQW)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP T hT fA hfPT)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW fB hfPW)
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ T hT fA hfQT k)
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ W hW fB hfQW k)
      (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP T hT fA hfPT i)
      (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP W hW fB hfPW i)
      rQ (fun _ => rfl) rP (fun _ => rfl) rNU (fun _ => rfl) a b aT (fun _ => rfl) bT
      (fun _ => rfl) aW (fun _ => rfl) bW (fun _ => rfl)
      (fun q => by
        have hz := congr($(hab).val.app (op T) q)
        rwa [SheafOfModules.comp_val] at hz)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
        T hT)
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok
        W hW)
      (fun y hy => mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver B S hS p hp κ ι
        hQ hP a b hab hab' hcok W hW hy)
  exact Module.BaseChange.bijective_liftBaseChange_of_comm r rNU
    { toFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := fun c n => by rw [smul_eq_symm_smul fA hfA c n]; rfl
      invFun := ULift.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    { toFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := fun c n => by rw [smul_eq_symm_smul fB hfB c n]; rfl
      invFun := ULift.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun n => congrArg ULift.up (hr n)) hbijU

include hp in
/-- **The base change of the sections at the canonical objects over a member of a covering
family.**  This is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation` applied to the
iterated-slice reading of the module restricted to `V`, read back at the two objects
`CategoryTheory.Over.mk (ct ≫ V.hom)` and `CategoryTheory.Over.mk (cw ≫ V.hom)` of the ambient
slice, which are the images of `CategoryTheory.Over.mk ct` and `CategoryTheory.Over.mk cw` under
`CategoryTheory.Over.iteratedSliceBackward`.

The presentation on the slice at `V.left` is
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft`, and the identifications of the
sections are `Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv` made linear by
`Module.linearEquivOfRingEquivComp`.  Only the objects of the canonical shape occur, so no
isomorphism of objects is involved; the general case is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over`. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation_mk
    {N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (V : Over x) (hN : (N.over V).HasGlobalPresentation)
    {TL WL : 𝒳} (ct : TL ⟶ V.left) (cw : WL ⟶ V.left) (hl : WL ⟶ TL) (hcl : hl ≫ ct = cw)
    (hT : IsAffineOver B S hS (p.obj TL)) (hW : IsAffineOver B S hS (p.obj WL))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x)))]
    [Module A (N.val.obj (op (Over.mk (cw ≫ V.hom) : Over x)))]
    [Module Bc (N.val.obj (op (Over.mk (cw ≫ V.hom) : Over x)))]
    [IsScalarTower A Bc (N.val.obj (op (Over.mk (cw ≫ V.hom) : Over x)))]
    (fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (ct ≫ V.hom) : Over x)) : Type u) ≃+* A)
    (hfA : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
        (op (Over.mk (ct ≫ V.hom) : Over x)) : Type u))
      (n : N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x))), fA c • n = c • n)
    (fB : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (cw ≫ V.hom) : Over x)) : Type u) ≃+* Bc)
    (hfB : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
        (op (Over.mk (cw ≫ V.hom) : Over x)) : Type u))
      (n : N.val.obj (op (Over.mk (cw ≫ V.hom) : Over x))), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB (((ringStructureSheafCore B S hS p hp .fppf).obj.map hl.op).hom (fA.symm c)))
    (r : N.val.obj (op (Over.mk (ct ≫ V.hom) : Over x)) →ₗ[A]
      N.val.obj (op (Over.mk (cw ≫ V.hom) : Over x)))
    (hr : ∀ n, r n = N.val.restrictₛₗ (Over.homMk hl (by
        change hl ≫ ct ≫ V.hom = cw ≫ V.hom
        rw [← Category.assoc, hcl]) :
      (Over.mk (cw ≫ V.hom) : Over x) ⟶ Over.mk (ct ≫ V.hom)).op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  let h' : (Over.mk cw : Over V.left) ⟶ Over.mk ct := Over.homMk hl hcl
  let fAU : (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
      (op (Over.mk ct)) : Type u) ≃+* A :=
    (Stacks.SheafOfModules.iteratedSliceLeftRingEquiv
      (ringStructureSheafCore B S hS p hp .fppf) V ct).symm.trans fA
  let fBU : (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
      (op (Over.mk cw)) : Type u) ≃+* Bc :=
    (Stacks.SheafOfModules.iteratedSliceLeftRingEquiv
      (ringStructureSheafCore B S hS p hp .fppf) V cw).symm.trans fB
  let mATU : Module A ((Stacks.SheafOfModules.iteratedSliceLeft
      (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk ct))) :=
    Module.compHom (R := (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
      (op (Over.mk ct)) : Type u)) _ fAU.symm.toRingHom
  let mBWU : Module Bc ((Stacks.SheafOfModules.iteratedSliceLeft
      (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk cw))) :=
    Module.compHom (R := (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
      (op (Over.mk cw)) : Type u)) _ fBU.symm.toRingHom
  let mAWU : Module A ((Stacks.SheafOfModules.iteratedSliceLeft
      (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk cw))) :=
    Module.compHom _ (algebraMap A Bc)
  have twWU : IsScalarTower A Bc ((Stacks.SheafOfModules.iteratedSliceLeft
      (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk cw))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfAU : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
        (op (Over.mk ct)) : Type u))
      (n : (Stacks.SheafOfModules.iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk ct))),
      fAU c • n = c • n := fun c n => apply_smul_compHom fAU c n
  have hfBU : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.obj
        (op (Over.mk cw)) : Type u))
      (n : (Stacks.SheafOfModules.iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk cw))),
      fBU c • n = c • n := fun c n => apply_smul_compHom fBU c n
  have halgU : ∀ c : A, algebraMap A Bc c =
      fBU ((((ringStructureSheafCore B S hS p hp .fppf).over V.left).obj.map h'.op).hom
        (fAU.symm c)) := halg
  let rU : (Stacks.SheafOfModules.iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk ct)) →ₗ[A]
      (Stacks.SheafOfModules.iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.obj (op (Over.mk cw)) :=
    linearMapOfSemilinear ((Stacks.SheafOfModules.iteratedSliceLeft
      (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V)).val.restrictₛₗ h'.op) fAU.symm _
        (map_symm_eq_symm_algebraMap _ fAU fBU halgU)
  have hbijU : Function.Bijective (rU.liftBaseChange Bc) :=
    bijective_liftBaseChange_of_hasGlobalPresentation B S hS p hp
      (Stacks.SheafOfModules.iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V))
      (Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V) hN)
      h' hT hW A Bc fAU hfAU fBU hfBU halgU rU (fun _ => rfl)
  exact Module.BaseChange.bijective_liftBaseChange_of_comm r rU
    (Module.linearEquivOfRingEquivComp
      (Stacks.SheafOfModules.iteratedSliceLeftRingEquiv
        (ringStructureSheafCore B S hS p hp .fppf) V ct)
      (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv
        (ringStructureSheafCore B S hS p hp .fppf) V N ct)
      (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv_smul
        (ringStructureSheafCore B S hS p hp .fppf) V N ct)
      A fA hfA fAU hfAU (fun _ => rfl))
    (Module.linearEquivOfRingEquivComp
      (Stacks.SheafOfModules.iteratedSliceLeftRingEquiv
        (ringStructureSheafCore B S hS p hp .fppf) V cw)
      (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv
        (ringStructureSheafCore B S hS p hp .fppf) V N cw)
      (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv_smul
        (ringStructureSheafCore B S hS p hp .fppf) V N cw)
      Bc fB hfB fBU hfBU (fun _ => rfl))
    (fun n => (congrArg (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv
        (ringStructureSheafCore B S hS p hp .fppf) V N cw) (hr n)).trans
      (Stacks.SheafOfModules.iteratedSliceLeftSectionAddEquiv_restrictₛₗ
        (ringStructureSheafCore B S hS p hp .fppf) V N ct cw h' n))
    hbijU

include hp in
/-- **The sections over an affine object lying over a member of a covering family are the base
change of the sections over an affine object it maps to over that member.**

Let `V` be an object on whose restriction the module has a global presentation, let `cT : T ⟶ V`
and `cW : W ⟶ V` with `T` and `W` affine, and let `h : W ⟶ T` be compatible with them.  Then the
sections over `W` are the base change of the sections over `T` along the induced map of the rings
of sections of the structure sheaf.

This is the hypothesis `hbij₃` of
`SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange`, at a triple overlap of a covering
family: there `V` is a member, `T` a double overlap mapping to it and `W` a triple overlap mapping
to `T`.

It is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_mk` read at `T`
and `W` instead of at the canonical objects `CategoryTheory.Over.mk (cT.left ≫ V.hom)` and
`CategoryTheory.Over.mk (cW.left ≫ V.hom)`.  The discrepancy is `CategoryTheory.Over.w`, a proof
field, so the objects are isomorphic by an isomorphism which is the identity on underlying objects;
restriction along it is bijective and linear, because the induced map of the rings of sections is
the identity, and `Module.BaseChange.bijective_liftBaseChange_of_comm` transports the
conclusion. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation_over
    {N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (V : Over x) (hN : (N.over V).HasGlobalPresentation)
    {T W : Over x} (cT : T ⟶ V) (cW : W ⟶ V) (h : W ⟶ T) (hc : h ≫ cT = cW)
    (hT : IsAffineOver B S hS (p.obj T.left)) (hW : IsAffineOver B S hS (p.obj W.left))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (N.val.obj (op T))] [Module A (N.val.obj (op W))] [Module Bc (N.val.obj (op W))]
    [IsScalarTower A Bc (N.val.obj (op W))]
    (fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u) ≃+* A)
    (hfA : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op T) : Type u))
      (n : N.val.obj (op T)), fA c • n = c • n)
    (fB : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u) ≃+* Bc)
    (hfB : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : N.val.obj (op W)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB ((((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map h.op).hom (fA.symm c)))
    (r : N.val.obj (op T) →ₗ[A] N.val.obj (op W))
    (hr : ∀ n, r n = N.val.restrictₛₗ h.op n) :
    Function.Bijective (r.liftBaseChange Bc) := by
  have hcl : h.left ≫ cT.left = cW.left := congrArg (fun f => f.left) hc
  let eT : (Over.mk (cT.left ≫ V.hom) : Over x) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  let eT' : T ⟶ (Over.mk (cT.left ≫ V.hom) : Over x) := Over.homMk (𝟙 T.left) (by simp)
  let eW : (Over.mk (cW.left ≫ V.hom) : Over x) ⟶ W := Over.homMk (𝟙 W.left) (by simp)
  let eW' : W ⟶ (Over.mk (cW.left ≫ V.hom) : Over x) := Over.homMk (𝟙 W.left) (by simp)
  let gh : (Over.mk (cW.left ≫ V.hom) : Over x) ⟶ (Over.mk (cT.left ≫ V.hom) : Over x) :=
    Over.homMk h.left (by
      show h.left ≫ cT.left ≫ V.hom = cW.left ≫ V.hom
      rw [← Category.assoc, hcl])
  have hTT : eT' ≫ eT = 𝟙 T := by ext; simp [eT, eT']
  have hTT' : eT ≫ eT' = 𝟙 (Over.mk (cT.left ≫ V.hom) : Over x) := by ext; simp [eT, eT']
  have hWW : eW' ≫ eW = 𝟙 W := by ext; simp [eW, eW']
  have hWW' : eW ≫ eW' = 𝟙 (Over.mk (cW.left ≫ V.hom) : Over x) := by ext; simp [eW, eW']
  have hsq : eW ≫ h = gh ≫ eT := by ext; simp [eW, eT, gh]
  have hringT : ∀ d : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (cT.left ≫ V.hom) : Over x)) : Type u),
      ((((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map eT.op)).hom d = d := fun d => by
    have h0 : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map eT.op) =
        (ringStructureSheafCore B S hS p hp .fppf).obj.map (𝟙 (op T.left)) := rfl
    rw [h0, CategoryTheory.Functor.map_id]
    rfl
  have hringW : ∀ d : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (cW.left ≫ V.hom) : Over x)) : Type u),
      ((((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map eW.op)).hom d = d := fun d => by
    have h0 : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map eW.op) =
        (ringStructureSheafCore B S hS p hp .fppf).obj.map (𝟙 (op W.left)) := rfl
    rw [h0, CategoryTheory.Functor.map_id]
    rfl
  let fA0 : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
    (op (Over.mk (cT.left ≫ V.hom) : Over x)) : Type u) ≃+* A := fA
  let fB0 : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
    (op (Over.mk (cW.left ≫ V.hom) : Over x)) : Type u) ≃+* Bc := fB
  let mAT0 : Module A (N.val.obj (op (Over.mk (cT.left ≫ V.hom) : Over x))) :=
    Module.compHom (R := (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (cT.left ≫ V.hom) : Over x)) : Type u)) _ fA0.symm.toRingHom
  let mBW0 : Module Bc (N.val.obj (op (Over.mk (cW.left ≫ V.hom) : Over x))) :=
    Module.compHom (R := (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (cW.left ≫ V.hom) : Over x)) : Type u)) _ fB0.symm.toRingHom
  let mAW0 : Module A (N.val.obj (op (Over.mk (cW.left ≫ V.hom) : Over x))) :=
    Module.compHom _ (algebraMap A Bc)
  have twW0 : IsScalarTower A Bc (N.val.obj (op (Over.mk (cW.left ≫ V.hom) : Over x))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let r0 : N.val.obj (op (Over.mk (cT.left ≫ V.hom) : Over x)) →ₗ[A]
      N.val.obj (op (Over.mk (cW.left ≫ V.hom) : Over x)) :=
    linearMapOfSemilinear (N.val.restrictₛₗ gh.op) fA0.symm _
      (map_symm_eq_symm_algebraMap _ fA0 fB0 halg)
  have hbij0 : Function.Bijective (r0.liftBaseChange Bc) :=
    bijective_liftBaseChange_of_hasGlobalPresentation_mk B S hS p hp V hN cT.left cW.left h.left
      hcl hT hW A Bc fA0
      (apply_smul_compHom fA0)
      fB0
      (apply_smul_compHom fB0)
      halg r0 (fun _ => rfl)
  have hLT : ∀ n, N.val.restrictₛₗ eT'.op (N.val.restrictₛₗ eT.op n) = n := fun n => by
    rw [N.val.restrictₛₗ_restrictₛₗ_op, hTT]; simp
  have hRT : ∀ n, N.val.restrictₛₗ eT.op (N.val.restrictₛₗ eT'.op n) = n := fun n => by
    rw [N.val.restrictₛₗ_restrictₛₗ_op, hTT']; simp
  have hLW : ∀ n, N.val.restrictₛₗ eW'.op (N.val.restrictₛₗ eW.op n) = n := fun n => by
    rw [N.val.restrictₛₗ_restrictₛₗ_op, hWW]; simp
  have hRW : ∀ n, N.val.restrictₛₗ eW.op (N.val.restrictₛₗ eW'.op n) = n := fun n => by
    rw [N.val.restrictₛₗ_restrictₛₗ_op, hWW']; simp
  refine Module.BaseChange.bijective_liftBaseChange_of_comm r r0
    { linearMapOfSemilinear (N.val.restrictₛₗ eT.op) fA.symm fA0.symm
        (fun c => hringT (fA.symm c)) (smul_eq_symm_smul fA hfA)
      with
      invFun := fun n => N.val.restrictₛₗ eT'.op n
      left_inv := hLT
      right_inv := hRT }
    { linearMapOfSemilinear (N.val.restrictₛₗ eW.op) fB.symm fB0.symm
        (fun c => hringW (fB.symm c)) (smul_eq_symm_smul fB hfB)
      with
      invFun := fun n => N.val.restrictₛₗ eW'.op n
      left_inv := hLW
      right_inv := hRW }
    (fun n => ?_) hbij0
  show N.val.restrictₛₗ eW.op (r n) = N.val.restrictₛₗ gh.op (N.val.restrictₛₗ eT.op n)
  rw [hr n, N.val.restrictₛₗ_restrictₛₗ_op, N.val.restrictₛₗ_restrictₛₗ_op, hsq]

include hp in
/-- **The sections over an affine object lying over a member of a covering family are the base
change of the sections over that member.**  This is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over` with the
member itself as the base, and it is the hypothesis `hbij₂` of
`SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange`: there `V` is the `j`-th member of
the family and `W` the double overlap of the `i`-th and the `j`-th, mapping to it by the second
projection. -/
theorem bijective_liftBaseChange_of_hasGlobalPresentation_self
    {N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (V : Over x) (hN : (N.over V).HasGlobalPresentation)
    {W : Over x} (a : W ⟶ V)
    (hV : IsAffineOver B S hS (p.obj V.left)) (hW : IsAffineOver B S hS (p.obj W.left))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (N.val.obj (op V))] [Module A (N.val.obj (op W))] [Module Bc (N.val.obj (op W))]
    [IsScalarTower A Bc (N.val.obj (op W))]
    (fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op V) : Type u) ≃+* A)
    (hfA : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op V) : Type u))
      (n : N.val.obj (op V)), fA c • n = c • n)
    (fB : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u) ≃+* Bc)
    (hfB : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : N.val.obj (op W)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB ((((ringStructureSheafCore B S hS p hp .fppf).over x).obj.map a.op).hom (fA.symm c)))
    (r : N.val.obj (op V) →ₗ[A] N.val.obj (op W))
    (hr : ∀ n, r n = N.val.restrictₛₗ a.op n) :
    Function.Bijective (r.liftBaseChange Bc) :=
  bijective_liftBaseChange_of_hasGlobalPresentation_over B S hS p hp V hN (𝟙 V) a a
    (Category.comp_id a) hV hW A Bc fA hfA fB hfB halg r hr

end AlgebraicGeometry.FibredSite
