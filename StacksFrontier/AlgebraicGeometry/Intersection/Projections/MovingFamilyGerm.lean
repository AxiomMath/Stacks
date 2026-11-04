module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyGraph
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism

/-!
# The graph of the family of projective transformations at a triple of closed points

Let `t` be a point of `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` whose three projections are the closed points cut
out by nonzero functionals `f_x`, `μ` and `f_y`. This file computes the germ at `t` of the minor
section of `𝒪(1,1,1)` and concludes that `t` lies on the graph of the family of projective
transformations exactly when all the `2 × 2` determinants

`f_y(u) · f_x(g v) - f_y(v) · f_x(g u)`

vanish, `g = lineEnd μ` being the tautological endomorphism the line coordinate names.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_propSection_iff`: the minor
  section attached to a pair of vectors is nonvanishing at such a point exactly when the
  corresponding determinant is nonzero.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingGraph_iff_of_linearFunctionalPoint`: such a
  point lies on the graph exactly when every determinant vanishes.

## Implementation notes

The computation is a germ computation in the invertible module `𝒪(1,1,1)`: the nonvanishing locus
of a global section is by definition the set of points whose germ escapes `𝔪ₓ · 𝒪(1,1,1)ₓ`, so the
whole argument happens in the stalk at `t` modulo that submodule, where the stalk is free of rank
one. Three ingredients carry it.

First, the tensor `prSource^*(ι a) ⊗ prLine^*(ι b) ⊗ prTarget^*(ι c)` is additive and
`k`-homogeneous in each of `a`, `b` and `c`. Additivity and homogeneity of a tautological section
come from the degree-`n` section map of a graded ring being `𝒮₀`-linear, and they survive the
pullback and the two tensor products because the comparison map into the sheafified tensor product
is a module morphism and `⊗ₜ` is bilinear.

The scalar produced by homogeneity is where care is needed. In each of the three slots it is a
global function on the triple product, and the three slots a priori produce three different
functions — the pullbacks along the three projections of the constant `r` on the three factors.
They have to be identified, because contracting the sum over the basis of the corank-two quotient
moves a scalar from the line slot into the source slot. The identification is that the constant
`r` on `𝐏(M)` is the pullback of `r` along the structure morphism `𝐏(M) ⟶ Spec k`, which reduces
the three functions to the single pullback of `r` along the structure morphism of the triple
product, the three projections being morphisms over `Spec k`.

Second, by the nonvanishing criterion for a tensor of three tautological sections, the germ of the
tensor at `t` escapes `𝔪ₓ · 𝒪(1,1,1)ₓ` exactly when none of `f_x(a)`, `μ(b)`, `f_y(c)` vanishes.
Splitting `a` as a vector killed by `f_x` plus a multiple of a fixed `a₀` with `f_x(a₀) ≠ 0`, and
likewise in the other two slots, therefore writes the germ of the tensor at `(a, b, c)` as the
scalar `f_x(a)μ(b)f_y(c) / f_x(a₀)μ(b₀)f_y(c₀)` times the germ at `(a₀, b₀, c₀)`, modulo
`𝔪ₓ · 𝒪(1,1,1)ₓ`.

Third, the minor section is a signed sum of four such tensors, so its germ is that same reference
germ times the determinant divided by `f_x(a₀)μ(b₀)f_y(c₀)`. A nonzero element of `k` has unit
image in the local ring, so the determinant is nonzero exactly when the germ escapes
`𝔪ₓ · 𝒪(1,1,1)ₓ`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u w

/-! ### Constants on a scheme over `Spec k` -/

section Constants

variable (k : Type u) [Field k]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The constant function `r` on a scheme over `Spec k`**: the image of `r` under the map on
global functions induced by a structure morphism to `Spec k`. It is spelled in the ring of
scalars of the sheaves of modules on the scheme, which is the spelling in which it can act on
them. -/
private def constTop {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) (r : k) :
    T.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom r

/-- **The germ at a point of the constant function `r`**, as a ring homomorphism from `k` to the
local ring there. -/
private def constGerm {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) (t : T) :
    k →+* ringStalk T.toRingedSpace t :=
  (ringGerm T.toRingedSpace t ⊤ (Opens.mem_top t)).comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom

/-- A nonzero constant has unit germ: a nonzero element of a field has unit image under any ring
homomorphism. -/
private theorem isUnit_constGerm {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) (t : T) {r : k}
    (hr : r ≠ 0) : IsUnit (constGerm k g t r) :=
  IsUnit.map (constGerm k g t) (isUnit_iff_ne_zero.mpr hr)

/-- The germ of the constant function `r` is the value at `r` of the germ homomorphism. -/
private theorem ringGerm_constTop {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) (t : T) (r : k) :
    ringGerm T.toRingedSpace t ⊤ (Opens.mem_top t) (constTop k g r) = constGerm k g t r := rfl

/-- Constants are compatible with pullback: the pullback of the constant `r` along a morphism of
schemes over `Spec k` is the constant `r`. -/
private theorem appTop_constTop {T T' : Scheme.{u}} (g : T ⟶ T')
    (h : T' ⟶ Spec (.of k)) (r : k) :
    g.appTop.hom (constTop k h r) = constTop k (g ≫ h) r := rfl

end Constants

/-! ### Additivity and homogeneity of the degree-`n` section map -/

section Graded

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

omit [GradedRing 𝒮] in
/-- A homogeneous element of degree `n` lies in the degree-zero piece of the `n`-th shift of the
regular graded module. -/
private theorem mem_twistGrading_zero' {n : ℕ} {x : S} (hx : x ∈ 𝒮 n) :
    x ∈ twistGrading (S := S) 𝒮 (n : ℤ) 0 := by
  simp [twistGrading, integerGrading, homogeneousSubmodule, hx]

/-- **The degree-`n` section map is additive.** -/
private theorem degreeSection_add_of_gradedRing (n : ℕ) (a b : 𝒮 n) :
    degreeSection 𝒮 n (a + b) = degreeSection 𝒮 n a + degreeSection 𝒮 n b := by
  change degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨((a + b : 𝒮 n) : S), mem_twistGrading_zero' 𝒮 (a + b).2⟩ = _
  rw [show (⟨((a + b : 𝒮 n) : S), mem_twistGrading_zero' 𝒮 (a + b).2⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) =
      ⟨(a : S), mem_twistGrading_zero' 𝒮 a.2⟩ + ⟨(b : S), mem_twistGrading_zero' 𝒮 b.2⟩ from rfl]
  exact map_add (degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))) _ _

/-- **The degree-`n` section map is homogeneous for the degree-zero part.** Multiplying a
homogeneous element of degree `n` by a degree-zero element multiplies its section by the global
function that degree-zero element names. -/
private theorem degreeSection_mul_zero (n : ℕ) (z : 𝒮 0) (a b : 𝒮 n)
    (hb : (b : S) = (z : S) * (a : S)) :
    degreeSection 𝒮 n b = degreeZeroRingToGlobalSections 𝒮 z • degreeSection 𝒮 n a := by
  let : Module ↥(𝒮 0) (twistGlobalSections 𝒮 n) :=
    Module.compHom _ (degreeZeroRingToGlobalSections 𝒮)
  have key : (⟨(b : S), mem_twistGrading_zero' 𝒮 b.2⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) = z • ⟨(a : S), mem_twistGrading_zero' 𝒮 a.2⟩ := by
    refine Subtype.ext ?_
    change (b : S) = (z : S) • (a : S)
    rw [hb, smul_eq_mul]
  change degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨(b : S), mem_twistGrading_zero' 𝒮 b.2⟩ = _
  rw [key]
  exact LinearMap.map_smul (degreeZeroToGlobalSections 𝒮
    (twistGrading (S := S) 𝒮 (n : ℤ))) z ⟨(a : S), mem_twistGrading_zero' 𝒮 a.2⟩

/-- The value at a point of the global function named by a degree-zero element is the fraction
`z / 1`. -/
private theorem degreeZeroRingToGlobalSections_val (z : 𝒮 0) (x : ProjectiveSpectrum.top 𝒮) :
    HomogeneousLocalization.val ((degreeZeroRingToGlobalSections 𝒮 z).1 ⟨x, trivial⟩) =
      algebraMap S (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (z : S) := by
  rw [← Proj.stalkIso'_germ 𝒮 ⊤ x trivial (degreeZeroRingToGlobalSections 𝒮 z),
    degreeZeroRingToGlobalSections_stalk]
  change Localization.mk z.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = _
  exact Localization.mk_algebraMap (A := S) z.1

/-- **The global function named by a degree-zero element is the pullback of that element along the
structure morphism `Proj 𝒮 ⟶ Spec 𝒮₀`.** Both have value `z / 1` at every point. -/
private theorem degreeZeroRingToGlobalSections_eq_toSpecZero (z : 𝒮 0) :
    degreeZeroRingToGlobalSections 𝒮 z =
      (Proj.toSpecZero 𝒮).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒮 0))).inv.hom z) := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  rw [degreeZeroRingToGlobalSections_val 𝒮 z x.1]
  exact (Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val 𝒮 z x.1).symm

end Graded

/-! ### The tautological section is additive and `k`-homogeneous -/

section Tautological

variable (k M : Type u) [Field k] [AddCommGroup M] [Module k M]

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The constants on `𝐏(M)` are the global functions named by the degree-zero part of the
symmetric algebra.** -/
private theorem constTop_projectiveSpaceOfModuleToSpec (r : k) :
    constTop k (projectiveSpaceOfModuleToSpec k M) r =
      degreeZeroRingToGlobalSections (symmetricGrading k M)
        (algebraMap k (symmetricGrading k M 0) r) := by
  rw [degreeZeroRingToGlobalSections_eq_toSpecZero]
  have e : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (projectiveSpaceOfModuleToSpec k M).appTop) =
      (CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k M))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (symmetricGrading k M 0))).inv ≫
          (Proj.toSpecZero (symmetricGrading k M)).appTop := by
    rw [show (projectiveSpaceOfModuleToSpec k M).appTop =
        (Spec.map (CommRingCat.ofHom
            (algebraMap k (SymPow.symmetricPower 0 k M)))).appTop ≫
          (Proj.toSpecZero (symmetricGrading k M)).appTop from rfl,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp e) r

/-- The global value over `⊤` of the tautological section attached to a vector is the degree-one
section named by that vector. -/
private theorem tautologicalSection_evalOp_top (v : M) :
    (tautologicalSection k M v).eval (op ⊤) =
      degreeSection (symmetricGrading k M) 1
        ⟨SymmetricAlgebra.ι k M v, ι_mem_symmetricPower_one k M v⟩ :=
  Stacks.SheafOfModules.sectionsOfTop_eval_top _ _

/-- **The tautological section is additive in its vector**, over `⊤`. -/
private theorem tautologicalSection_evalOp_top_add (v w : M) :
    (tautologicalSection k M (v + w)).eval (op ⊤) =
      (tautologicalSection k M v).eval (op ⊤) + (tautologicalSection k M w).eval (op ⊤) := by
  rw [tautologicalSection_evalOp_top, tautologicalSection_evalOp_top,
    tautologicalSection_evalOp_top,
    show (⟨SymmetricAlgebra.ι k M (v + w), ι_mem_symmetricPower_one k M (v + w)⟩ :
          symmetricGrading k M 1) =
        ⟨SymmetricAlgebra.ι k M v, ι_mem_symmetricPower_one k M v⟩ +
          ⟨SymmetricAlgebra.ι k M w, ι_mem_symmetricPower_one k M w⟩ from
      Subtype.ext (map_add (SymmetricAlgebra.ι k M) v w)]
  exact degreeSection_add_of_gradedRing (symmetricGrading k M) 1 _ _

/-- **The tautological section is `k`-homogeneous in its vector**, over `⊤`: scaling the vector
multiplies the section by the corresponding constant function. -/
private theorem tautologicalSection_evalOp_top_smul (r : k) (v : M) :
    (tautologicalSection k M (r • v)).eval (op ⊤) =
      constTop k (projectiveSpaceOfModuleToSpec k M) r •
        (tautologicalSection k M v).eval (op ⊤) := by
  rw [tautologicalSection_evalOp_top, tautologicalSection_evalOp_top,
    constTop_projectiveSpaceOfModuleToSpec]
  refine degreeSection_mul_zero (symmetricGrading k M) 1
    (algebraMap k (symmetricGrading k M 0) r) _ _ ?_
  change SymmetricAlgebra.ι k M (r • v) =
    ((algebraMap k (symmetricGrading k M 0) r : SymmetricAlgebra k M)) *
      SymmetricAlgebra.ι k M v
  rw [SetLike.GradeZero.coe_algebraMap, map_smul, Algebra.smul_def]

end Tautological

/-! ### Additivity and homogeneity of a pulled-back tautological section -/

section Pullback

variable (k M : Type u) [Field k] [AddCommGroup M] [Module k M]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The global value over `⊤` of a pulled-back tautological section is the image of the global
value of the section under the unit of the pullback adjunction. -/
private theorem pullbackTaut_eval_top {T : Scheme.{u}}
    (g : T ⟶ projectiveSpaceOfModule k M) (v : M) :
    (pullbackTaut k M g v).eval (op ⊤) =
      Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
        ((tautologicalSection k M v).eval (op ⊤)) :=
  Stacks.SheafOfModules.modulePullbackSection_eval_top _ _ _

/-- **A pulled-back tautological section is additive in its vector**, over `⊤`. -/
private theorem pullbackTaut_eval_top_add {T : Scheme.{u}}
    (g : T ⟶ projectiveSpaceOfModule k M) (v w : M) :
    (pullbackTaut k M g (v + w)).eval (op ⊤) =
      (pullbackTaut k M g v).eval (op ⊤) + (pullbackTaut k M g w).eval (op ⊤) := by
  rw [pullbackTaut_eval_top, pullbackTaut_eval_top, pullbackTaut_eval_top,
    tautologicalSection_evalOp_top_add]
  exact Stacks.RingedSpace.pullbackUnit_add _ _ _ _ _

/-- **A pulled-back tautological section is `k`-homogeneous in its vector**, over `⊤`: the scalar
is the constant function on the source attached to the composite structure morphism. -/
private theorem pullbackTaut_eval_top_smul {T : Scheme.{u}}
    (g : T ⟶ projectiveSpaceOfModule k M) (r : k) (v : M) :
    (pullbackTaut k M g (r • v)).eval (op ⊤) =
      constTop k (g ≫ projectiveSpaceOfModuleToSpec k M) r •
        (pullbackTaut k M g v).eval (op ⊤) := by
  rw [pullbackTaut_eval_top, pullbackTaut_eval_top, tautologicalSection_evalOp_top_smul]
  exact Stacks.RingedSpace.pullbackUnit_smul _ _ _ _ _

end Pullback

/-! ### Additivity and homogeneity of a tensor of two sections -/

section Tensor

variable {X : RingedSpace.{u, u}} (F G : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- A tensor of two global sections is additive over `U` in its left factor. -/
private theorem tensorSections_eval_add_left (s s₁ s₂ : F.sections) (t : G.sections)
    (U : (Opens X.carrier)ᵒᵖ) (h : s.eval U = s₁.eval U + s₂.eval U) :
    (tensorSections F G s t).eval U =
      (tensorSections F G s₁ t).eval U + (tensorSections F G s₂ t).eval U := by
  rw [tensorSections_eval, tensorSections_eval, tensorSections_eval, h,
    TensorProduct.add_tmul]
  exact map_add ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom _ _

/-- A tensor of two global sections is additive over `U` in its right factor. -/
private theorem tensorSections_eval_add_right (s : F.sections) (t t₁ t₂ : G.sections)
    (U : (Opens X.carrier)ᵒᵖ) (h : t.eval U = t₁.eval U + t₂.eval U) :
    (tensorSections F G s t).eval U =
      (tensorSections F G s t₁).eval U + (tensorSections F G s t₂).eval U := by
  rw [tensorSections_eval, tensorSections_eval, tensorSections_eval, h,
    TensorProduct.tmul_add]
  exact map_add ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom _ _

/-- A tensor of two global sections is homogeneous over `U` in its left factor. -/
private theorem tensorSections_eval_smul_left (s s₁ : F.sections) (t : G.sections)
    (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U)
    (h : s.eval U = r • s₁.eval U) :
    (tensorSections F G s t).eval U =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨X.presheaf, X.IsSheaf⟩).obj.obj U) _ _ r
        ((tensorSections F G s₁ t).eval U) := by
  rw [tensorSections_eval, tensorSections_eval, h]
  refine Eq.trans (congrArg (toTensorSheafSection X F G U)
    (TensorProduct.smul_tmul' r (s₁.eval U) (t.eval U))) ?_
  exact map_smul ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom r
    (s₁.eval U ⊗ₜ[X.presheaf.obj U] t.eval U)

/-- A tensor of two global sections is homogeneous over `U` in its right factor. -/
private theorem tensorSections_eval_smul_right (s : F.sections) (t t₁ : G.sections)
    (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U)
    (h : t.eval U = r • t₁.eval U) :
    (tensorSections F G s t).eval U =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨X.presheaf, X.IsSheaf⟩).obj.obj U) _ _ r
        ((tensorSections F G s t₁).eval U) := by
  rw [tensorSections_eval, tensorSections_eval, h]
  refine Eq.trans (congrArg (toTensorSheafSection X F G U)
    (TensorProduct.tmul_smul r (s.eval U) (t₁.eval U))) ?_
  exact map_smul ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom r
    (s.eval U ⊗ₜ[X.presheaf.obj U] t₁.eval U)

end Tensor

/-! ### Trilinearity of the tensor of three tautological sections -/

section Box

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The source projection is a morphism over `Spec k`. -/
theorem prSource_comp_toSpec :
    prSource k V L ≫ projectiveSpaceOfModuleToSpec k V = movingProdToSpec k V L :=
  pullback.condition

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The line projection is a morphism over `Spec k`. -/
theorem prLine_comp_toSpec :
    prLine k V L ≫ movingLineToSpec k V L = movingProdToSpec k V L := by
  rw [prLine, Category.assoc]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The target projection is a morphism over `Spec k`. -/
theorem prTarget_comp_toSpec :
    prTarget k V L ≫ projectiveSpaceOfModuleToSpec k V = movingProdToSpec k V L := by
  rw [prTarget, Category.assoc, ← pullback.condition]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is additive in its source vector.** -/
private theorem boxSection_eval_top_add_source (a a' : V) (b : lineSpace k V L) (c : V) :
    (boxSection k V L (a + a') b c).eval (op ⊤) =
      (boxSection k V L a b c).eval (op ⊤) + (boxSection k V L a' b c).eval (op ⊤) := by
  refine tensorSections_eval_add_left _ _ _ _ _ _ _ ?_
  exact tensorSections_eval_add_left _ _ _ _ _ _ _
    (pullbackTaut_eval_top_add k V (prSource k V L) a a')

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is additive in its line vector.** -/
private theorem boxSection_eval_top_add_line (a : V) (b b' : lineSpace k V L) (c : V) :
    (boxSection k V L a (b + b') c).eval (op ⊤) =
      (boxSection k V L a b c).eval (op ⊤) + (boxSection k V L a b' c).eval (op ⊤) := by
  refine tensorSections_eval_add_left _ _ _ _ _ _ _ ?_
  exact tensorSections_eval_add_right _ _ _ _ _ _ _
    (pullbackTaut_eval_top_add k (lineSpace k V L) (prLine k V L) b b')

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is additive in its target vector.** -/
private theorem boxSection_eval_top_add_target (a : V) (b : lineSpace k V L) (c c' : V) :
    (boxSection k V L a b (c + c')).eval (op ⊤) =
      (boxSection k V L a b c).eval (op ⊤) + (boxSection k V L a b c').eval (op ⊤) :=
  tensorSections_eval_add_right _ _ _ _ _ _ _
    (pullbackTaut_eval_top_add k V (prTarget k V L) c c')

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is `k`-homogeneous in its source vector**, the
scalar being the constant function on the triple product. -/
private theorem boxSection_eval_top_smul_source (r : k) (a : V) (b : lineSpace k V L) (c : V) :
    (boxSection k V L (r • a) b c).eval (op ⊤) =
      constTop k (movingProdToSpec k V L) r • (boxSection k V L a b c).eval (op ⊤) := by
  refine tensorSections_eval_smul_left _ _ _ _ _ _ _ ?_
  refine tensorSections_eval_smul_left _ _ _ _ _ _ _ ?_
  rw [pullbackTaut_eval_top_smul, prSource_comp_toSpec]
  rfl

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is `k`-homogeneous in its line vector**, the
scalar being the constant function on the triple product. -/
private theorem boxSection_eval_top_smul_line (r : k) (a : V) (b : lineSpace k V L) (c : V) :
    (boxSection k V L a (r • b) c).eval (op ⊤) =
      constTop k (movingProdToSpec k V L) r • (boxSection k V L a b c).eval (op ⊤) := by
  refine tensorSections_eval_smul_left _ _ _ _ _ _ _ ?_
  refine tensorSections_eval_smul_right _ _ _ _ _ _ _ ?_
  rw [pullbackTaut_eval_top_smul, prLine_comp_toSpec]
  rfl

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is `k`-homogeneous in its target vector**, the
scalar being the constant function on the triple product. -/
private theorem boxSection_eval_top_smul_target (r : k) (a : V) (b : lineSpace k V L) (c : V) :
    (boxSection k V L a b (r • c)).eval (op ⊤) =
      constTop k (movingProdToSpec k V L) r • (boxSection k V L a b c).eval (op ⊤) := by
  refine tensorSections_eval_smul_right _ _ _ _ _ _ _ ?_
  rw [pullbackTaut_eval_top_smul, prTarget_comp_toSpec]
  rfl

end Box

/-! ### The germ of the tensor of three tautological sections at a triple of closed points -/

section Germ

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- The triple product read as a ringed space. -/
private abbrev movingRS : RingedSpace.{u, u} := (movingProd k V L).toRingedSpace

/-- `𝒪(1,1,1)` retyped as a sheaf of modules over the structure sheaf of the triple product read
as a ringed space, which is the spelling whose stalks carry their module structure by instance
search. -/
private abbrev boxSh : _root_.SheafOfModules.{u} (structureSheafRing (movingRS k V L)) :=
  boxModule k V L

/-- **The germ at a point of the tensor of three tautological sections.** -/
private abbrev boxGerm (t : movingProd k V L) (a : V) (b : lineSpace k V L) (c : V) :
    grpStalk (movingRS k V L) (boxSh k V L).val t :=
  grpGerm (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t)
    ((boxSection k V L a b c).eval (op ⊤))

/-- The submodule `𝔪ₜ · 𝒪(1,1,1)ₜ` of the stalk at `t`: a global section is nonvanishing at `t`
exactly when its germ escapes it. -/
private abbrev boxMax (t : movingProd k V L) :
    Submodule (ringStalk (movingRS k V L) t)
      (grpStalk (movingRS k V L) (boxSh k V L).val t) :=
  IsLocalRing.maximalIdeal (ringStalk (movingRS k V L) t) • ⊤

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The nonvanishing locus of a global section of `𝒪(1,1,1)` as a condition on its germ.** -/
private theorem mem_nonvanishingLocus_iff_germ (t : movingProd k V L)
    (s : (boxModule k V L).sections) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := movingRS k V L)
        (boxModule k V L) s ↔
      grpGerm (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t) (s.eval (op ⊤)) ∉
        boxMax k V L t := Iff.rfl

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is additive in its source vector. -/
private theorem boxGerm_add_source (t : movingProd k V L) (a a' : V) (b : lineSpace k V L)
    (c : V) :
    boxGerm k V L t (a + a') b c = boxGerm k V L t a b c + boxGerm k V L t a' b c :=
  by rw [boxGerm, boxGerm, boxGerm, boxSection_eval_top_add_source, map_add]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is additive in its line vector. -/
private theorem boxGerm_add_line (t : movingProd k V L) (a : V) (b b' : lineSpace k V L)
    (c : V) :
    boxGerm k V L t a (b + b') c = boxGerm k V L t a b c + boxGerm k V L t a b' c :=
  by rw [boxGerm, boxGerm, boxGerm, boxSection_eval_top_add_line, map_add]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is additive in its target vector. -/
private theorem boxGerm_add_target (t : movingProd k V L) (a : V) (b : lineSpace k V L)
    (c c' : V) :
    boxGerm k V L t a b (c + c') = boxGerm k V L t a b c + boxGerm k V L t a b c' :=
  by rw [boxGerm, boxGerm, boxGerm, boxSection_eval_top_add_target, map_add]

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is `k`-homogeneous in its source
vector. -/
private theorem boxGerm_smul_source (t : movingProd k V L) (r : k) (a : V)
    (b : lineSpace k V L) (c : V) :
    boxGerm k V L t (r • a) b c =
      constGerm k (movingProdToSpec k V L) t r • boxGerm k V L t a b c :=
  by
    rw [boxGerm, boxGerm, boxSection_eval_top_smul_source]
    exact stalkModule_germ_smul (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t) _ _

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is `k`-homogeneous in its line
vector. -/
private theorem boxGerm_smul_line (t : movingProd k V L) (r : k) (a : V)
    (b : lineSpace k V L) (c : V) :
    boxGerm k V L t a (r • b) c =
      constGerm k (movingProdToSpec k V L) t r • boxGerm k V L t a b c :=
  by
    rw [boxGerm, boxGerm, boxSection_eval_top_smul_line]
    exact stalkModule_germ_smul (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t) _ _

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The germ of the tensor of three tautological sections is `k`-homogeneous in its target
vector. -/
private theorem boxGerm_smul_target (t : movingProd k V L) (r : k) (a : V)
    (b : lineSpace k V L) (c : V) :
    boxGerm k V L t a b (r • c) =
      constGerm k (movingProdToSpec k V L) t r • boxGerm k V L t a b c :=
  by
    rw [boxGerm, boxGerm, boxSection_eval_top_smul_target]
    exact stalkModule_germ_smul (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t) _ _

/-- **Normalising one slot.** If `F` is additive, homogeneous for a ring map `c` and lands in a
submodule `P` on the kernel of a functional `φ`, then modulo `P` replacing `a` by a reference
vector `a₀` costs the scalar `φ(a) / φ(a₀)`. -/
private theorem sub_smul_mem_of_kernel {K R W N : Type*} [Field K] [Semiring R] [AddCommGroup W]
    [Module K W] [AddCommGroup N] [Module R N] (c : K →+* R) (P : Submodule R N) (F : W → N)
    (φ : Module.Dual K W) (hadd : ∀ x y, F (x + y) = F x + F y)
    (hsmul : ∀ (r : K) x, F (r • x) = c r • F x) (hker : ∀ x, φ x = 0 → F x ∈ P) (a₀ : W)
    (ha₀ : φ a₀ ≠ 0) (a : W) : F a - c (φ a / φ a₀) • F a₀ ∈ P := by
  have key : F a = F (a - (φ a / φ a₀) • a₀) + c (φ a / φ a₀) • F a₀ := by
    rw [← hsmul, ← hadd, sub_add_cancel]
  rw [key, add_sub_cancel_right]
  refine hker _ ?_
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ ha₀, sub_self]

/-! ### The vanishing criterion for the tensor of three tautological sections -/

variable (t : movingProd k V L) (fx : Module.Dual k V) (hfx : fx ≠ 0)
  (hsrc : (prSource k V L).base t = linearFunctionalPoint k V fx hfx)
  (mu : Module.Dual k (lineSpace k V L)) (hmu : mu ≠ 0)
  (hline : (prLine k V L).base t = linearFunctionalPoint k (lineSpace k V L) mu hmu)
  (fy : Module.Dual k V) (hfy : fy ≠ 0)
  (htgt : (prTarget k V L).base t = linearFunctionalPoint k V fy hfy)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hsrc in
/-- **A source vector killed by the source functional makes the germ of the tensor vanish** at a
point whose source projection is the closed point cut out by that functional. -/
private theorem boxGerm_mem_of_source (a : V) (ha : fx a = 0) (bb : lineSpace k V L) (c : V) :
    boxGerm k V L t a bb c ∈ boxMax k V L t := by
  by_contra h
  have hnv : t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := movingRS k V L)
      (boxModule k V L) (boxSection k V L a bb c) :=
    (mem_nonvanishingLocus_iff_germ k V L t (boxSection k V L a bb c)).mpr h
  have h1 := ((mem_nonvanishingLocus_boxSection_iff k V L a bb c t).mp hnv).1
  rw [hsrc] at h1
  exact h1 ((linearFunctionalPoint_ι_mem k V fx hfx a).mpr ha)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hline in
/-- **A line vector killed by the line functional makes the germ of the tensor vanish.** -/
private theorem boxGerm_mem_of_line (a : V) (bb : lineSpace k V L) (hb : mu bb = 0) (c : V) :
    boxGerm k V L t a bb c ∈ boxMax k V L t := by
  by_contra h
  have hnv : t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := movingRS k V L)
      (boxModule k V L) (boxSection k V L a bb c) :=
    (mem_nonvanishingLocus_iff_germ k V L t (boxSection k V L a bb c)).mpr h
  have h1 := ((mem_nonvanishingLocus_boxSection_iff k V L a bb c t).mp hnv).2.1
  rw [hline] at h1
  exact h1 ((linearFunctionalPoint_ι_mem k (lineSpace k V L) mu hmu bb).mpr hb)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include htgt in
/-- **A target vector killed by the target functional makes the germ of the tensor vanish.** -/
private theorem boxGerm_mem_of_target (a : V) (bb : lineSpace k V L) (c : V) (hc : fy c = 0) :
    boxGerm k V L t a bb c ∈ boxMax k V L t := by
  by_contra h
  have hnv : t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := movingRS k V L)
      (boxModule k V L) (boxSection k V L a bb c) :=
    (mem_nonvanishingLocus_iff_germ k V L t (boxSection k V L a bb c)).mpr h
  have h1 := ((mem_nonvanishingLocus_boxSection_iff k V L a bb c t).mp hnv).2.2
  rw [htgt] at h1
  exact h1 ((linearFunctionalPoint_ι_mem k V fy hfy c).mpr hc)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hsrc hline htgt in
/-- **The germ of the tensor of three tautological sections escapes `𝔪ₜ · 𝒪(1,1,1)ₜ` exactly when
none of the three functionals kills its vector.** -/
private theorem boxGerm_notMem (a : V) (ha : fx a ≠ 0) (bb : lineSpace k V L) (hb : mu bb ≠ 0)
    (c : V) (hc : fy c ≠ 0) :
    boxGerm k V L t a bb c ∉ boxMax k V L t := by
  refine (mem_nonvanishingLocus_iff_germ k V L t (boxSection k V L a bb c)).mp ?_
  refine (mem_nonvanishingLocus_boxSection_iff k V L a bb c t).mpr ⟨?_, ?_, ?_⟩
  · rw [hsrc]
    exact fun h => ha ((linearFunctionalPoint_ι_mem k V fx hfx a).mp h)
  · rw [hline]
    exact fun h => hb ((linearFunctionalPoint_ι_mem k (lineSpace k V L) mu hmu bb).mp h)
  · rw [htgt]
    exact fun h => hc ((linearFunctionalPoint_ι_mem k V fy hfy c).mp h)

/-! ### The germ of the tensor against a reference triple -/

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hsrc in
/-- **Normalising the source slot.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, replacing the source vector by a
reference vector `a₀` costs the scalar `f_x(a) / f_x(a₀)`. -/
private theorem boxGerm_sub_smul_source_mem (a₀ : V) (ha₀ : fx a₀ ≠ 0) (a : V)
    (bb : lineSpace k V L) (c : V) :
    boxGerm k V L t a bb c -
        constGerm k (movingProdToSpec k V L) t (fx a / fx a₀) • boxGerm k V L t a₀ bb c ∈
      boxMax k V L t :=
  sub_smul_mem_of_kernel (constGerm k (movingProdToSpec k V L) t) _
    (boxGerm k V L t · bb c) fx
    (fun x y => boxGerm_add_source k V L t x y bb c)
    (fun r x => boxGerm_smul_source k V L t r x bb c)
    (fun x hx => boxGerm_mem_of_source k V L t fx hfx hsrc x hx bb c) a₀ ha₀ a

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hline in
/-- **Normalising the line slot.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, replacing the line vector by a
reference vector `b₀` costs the scalar `μ(b) / μ(b₀)`. -/
private theorem boxGerm_sub_smul_line_mem (b₀ : lineSpace k V L) (hb₀ : mu b₀ ≠ 0) (a : V)
    (bb : lineSpace k V L) (c : V) :
    boxGerm k V L t a bb c -
        constGerm k (movingProdToSpec k V L) t (mu bb / mu b₀) • boxGerm k V L t a b₀ c ∈
      boxMax k V L t :=
  sub_smul_mem_of_kernel (constGerm k (movingProdToSpec k V L) t) _
    (boxGerm k V L t a · c) mu
    (fun x y => boxGerm_add_line k V L t a x y c) (fun r x => boxGerm_smul_line k V L t r a x c)
    (fun x hx => boxGerm_mem_of_line k V L t mu hmu hline a x hx c) b₀ hb₀ bb

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include htgt in
/-- **Normalising the target slot.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, replacing the target vector by a
reference vector `c₀` costs the scalar `f_y(c) / f_y(c₀)`. -/
private theorem boxGerm_sub_smul_target_mem (c₀ : V) (hc₀ : fy c₀ ≠ 0) (a : V)
    (bb : lineSpace k V L) (c : V) :
    boxGerm k V L t a bb c -
        constGerm k (movingProdToSpec k V L) t (fy c / fy c₀) • boxGerm k V L t a bb c₀ ∈
      boxMax k V L t :=
  sub_smul_mem_of_kernel (constGerm k (movingProdToSpec k V L) t) _
    (boxGerm k V L t a bb ·) fy
    (fun x y => boxGerm_add_target k V L t a bb x y)
    (fun r x => boxGerm_smul_target k V L t r a bb x)
    (fun x hx => boxGerm_mem_of_target k V L t fy hfy htgt a bb x hx) c₀ hc₀ c

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hsrc hline htgt in
/-- **The germ formula.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, the germ at `t` of the tensor of three
tautological sections is the germ of the reference tensor times the product of the three
ratios. -/
private theorem boxGerm_sub_smul_mem (a₀ : V) (ha₀ : fx a₀ ≠ 0) (b₀ : lineSpace k V L)
    (hb₀ : mu b₀ ≠ 0) (c₀ : V) (hc₀ : fy c₀ ≠ 0) (a : V) (bb : lineSpace k V L) (c : V) :
    boxGerm k V L t a bb c -
        constGerm k (movingProdToSpec k V L) t
            (fx a / fx a₀ * (mu bb / mu b₀) * (fy c / fy c₀)) •
          boxGerm k V L t a₀ b₀ c₀ ∈
      boxMax k V L t := by
  have h1 := boxGerm_sub_smul_source_mem k V L t fx hfx hsrc a₀ ha₀ a bb c
  have h2 := boxGerm_sub_smul_line_mem k V L t mu hmu hline b₀ hb₀ a₀ bb c
  have h3 := boxGerm_sub_smul_target_mem k V L t fy hfy htgt c₀ hc₀ a₀ b₀ c
  have hsum : boxGerm k V L t a bb c -
      constGerm k (movingProdToSpec k V L) t
          (fx a / fx a₀ * (mu bb / mu b₀) * (fy c / fy c₀)) • boxGerm k V L t a₀ b₀ c₀ =
      (boxGerm k V L t a bb c -
          constGerm k (movingProdToSpec k V L) t (fx a / fx a₀) • boxGerm k V L t a₀ bb c) +
        constGerm k (movingProdToSpec k V L) t (fx a / fx a₀) •
          (boxGerm k V L t a₀ bb c -
            constGerm k (movingProdToSpec k V L) t (mu bb / mu b₀) •
              boxGerm k V L t a₀ b₀ c) +
        (constGerm k (movingProdToSpec k V L) t (fx a / fx a₀) *
            constGerm k (movingProdToSpec k V L) t (mu bb / mu b₀)) •
          (boxGerm k V L t a₀ b₀ c -
            constGerm k (movingProdToSpec k V L) t (fy c / fy c₀) •
              boxGerm k V L t a₀ b₀ c₀) := by
    rw [_root_.map_mul, _root_.map_mul]
    module
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))
    (Submodule.smul_mem _ _ h3)

/-! ### The determinant -/

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The value of a source functional at the tautological endomorphism, expanded in a basis of
the corank-two quotient.** -/
private theorem apply_lineEnd_eq_sum {ι : Type*} [Fintype ι]
    (bs : Module.Basis ι k (lineSpace k V L)) (nu : Module.Dual k (lineSpace k V L))
    (f : Module.Dual k V) (w : V) :
    f (lineEnd k V L nu w) = ∑ i, nu (bs i) * f (lineEnd k V L (bs.coord i) w) := by
  rw [lineEnd_eq_sum k V L bs nu, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul]

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The four normalising scalars of the minor section sum to the `2 × 2` determinant divided by
the product of the three reference values.** -/
private theorem sum_ratio_eq_det {ι : Type*} [Fintype ι]
    (bs : Module.Basis ι k (lineSpace k V L)) (nu : Module.Dual k (lineSpace k V L))
    (f g : Module.Dual k V) (a₀ : V) (ha₀ : f a₀ ≠ 0) (b₀ : lineSpace k V L)
    (hb₀ : nu b₀ ≠ 0) (c₀ : V) (hc₀ : g c₀ ≠ 0) (u v : V) :
    ∑ i : ι,
        (f (lineEnd k V L (bs.coord i) v) / f a₀ * (nu (bs i) / nu b₀) * (g u / g c₀) -
          f (lineEnd k V L (bs.coord i) u) / f a₀ * (nu (bs i) / nu b₀) * (g v / g c₀)) =
      (g u * f (lineEnd k V L nu v) - g v * f (lineEnd k V L nu u)) / (f a₀ * nu b₀ * g c₀) := by
  rw [apply_lineEnd_eq_sum k V L bs nu f v, apply_lineEnd_eq_sum k V L bs nu f u,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The germ of the minor section is the signed sum over the basis of the germs of the four
tensors.** -/
private theorem propGerm_eq_sum {ι : Type*} [Fintype ι]
    (bs : Module.Basis ι k (lineSpace k V L)) (u v : V) :
    grpGerm (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t)
        ((propSection k V L bs u v).eval (op ⊤)) =
      ∑ i : ι, (boxGerm k V L t (lineEnd k V L (bs.coord i) v) (bs i) u -
        boxGerm k V L t (lineEnd k V L (bs.coord i) u) (bs i) v) := by
  rw [propSection_eval, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_sub _ _ _

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
include hsrc hline htgt in
/-- **The germ formula for the minor section.** Modulo `𝔪ₜ · 𝒪(1,1,1)ₜ`, the germ at `t` of the
minor section is the germ of the reference tensor times the `2 × 2` determinant divided by the
product of the three reference values. -/
private theorem propGerm_sub_smul_mem {ι : Type*} [Fintype ι]
    (bs : Module.Basis ι k (lineSpace k V L)) (a₀ : V) (ha₀ : fx a₀ ≠ 0)
    (b₀ : lineSpace k V L) (hb₀ : mu b₀ ≠ 0) (c₀ : V) (hc₀ : fy c₀ ≠ 0) (u v : V) :
    grpGerm (movingRS k V L) (boxSh k V L).val t ⊤ (Opens.mem_top t)
          ((propSection k V L bs u v).eval (op ⊤)) -
        constGerm k (movingProdToSpec k V L) t
            ((fy u * fx (lineEnd k V L mu v) - fy v * fx (lineEnd k V L mu u)) /
              (fx a₀ * mu b₀ * fy c₀)) •
          boxGerm k V L t a₀ b₀ c₀ ∈
      boxMax k V L t := by
  rw [propGerm_eq_sum k V L t bs u v,
    ← sum_ratio_eq_det k V L bs mu fx fy a₀ ha₀ b₀ hb₀ c₀ hc₀ u v, map_sum, Finset.sum_smul,
    ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 := boxGerm_sub_smul_mem k V L t fx hfx hsrc mu hmu hline fy hfy htgt a₀ ha₀ b₀ hb₀
    c₀ hc₀ (lineEnd k V L (bs.coord i) v) (bs i) u
  have h2 := boxGerm_sub_smul_mem k V L t fx hfx hsrc mu hmu hline fy hfy htgt a₀ ha₀ b₀ hb₀
    c₀ hc₀ (lineEnd k V L (bs.coord i) u) (bs i) v
  have hrw : (boxGerm k V L t (lineEnd k V L (bs.coord i) v) (bs i) u -
          boxGerm k V L t (lineEnd k V L (bs.coord i) u) (bs i) v) -
        constGerm k (movingProdToSpec k V L) t
            (fx (lineEnd k V L (bs.coord i) v) / fx a₀ * (mu (bs i) / mu b₀) * (fy u / fy c₀) -
              fx (lineEnd k V L (bs.coord i) u) / fx a₀ * (mu (bs i) / mu b₀) *
                (fy v / fy c₀)) •
          boxGerm k V L t a₀ b₀ c₀ =
      (boxGerm k V L t (lineEnd k V L (bs.coord i) v) (bs i) u -
          constGerm k (movingProdToSpec k V L) t
              (fx (lineEnd k V L (bs.coord i) v) / fx a₀ * (mu (bs i) / mu b₀) *
                (fy u / fy c₀)) •
            boxGerm k V L t a₀ b₀ c₀) -
        (boxGerm k V L t (lineEnd k V L (bs.coord i) u) (bs i) v -
          constGerm k (movingProdToSpec k V L) t
              (fx (lineEnd k V L (bs.coord i) u) / fx a₀ * (mu (bs i) / mu b₀) *
                (fy v / fy c₀)) •
            boxGerm k V L t a₀ b₀ c₀) := by
    rw [map_sub]
    module
  rw [hrw]
  exact Submodule.sub_mem _ h1 h2

end Germ

/-! ### The characterisation at a triple of closed points -/

section Main

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The minor section is nonvanishing at a point whose three projections are the closed points
cut out by `f_x`, `μ` and `f_y` exactly when the corresponding `2 × 2` determinant is nonzero.**
-/
public theorem mem_nonvanishingLocus_propSection_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (t : movingProd k V L)
    (fx : Module.Dual k V) (hfx : fx ≠ 0)
    (hsrc : (prSource k V L).base t = linearFunctionalPoint k V fx hfx)
    (mu : Module.Dual k (lineSpace k V L)) (hmu : mu ≠ 0)
    (hline : (prLine k V L).base t = linearFunctionalPoint k (lineSpace k V L) mu hmu)
    (fy : Module.Dual k V) (hfy : fy ≠ 0)
    (htgt : (prTarget k V L).base t = linearFunctionalPoint k V fy hfy) (u v : V) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
        (boxModule k V L) (propSection k V L b u v) ↔
      fy u * fx (lineEnd k V L mu v) - fy v * fx (lineEnd k V L mu u) ≠ 0 := by
  obtain ⟨a₀, ha₀⟩ : ∃ a : V, fx a ≠ 0 := by simpa using DFunLike.ne_iff.mp hfx
  obtain ⟨b₀, hb₀⟩ : ∃ bb : lineSpace k V L, mu bb ≠ 0 := by simpa using DFunLike.ne_iff.mp hmu
  obtain ⟨c₀, hc₀⟩ : ∃ c : V, fy c ≠ 0 := by simpa using DFunLike.ne_iff.mp hfy
  have he := boxGerm_notMem k V L t fx hfx hsrc mu hmu hline fy hfy htgt a₀ ha₀ b₀ hb₀ c₀ hc₀
  have hmain := propGerm_sub_smul_mem k V L t fx hfx hsrc mu hmu hline fy hfy htgt b a₀ ha₀
    b₀ hb₀ c₀ hc₀ u v
  rw [mem_nonvanishingLocus_iff_germ k V L t (propSection k V L b u v)]
  refine ⟨fun h hD => h ?_, fun hD => ?_⟩
  · rw [hD, zero_div, map_zero, zero_smul, sub_zero] at hmain
    exact hmain
  · have hden : fx a₀ * mu b₀ * fy c₀ ≠ 0 := mul_ne_zero (mul_ne_zero ha₀ hb₀) hc₀
    have hunit := isUnit_constGerm k (movingProdToSpec k V L) t (div_ne_zero hD hden)
    have h2 : constGerm k (movingProdToSpec k V L) t
          ((fy u * fx (lineEnd k V L mu v) - fy v * fx (lineEnd k V L mu u)) /
            (fx a₀ * mu b₀ * fy c₀)) • boxGerm k V L t a₀ b₀ c₀ ∉ boxMax k V L t :=
      (Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff _ _).mpr ⟨hunit, he⟩
    have hadd := Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_add _ _ h2 hmain
    rwa [add_sub_cancel] at hadd

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **A point of the triple product whose three projections are closed points lies on the graph
of the family of projective transformations exactly when all the `2 × 2` determinants vanish**,
that is exactly when the functional cutting out its target point is proportional to `f_x ∘ g`
for the tautological endomorphism `g = lineEnd μ` its line coordinate names. -/
public theorem mem_movingGraph_iff_of_linearFunctionalPoint {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (t : movingProd k V L)
    (fx : Module.Dual k V) (hfx : fx ≠ 0)
    (hsrc : (prSource k V L).base t = linearFunctionalPoint k V fx hfx)
    (mu : Module.Dual k (lineSpace k V L)) (hmu : mu ≠ 0)
    (hline : (prLine k V L).base t = linearFunctionalPoint k (lineSpace k V L) mu hmu)
    (fy : Module.Dual k V) (hfy : fy ≠ 0)
    (htgt : (prTarget k V L).base t = linearFunctionalPoint k V fy hfy) :
    t ∈ movingGraph k V L b ↔
      ∀ u v : V, fy u * fx (lineEnd k V L mu v) = fy v * fx (lineEnd k V L mu u) := by
  rw [mem_movingGraph_iff]
  refine forall_congr' fun u => forall_congr' fun v => ?_
  rw [mem_nonvanishingLocus_propSection_iff k V L b t fx hfx hsrc mu hmu hline fy hfy htgt u v,
    not_not, sub_eq_zero]

end Main

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
