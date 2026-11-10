module

public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus

/-!
# Linearity of the tautological sections of `𝒪(1)` on `𝐏(M)`

The global section `ι v / 1` of `𝒪(1)` on `𝐏(M) = Proj (Sym_k M)` attached to a vector `v` of a
`k`-vector space `M` is `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalSection`. This
file records that it depends `k`-linearly on `v`, open by open: over every open `U` of `𝐏(M)` the
value of the section is additive in `v`, kills `0`, and scales by the degree-zero function
`r / 1` when `v` is scaled by `r`. The same three statements are proved for the pullback of the
section along an arbitrary morphism of schemes `f : T ⟶ 𝐏(M)`, and the bilinearity of the tensor
product of two global sections is recorded at the level of the values over an open.

The vector cannot be moved inside the type `(tautologicalModule k M).sections`: that type is a
bare subtype of a product of modules with no additive structure attached, which is why every
statement here is an identity between the *values* `s.eval U` and not between sections.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.ιOne`: a vector of `M` read as a degree-one
  homogeneous element of `Sym_k M`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGlobalFunction` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarFunction`: the global function `r / 1` on
  `𝐏(M)` attached to a scalar `r : k`, and its restriction to an open.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection`: the pullback of the
  tautological section along a morphism `f : T ⟶ 𝐏(M)` of schemes, with
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackScalarFunction` the pullback of the scalar
  function.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalSection_evalOp_add`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalSection_evalOp_smul` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalSection_evalOp_zero`: **the value of the
  tautological section over an open is `k`-linear in the vector.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection_eval_add`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection_eval_smul` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection_eval_zero`: the same for the
  pullback along a morphism of schemes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.nonvanishingLocus_pullbackTautSection`: the
  nonvanishing locus of a pulled-back tautological section is the preimage of the nonvanishing
  locus.
* `Stacks.SheafOfModules.tensorSections_eval_add_left`,
  `Stacks.SheafOfModules.tensorSections_eval_add_right`,
  `Stacks.SheafOfModules.tensorSections_eval_smul_left` and
  `Stacks.SheafOfModules.tensorSections_eval_smul_right`: **the tensor product of two global
  sections is bilinear** at the level of the values over an open.

## Implementation notes

The scalar action is the one of the structure sheaf, not a `k`-action: the module
`(tautologicalModule k M).val.obj U` is a module over `𝒪(U)` and carries no `k`-structure, so
the scaling statement multiplies by the image of `r` under `k → 𝒮 0 → Γ(𝐏(M), 𝒪) → 𝒪(U)`, which
is `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarFunction`. That image is produced from the
degree-zero element `r • 1` of the symmetric grading through
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroRingToGlobalSections`, which is
exactly the ring whose action
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections` is linear for.

The linearity of the degree-`n` section map is therefore its `𝒮 0`-linearity read through that
canonical ring map, and the only arithmetic in the file is the identity `(r • 1) * a = r • a` in
the symmetric algebra, which turns a `k`-scaling of a homogeneous element into the `𝒮 0`-scaling
the linear map understands.

Each `_eval` lemma is `rfl`: the sections produced by
`Stacks.ProjTwistSection.homogeneousSection` and
`Stacks.SheafOfModules.modulePullbackSection` are, by construction, the restrictions of a single
element over `⊤`, so their value over `U` is a restriction map applied to that element. The
restriction maps are used in their bundled semilinear form `PresheafOfModules.restrictₛₗ`, which
is what carries the additivity and the semilinearity used in every proof.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k M : Type u) [Field k] [AddCommGroup M] [Module k M]

/-! ### Linearity of the degree-`n` section map -/

/-- A homogeneous element of degree `n` of the symmetric algebra lies in the degree-zero piece of
the `n`-th shift of the regular graded module, which is the grading the twisting sheaf `𝒪(n)` is
built from. -/
public theorem mem_twistGrading_zero_of_mem (n : ℕ) (x : SymmetricAlgebra k M)
    (hx : x ∈ symmetricGrading k M n) :
    x ∈ twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ) 0 := by
  simp [twistGrading, integerGrading, homogeneousSubmodule, hx]

/-- **The global section of `𝒪(n)` attached to a homogeneous element is additive** in that
element. -/
public theorem degreeSection_add (n : ℕ) (a b : symmetricGrading k M n) :
    degreeSection (symmetricGrading k M) n (a + b) =
      degreeSection (symmetricGrading k M) n a + degreeSection (symmetricGrading k M) n b :=
  map_add (degreeZeroToGlobalSections (symmetricGrading k M)
      (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ)))
    ⟨(a : SymmetricAlgebra k M), mem_twistGrading_zero_of_mem k M n a a.2⟩
    ⟨(b : SymmetricAlgebra k M), mem_twistGrading_zero_of_mem k M n b b.2⟩

/-- **The global section of `𝒪(n)` attached to the zero homogeneous element is zero.** -/
public theorem degreeSection_zero (n : ℕ) :
    degreeSection (symmetricGrading k M) n 0 = 0 :=
  map_zero (degreeZeroToGlobalSections (symmetricGrading k M)
    (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ)))

/-- The degree-zero homogeneous element `r • 1` of `Sym_k M` attached to a scalar `r : k`. It is
the degree-zero scalar through which a `k`-scaling of a homogeneous element is seen by the
degree-`n` section map. -/
public def scalarUnit (r : k) : symmetricGrading k M 0 :=
  r • ⟨1, SetLike.one_mem_graded (symmetricGrading k M)⟩

/-- **Scaling a homogeneous element by `r : k` is the action of the degree-zero element
`r • 1`**: the only arithmetic behind the linearity of the section map, namely
`(r • 1) * a = r • a`. -/
public theorem scalarUnit_smul (n : ℕ) (r : k) (a : symmetricGrading k M n) :
    scalarUnit k M r •
      (⟨(a : SymmetricAlgebra k M), mem_twistGrading_zero_of_mem k M n a a.2⟩ :
        twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ) 0) =
      ⟨((r • a : symmetricGrading k M n) : SymmetricAlgebra k M),
        mem_twistGrading_zero_of_mem k M n _ (r • a).2⟩ := by
  apply Subtype.ext
  change (r • (1 : SymmetricAlgebra k M)) • (a : SymmetricAlgebra k M) =
    r • (a : SymmetricAlgebra k M)
  rw [smul_eq_mul, smul_mul_assoc, one_mul]

/-- **The global section of `𝒪(n)` attached to a homogeneous element scaled by `r : k` is the
structure-sheaf function `r / 1` times the original section.** -/
public theorem degreeSection_smul (n : ℕ) (r : k) (a : symmetricGrading k M n) :
    degreeSection (symmetricGrading k M) n (r • a) =
      degreeZeroRingToGlobalSections (symmetricGrading k M) (scalarUnit k M r) •
        degreeSection (symmetricGrading k M) n a := by
  let : Module ↥(symmetricGrading k M 0)
      ((associatedModuleSheaf (symmetricGrading k M)
        (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ))).val.obj
          (op ⊤)) :=
    Module.compHom _ (degreeZeroRingToGlobalSections (symmetricGrading k M))
  have h : degreeZeroToGlobalSections (symmetricGrading k M)
        (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ))
        (scalarUnit k M r •
          ⟨(a : SymmetricAlgebra k M), mem_twistGrading_zero_of_mem k M n a a.2⟩) =
      scalarUnit k M r • degreeZeroToGlobalSections (symmetricGrading k M)
        (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ))
        ⟨(a : SymmetricAlgebra k M), mem_twistGrading_zero_of_mem k M n a a.2⟩ :=
    LinearMap.map_smul _ _ _
  exact (congrArg (fun x => degreeZeroToGlobalSections (symmetricGrading k M)
    (twistGrading (S := SymmetricAlgebra k M) (symmetricGrading k M) (n : ℤ)) x)
    (scalarUnit_smul k M n r a).symm).trans h

/-! ### The tautological section as a linear function of the vector -/

/-- A vector of `M` read as a degree-one homogeneous element of `Sym_k M`: the linear form `v`
itself, which is what the tautological section of `𝒪(1)` is built from. -/
public def ιOne (v : M) : symmetricGrading k M 1 :=
  ⟨SymmetricAlgebra.ι k M v, ι_mem_symmetricPower_one k M v⟩

/-- The global function `r / 1` on `𝐏(M)` attached to a scalar `r : k`: the image of the
degree-zero element `r • 1` under the canonical ring map to the global sections of the structure
sheaf. -/
public def scalarGlobalFunction (r : k) :
    (projectiveSpaceOfModule k M).ringCatSheaf.obj.obj (op ⊤) :=
  degreeZeroRingToGlobalSections (symmetricGrading k M) (scalarUnit k M r)

/-- The function `r / 1` on `𝐏(M)` restricted to an open `U`: the scalar of `𝒪(U)` by which the
tautological section of a scaled vector differs from the tautological section. -/
public def scalarFunction (r : k) (U : (Opens ↥(projectiveSpaceOfModule k M))ᵒᵖ) :
    (projectiveSpaceOfModule k M).ringCatSheaf.obj.obj U :=
  ((projectiveSpaceOfModule k M).ringCatSheaf.obj.map
    (homOfLE (le_top (a := U.unop))).op).hom (scalarGlobalFunction k M r)

/-- The value of the tautological section over an open is the restriction of the global section
of `𝒪(1)` attached to the degree-one element `ι v`. -/
public theorem tautologicalSection_evalOp (v : M)
    (U : (Opens ↥(projectiveSpaceOfModule k M))ᵒᵖ) :
    (tautologicalSection k M v).eval U =
      (tautologicalModule k M).val.restrictₛₗ (homOfLE (le_top (a := U.unop))).op
        (degreeSection (symmetricGrading k M) 1 (ιOne k M v)) := rfl

/-- **The value of the tautological section over an open is additive in the vector.** -/
public theorem tautologicalSection_evalOp_add (v w : M)
    (U : (Opens ↥(projectiveSpaceOfModule k M))ᵒᵖ) :
    (tautologicalSection k M (v + w)).eval U =
      (tautologicalSection k M v).eval U + (tautologicalSection k M w).eval U := by
  have h : degreeSection (symmetricGrading k M) 1 (ιOne k M (v + w)) =
      degreeSection (symmetricGrading k M) 1 (ιOne k M v) +
        degreeSection (symmetricGrading k M) 1 (ιOne k M w) := by
    rw [show ιOne k M (v + w) = ιOne k M v + ιOne k M w from
      Subtype.ext (map_add (SymmetricAlgebra.ι k M) v w)]
    exact degreeSection_add k M 1 _ _
  rw [tautologicalSection_evalOp, tautologicalSection_evalOp, tautologicalSection_evalOp, h]
  exact map_add _ _ _

/-- **The value of the tautological section over an open scales by the function `r / 1` when the
vector is scaled by `r`.** -/
public theorem tautologicalSection_evalOp_smul (r : k) (v : M)
    (U : (Opens ↥(projectiveSpaceOfModule k M))ᵒᵖ) :
    (tautologicalSection k M (r • v)).eval U =
      scalarFunction k M r U • (tautologicalSection k M v).eval U := by
  have h : degreeSection (symmetricGrading k M) 1 (ιOne k M (r • v)) =
      degreeZeroRingToGlobalSections (symmetricGrading k M) (scalarUnit k M r) •
        degreeSection (symmetricGrading k M) 1 (ιOne k M v) := by
    rw [show ιOne k M (r • v) = r • ιOne k M v from
      Subtype.ext (map_smul (SymmetricAlgebra.ι k M) r v)]
    exact degreeSection_smul k M 1 r _
  rw [tautologicalSection_evalOp, tautologicalSection_evalOp, h]
  exact LinearMap.map_smulₛₗ _ _ _

/-- **The tautological section of the zero vector vanishes over every open.** -/
public theorem tautologicalSection_evalOp_zero
    (U : (Opens ↥(projectiveSpaceOfModule k M))ᵒᵖ) :
    (tautologicalSection k M (0 : M)).eval U = 0 := by
  have h : degreeSection (symmetricGrading k M) 1 (ιOne k M 0) = 0 := by
    rw [show ιOne k M (0 : M) = 0 from Subtype.ext (map_zero (SymmetricAlgebra.ι k M))]
    exact degreeSection_zero k M 1
  rw [tautologicalSection_evalOp, h]
  exact map_zero _

/-! ### The pullback of the tautological section along a morphism of schemes -/

variable {T : Scheme.{u}}

/-- The pullback along a morphism of schemes `f : T ⟶ 𝐏(M)` of the tautological section of
`𝒪(1)` attached to a vector. -/
public def pullbackTautSection (f : T ⟶ projectiveSpaceOfModule k M) (v : M) :
    ((Scheme.Modules.pullback f).obj (tautologicalModule k M)).sections :=
  Stacks.SheafOfModules.modulePullbackSection f.toLRSHom (tautologicalModule k M)
    (tautologicalSection k M v)

/-- The pullback along `f` of the function `r / 1`, restricted to an open of `T`. -/
public def pullbackScalarFunction (f : T ⟶ projectiveSpaceOfModule k M) (r : k)
    (U : (Opens ↥T)ᵒᵖ) : T.ringCatSheaf.obj.obj U :=
  (T.ringCatSheaf.obj.map (homOfLE (le_top (a := U.unop))).op).hom
    (Stacks.RingedSpace.sharp f.toLRSHom.toShHom (op ⊤) (scalarGlobalFunction k M r))

/-- The value of a pulled-back tautological section over an open is the restriction of the image
of the global value of the section under the unit of `f^* ⊣ f_*`. -/
public theorem pullbackTautSection_eval (f : T ⟶ projectiveSpaceOfModule k M) (v : M)
    (U : (Opens ↥T)ᵒᵖ) :
    (pullbackTautSection k M f v).eval U =
      ((Scheme.Modules.pullback f).obj (tautologicalModule k M)).val.restrictₛₗ
        (homOfLE (le_top (a := U.unop))).op
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
          ((tautologicalSection k M v).eval (op ⊤))) := rfl

/-- **The value of a pulled-back tautological section over an open is additive in the
vector.** -/
public theorem pullbackTautSection_eval_add (f : T ⟶ projectiveSpaceOfModule k M) (v w : M)
    (U : (Opens ↥T)ᵒᵖ) :
    (pullbackTautSection k M f (v + w)).eval U =
      (pullbackTautSection k M f v).eval U + (pullbackTautSection k M f w).eval U := by
  have h : Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
        ((tautologicalSection k M (v + w)).eval (op ⊤)) =
      Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
          ((tautologicalSection k M v).eval (op ⊤)) +
        Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
          ((tautologicalSection k M w).eval (op ⊤)) := by
    rw [tautologicalSection_evalOp_add k M v w (op ⊤)]
    exact Stacks.RingedSpace.pullbackUnit_add f.toLRSHom.toShHom (tautologicalModule k M)
      (op ⊤) _ _
  rw [pullbackTautSection_eval, pullbackTautSection_eval, pullbackTautSection_eval, h]
  exact map_add _ _ _

/-- **The value of a pulled-back tautological section over an open scales by the pulled-back
function `r / 1` when the vector is scaled by `r`.** -/
public theorem pullbackTautSection_eval_smul (f : T ⟶ projectiveSpaceOfModule k M) (r : k)
    (v : M) (U : (Opens ↥T)ᵒᵖ) :
    (pullbackTautSection k M f (r • v)).eval U =
      pullbackScalarFunction k M f r U • (pullbackTautSection k M f v).eval U := by
  have h : Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
        ((tautologicalSection k M (r • v)).eval (op ⊤)) =
      Stacks.RingedSpace.sharp f.toLRSHom.toShHom (op ⊤) (scalarGlobalFunction k M r) •
        Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
          ((tautologicalSection k M v).eval (op ⊤)) := by
    rw [tautologicalSection_evalOp_smul k M r v (op ⊤)]
    exact Stacks.RingedSpace.pullbackUnit_smul f.toLRSHom.toShHom (tautologicalModule k M)
      (op ⊤) _ _
  rw [pullbackTautSection_eval, pullbackTautSection_eval, h]
  exact LinearMap.map_smulₛₗ _ _ _

/-- **A pulled-back tautological section of the zero vector vanishes over every open.** -/
public theorem pullbackTautSection_eval_zero (f : T ⟶ projectiveSpaceOfModule k M)
    (U : (Opens ↥T)ᵒᵖ) :
    (pullbackTautSection k M f (0 : M)).eval U = 0 := by
  have h : Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (tautologicalModule k M) (op ⊤)
      ((tautologicalSection k M (0 : M)).eval (op ⊤)) = 0 := by
    rw [tautologicalSection_evalOp_zero k M (op ⊤)]
    exact map_zero _
  rw [pullbackTautSection_eval, h]
  exact map_zero _

/-- **The nonvanishing locus of a pulled-back tautological section is the preimage of the
nonvanishing locus** of the tautological section ([Stacks, Tag 0H78]). -/
public theorem nonvanishingLocus_pullbackTautSection (f : T ⟶ projectiveSpaceOfModule k M)
    (v : M) :
    Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        ((Scheme.Modules.pullback f).obj (tautologicalModule k M))
        (pullbackTautSection k M f v) =
      f.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k M).toRingedSpace)
        (tautologicalModule k M) (tautologicalSection k M v) := by
  have hinv := isInvertible_tautologicalModule k M
  exact (congrArg (fun U : T.Opens => (U : Set T))
    (Stacks.SheafOfModules.preimage_nonvanishingOpen f (tautologicalModule k M)
      (tautologicalSection k M v))).symm

end AlgebraicGeometry.ProjectiveSpaceOfModule

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (F G : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- The canonical map from the presheaf tensor product into the sheafified one is additive. -/
public theorem toTensorSheafSection_add (U : (Opens X.carrier)ᵒᵖ)
    (x y : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    TensorStalkRingedSpace.toTensorSheafSection X F G U (x + y) =
      TensorStalkRingedSpace.toTensorSheafSection X F G U x +
        TensorStalkRingedSpace.toTensorSheafSection X F G U y :=
  map_add (PresheafOfModules.Hom.app (TensorStalkRingedSpace.sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) U).hom x y

/-- The canonical map from the presheaf tensor product into the sheafified one is
`𝒪(U)`-linear. -/
public theorem toTensorSheafSection_smul (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U)
    (x : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    TensorStalkRingedSpace.toTensorSheafSection X F G U (r • x) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U)
          _ _ r (TensorStalkRingedSpace.toTensorSheafSection X F G U x) :=
  map_smul (PresheafOfModules.Hom.app (TensorStalkRingedSpace.sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) U).hom r x

variable (s s' : F.sections) (t t' : G.sections) (U : (Opens X.carrier)ᵒᵖ)

/-- **The tensor product of two global sections is additive in its first argument**, at the level
of the values over an open: the `sections` type carries no additive structure, so the sum is
taken inside the tensor product of the values. -/
public theorem tensorSections_eval_add_left :
    TensorStalkRingedSpace.toTensorSheafSection X F G U
        ((s.eval U + s'.eval U) ⊗ₜ[X.presheaf.obj U] t.eval U) =
      (tensorSections F G s t).eval U + (tensorSections F G s' t).eval U := by
  rw [tensorSections_eval, tensorSections_eval, TensorProduct.add_tmul]
  exact toTensorSheafSection_add F G U _ _

/-- **The tensor product of two global sections is additive in its second argument**, at the
level of the values over an open. -/
public theorem tensorSections_eval_add_right :
    TensorStalkRingedSpace.toTensorSheafSection X F G U
        (s.eval U ⊗ₜ[X.presheaf.obj U] (t.eval U + t'.eval U)) =
      (tensorSections F G s t).eval U + (tensorSections F G s t').eval U := by
  rw [tensorSections_eval, tensorSections_eval, TensorProduct.tmul_add]
  exact toTensorSheafSection_add F G U _ _

/-- **The tensor product of two global sections is `𝒪(U)`-linear in its first argument**, at the
level of the values over an open. -/
public theorem tensorSections_eval_smul_left (r : X.presheaf.obj U) :
    TensorStalkRingedSpace.toTensorSheafSection X F G U
        ((r • s.eval U) ⊗ₜ[X.presheaf.obj U] t.eval U) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U)
        _ _ r ((tensorSections F G s t).eval U) := by
  rw [tensorSections_eval, ← TensorProduct.smul_tmul']
  exact toTensorSheafSection_smul F G U r _

/-- **The tensor product of two global sections is `𝒪(U)`-linear in its second argument**, at
the level of the values over an open. -/
public theorem tensorSections_eval_smul_right (r : X.presheaf.obj U) :
    TensorStalkRingedSpace.toTensorSheafSection X F G U
        (s.eval U ⊗ₜ[X.presheaf.obj U] (r • t.eval U)) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U)
        _ _ r ((tensorSections F G s t).eval U) := by
  rw [tensorSections_eval, TensorProduct.tmul_smul]
  exact toTensorSheafSection_smul F G U r _

end Stacks.SheafOfModules

end
