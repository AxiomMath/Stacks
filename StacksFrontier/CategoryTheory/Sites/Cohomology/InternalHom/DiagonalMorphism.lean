module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
import StacksCore.Tactic.StacksAttribute

/-! # The diagonal morphism into an internal Hom of a total tensor product

Let `(C, O)` be a ringed site and let `K` and `L` be complexes of `O`-modules. A local section
`k` of `K` of degree `n` over an object `U` sends a local section `l` of `L` of degree `p` to
the pure tensor `k ⊗ l`, a local section of `Tot(K ⊗_O L)` of degree `n + p`; these maps are
the components of a homogeneous local section of the internal Hom complex
`SheafHom(L, Tot(K ⊗_O L))`, and they assemble into the canonical morphism of complexes of
`O`-modules of Stacks 0A93,

`K ⟶ SheafHom(L, Tot(K ⊗_O L))`,

which is natural in `K` and dinatural in `L`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalSectionAt`: the homogeneous local pure tensor of
  `AlgebraicGeometry.RingedSite.tensorTotalSection`, read in a degree `c` with `t + r = c`.
* `AlgebraicGeometry.RingedSite.diagonalCochain` and
  `AlgebraicGeometry.RingedSite.diagonalHomSection`: the homogeneous local section of
  `SheafHom(L, Tot(K ⊗_O L))` determined by a homogeneous local section of `K`, as a cochain
  and as a section.
* `AlgebraicGeometry.RingedSite.diagonalMap`: the diagonal morphism of Stacks 0A93.
* `AlgebraicGeometry.RingedSite.DiagonalConstruction`: the diagonal morphism together with its
  characterisation on homogeneous local sections.

## Main results

* `AlgebraicGeometry.RingedSite.restrictSection_add` and its companions: the elementary
  calculus of `AlgebraicGeometry.RingedSite.restrictSection`.
* `AlgebraicGeometry.RingedSite.tensorTotalSectionAt_d`: the Koszul Leibniz rule
  `d(a ⊗ b) = (da) ⊗ b + (-1)^t a ⊗ (db)` for the local pure tensors; with
  `AlgebraicGeometry.RingedSite.tensorTotalSectionAt_add_left` and its companions these are
  their bilinearity, their compatibility with restriction, their functoriality, and the
  renaming of the degrees they are read in — `tensorTotalSectionAt_congr_right` for the degree
  of the second factor and `tensorTotalSectionAt_XIsoOfEq` for the total degree, which are what
  keep an `eqToHom` out of statements about them.
* `AlgebraicGeometry.RingedSite.diagonalMap_applyHomSection`: the characterisation of
  `diagonalMap` on homogeneous local sections.
* `AlgebraicGeometry.RingedSite.diagonalConstruction`: **Stacks 0A93**, the canonical diagonal
  morphism.
* `AlgebraicGeometry.RingedSite.diagonalMap_natural`: **Stacks 0A93**, functoriality in both
  complexes.

## Implementation notes

The construction follows `AlgebraicGeometry.RingedSite.compositionMap` of Stacks 0A91 and
`AlgebraicGeometry.RingedSite.evaluationMap` of Stacks 0A92, with one simplification: the
source of the diagonal is the complex `K` itself rather than a total tensor product, so there
is no sheafification to lift through and the morphism is assembled directly out of its
homogeneous local sections. Everything about those sections is proved in the evaluation
vocabulary of `StacksDraft.Ch21.Sec34.HomSectionEvaluation`, through
`AlgebraicGeometry.RingedSite.homSection_ext`, which is what lets this file need no
transparency option.

The elementary calculus of the local pure tensors of `Tot(K ⊗_O L)` — bilinearity,
compatibility with restriction, and the Koszul Leibniz rule — is developed here because this
is the first place it is needed; it belongs with
`AlgebraicGeometry.RingedSite.tensorTotalSection` itself. The Leibniz rule is a presheaf-level
bicomplex computation, `AlgebraicGeometry.RingedSite.ιTensorTotalPresheaf_comp_d`, whose two
Koszul signs are the `ε₁ = 1` and `ε₂ = (-1)^t` of a total complex, transported across the
degreewise sheafification by unit naturality. Those pure tensors are introduced through the
single morphism of presheaves of modules
`AlgebraicGeometry.RingedSite.tensorTotalTmulMap`, so that every one of their elementary
properties is `map_add`, `map_smul` or naturality of that one morphism; stating them instead
by unfolding the pure tensor leaves goals that are only type-correct at default transparency,
which is what makes `rw` refuse on them.

Restriction of a section is always written `AlgebraicGeometry.RingedSite.restrictSection`,
whose declared type is the ambient one: `A.val.map i.op x` has the type of a restriction of
scalars, and a goal containing it is not type-correct at the `implicit` transparency level,
after which every rewrite fails. Its elementary calculus is recorded here because it is public
API that the statements of this file and of its consumers are phrased in.

A version of the pure tensor carrying its total degree as a separate parameter is needed
because the two summands of the Leibniz rule naturally live in degrees `(t + 1) + r` and
`t + (r + 1)`, neither of which is the degree `t + r + 1` of the target, and because a
component of a degree-`n` cochain out of `L` is indexed by `p + n = q` rather than by
`n + p = q`.

The universes are the diagonal `RingedSite.{u, u, u}`, which is where
`AlgebraicGeometry.RingedSite.tensorTotal` and the composition and evaluation morphisms of
Stacks 0A91 and 0A92 are stated.

Over a ringed space the same morphism is
`Stacks.SheafOfModules.diagonalTensorHom` of Stacks 0A8Q; a ringed space is a ringed site, but
its sheaves of modules there are indexed by a topological sheaf of rings rather than by
`AlgebraicGeometry.RingedSite.ringSheaf`, so neither statement is literally an instance of the
other.

## References

* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-! ## Restriction of local sections -/

/-- Restriction of a section is additive. -/
lemma restrictSection_add {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {W V : X.C} (i : V ⟶ W) (x y : A.val.obj (op W)) :
    restrictSection X i (x + y) = restrictSection X i x + restrictSection X i y :=
  map_add _ _ _

/-- Restriction of a section is semilinear. -/
lemma restrictSection_smul {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {W V : X.C} (i : V ⟶ W)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (x : A.val.obj (op W)) :
    restrictSection X i (s • x) =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op s • restrictSection X i x :=
  PresheafOfModules.map_smul A.val i.op s x

/-- Restriction of a section along the identity. -/
lemma restrictSection_id {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {W : X.C} (x : A.val.obj (op W)) : restrictSection X (𝟙 W) x = x := by
  simp [restrictSection]

/-- Restriction of a section along a composite. -/
lemma restrictSection_comp {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {W V V' : X.C} (i : V ⟶ W) (j : V' ⟶ V) (x : A.val.obj (op W)) :
    restrictSection X (j ≫ i) x = restrictSection X j (restrictSection X i x) :=
  PresheafOfModules.map_comp_apply A.val i.op j.op x

/-- A morphism of sheaves of `O`-modules commutes with restriction of sections. -/
lemma restrictSection_natural
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    {W V : X.C} (i : V ⟶ W) (x : A.val.obj (op W)) :
    restrictSection X i (f.val.app (op W) x) = f.val.app (op V) (restrictSection X i x) :=
  (PresheafOfModules.naturality_apply f.val i.op x).symm

/-! ## The local pure tensors of the total tensor-product complex -/

section PureTensors

variable (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The morphism of presheaves of modules introducing the local pure tensors of degrees `t` and
`r` into the degree-`c` term of `Tot(A ⊗_O B)`: the inclusion of the `(t, r)` summand followed
by the unit of the degreewise sheafification. -/
noncomputable def tensorTotalTmulMap (t r c : ℤ) (h : t + r = c) :
    tensorTotalPresheafTerm X A B t r ⟶ ((tensorTotal X A B).X c).val :=
  ιTensorTotalPresheaf X A B t r c h ≫
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((tensorTotalPresheaf X A B).X c)

/-- The homogeneous local pure tensor of a section of `A` of degree `t` and a section of `B` of
degree `r` over the same object, read as a section of the degree-`c` term of `Tot(A ⊗_O B)` for
any `c` with `t + r = c`. -/
noncomputable abbrev tensorTotalSectionAt (U : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal X A B).X c).val.obj (op U) :=
  (tensorTotalTmulMap X A B t r c h).app (op U)
    (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)

/-- In the degree `t + r` the transported pure tensor is
`AlgebraicGeometry.RingedSite.tensorTotalSection` itself. -/
lemma tensorTotalSectionAt_self (U : X.C) (t r : ℤ) (a : (A.X t).val.obj (op U))
    (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r (t + r) rfl a b = tensorTotalSection X A B U t r a b := rfl

variable {A B}

/-- The local pure tensor is additive in the section of `A`. -/
lemma tensorTotalSectionAt_add_left (U : X.C) (t r c : ℤ) (h : t + r = c)
    (a a' : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h (a + a') b =
      tensorTotalSectionAt X A B U t r c h a b + tensorTotalSectionAt X A B U t r c h a' b :=
  (congrArg _ (TensorProduct.add_tmul a a' b)).trans (map_add _ _ _)

/-- The local pure tensor is additive in the section of `B`. -/
lemma tensorTotalSectionAt_add_right (U : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op U)) (b b' : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a (b + b') =
      tensorTotalSectionAt X A B U t r c h a b + tensorTotalSectionAt X A B U t r c h a b' :=
  (congrArg _ (TensorProduct.tmul_add a b b')).trans (map_add _ _ _)

/-- The local pure tensor with the zero section of `B` vanishes. -/
lemma tensorTotalSectionAt_zero_right (U : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a 0 = 0 :=
  (congrArg _ (TensorProduct.tmul_zero _ a)).trans (map_zero _)

/-- The local pure tensor is linear in the section of `A`. -/
lemma tensorTotalSectionAt_smul_left (U : X.C) (t r c : ℤ) (h : t + r = c)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (a : (A.X t).val.obj (op U))
    (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h (s • a) b =
      s • tensorTotalSectionAt X A B U t r c h a b :=
  (congrArg _ (TensorProduct.smul_tmul'
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) s a b).symm).trans
    (map_smul _ _ _)

/-- The local pure tensor is linear in the section of `B`. -/
lemma tensorTotalSectionAt_smul_right (U : X.C) (t r c : ℤ) (h : t + r = c)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (a : (A.X t).val.obj (op U))
    (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a (s • b) =
      s • tensorTotalSectionAt X A B U t r c h a b :=
  (congrArg _ (TensorProduct.tmul_smul
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) s a b)).trans
    (map_smul _ _ _)

/-- The local pure tensor is compatible with restriction along an arrow of the site. -/
lemma tensorTotalSectionAt_restrict {U V : X.C} (i : V ⟶ U) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    restrictSection X i (tensorTotalSectionAt X A B U t r c h a b) =
      tensorTotalSectionAt X A B V t r c h (restrictSection X i a) (restrictSection X i b) :=
  (PresheafOfModules.naturality_apply (tensorTotalTmulMap X A B t r c h) i.op
      (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)).symm.trans
    (congrArg ((tensorTotalTmulMap X A B t r c h).app (op V))
      (PresheafOfModules.Monoidal.tensorObj_map_tmul i.op a b))

/-- The local pure tensor is linear in the section of `B` for the action of `ℤ`. This is not an
instance of `AlgebraicGeometry.RingedSite.tensorTotalSectionAt_smul_right`, whose scalars are
sections of the structure sheaf; the integers act on every sheaf of modules, and it is their
action that signs are carried by. -/
lemma tensorTotalSectionAt_zsmul_right (U : X.C) (t r c : ℤ) (h : t + r = c) (n : ℤ)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a (n • b) =
      n • tensorTotalSectionAt X A B U t r c h a b :=
  (congrArg _ (TensorProduct.tmul_smul
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) n a b)).trans
    (map_zsmul _ _ _)

/-- **The degree of the second factor can be renamed.** Transporting a section of `B` from the
degree `r'` to an equal degree `r` and then forming the pure tensor is forming the pure tensor
in the degree `r'`. The transport is invisible in the pure tensor, and this is how it is
removed: a comparison of complexes built from `B` arrives with its degrees named one way and
the pure tensors it must be tested against have them named another. -/
lemma tensorTotalSectionAt_congr_right (U : X.C) (t r r' c : ℤ) (h : t + r = c) (e : r' = r)
    (h' : t + r' = c) (a : (A.X t).val.obj (op U)) (b : (B.X r').val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a ((B.XIsoOfEq e).hom.val.app (op U) b) =
      tensorTotalSectionAt X A B U t r' c h' a b := by
  subst e
  simp

/-- The local pure tensor is linear in the section of `B` for the action of the units of `ℤ`.
This is the form in which signs appear: `Int.negOnePow` is valued in `ℤˣ`. -/
lemma tensorTotalSectionAt_units_smul_right (U : X.C) (t r c : ℤ) (h : t + r = c) (u : ℤˣ)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a (u • b) =
      u • tensorTotalSectionAt X A B U t r c h a b := by
  rw [Units.smul_def, Units.smul_def, tensorTotalSectionAt_zsmul_right]

/-- **The total degree can be renamed.** Transporting a pure tensor along an equality of total
degrees is the pure tensor read in the other degree. Together with
`AlgebraicGeometry.RingedSite.tensorTotalSectionAt_congr_right` this is what makes the free
degree parameter of `AlgebraicGeometry.RingedSite.tensorTotalSectionAt` useful: no `eqToHom`
survives a computation stated in terms of these. -/
lemma tensorTotalSectionAt_XIsoOfEq (U : X.C) (t r c c' : ℤ) (h : t + r = c) (e : c = c')
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal X A B).XIsoOfEq e).hom.val.app (op U)
        (tensorTotalSectionAt X A B U t r c h a b) =
      tensorTotalSectionAt X A B U t r c' (by omega) a b := by
  subst e
  simp

/-- **The total degree can be renamed, in the other direction.** The inverse of the transport
along an equality of total degrees acts on the pure tensors the same way, the two degrees being
equal; it is a separate statement only because the two transports are separate terms. -/
lemma tensorTotalSectionAt_XIsoOfEq_inv (U : X.C) (t r c c' : ℤ) (h : t + r = c') (e : c = c')
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal X A B).XIsoOfEq e).inv.val.app (op U)
        (tensorTotalSectionAt X A B U t r c' h a b) =
      tensorTotalSectionAt X A B U t r c (by omega) a b := by
  subst e
  simp

/-- `tensorTotalMap` sends a local pure tensor to the pure tensor of the images of its two
factors. -/
lemma tensorTotalMap_tensorTotalSectionAt
    {A' B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B')
    (U : X.C) (t r c : ℤ) (h : t + r = c) (a : (A.X t).val.obj (op U))
    (b : (B.X r).val.obj (op U)) :
    ((tensorTotalMap X f g).f c).val.app (op U) (tensorTotalSectionAt X A B U t r c h a b) =
      tensorTotalSectionAt X A' B' U t r c h ((f.f t).val.app (op U) a)
        ((g.f r).val.app (op U) b) := by
  subst h
  exact tensorTotalMap_tensorTotalSection X f g U t r a b

/-- A unit multiple of a morphism of presheaves of modules acts degreewise by the corresponding
integer multiple. -/
private lemma presheaf_units_zsmul_app
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    (f : P ⟶ Q) (n : ℤˣ) (U : X.Cᵒᵖ) : (n • f).app U = (n : ℤ) • f.app U := by
  rw [Units.smul_def]
  exact PresheafOfModules.zsmul_app (n : ℤ) f U

/-- **The differential of the presheaf-level total tensor complex on a summand.** On the
`(t, r)` summand of the degree-`c` term the differential is `dA ⊗ 1` into the `(t + 1, r)`
summand plus `(-1)^t` times `1 ⊗ dB` into the `(t, r + 1)` summand; the two Koszul signs are
the `ε₁ = 1` and `ε₂ = (-1)^t` of the total complex of a bicomplex. -/
lemma ιTensorTotalPresheaf_comp_d (t r c c' : ℤ) (h : t + r = c) (hc : c + 1 = c') :
    ιTensorTotalPresheaf X A B t r c h ≫ (tensorTotalPresheaf X A B).d c c' =
      ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
            ((underlyingPresheafComplex X A).d t (t + 1))).app
            ((underlyingPresheafComplex X B).X r) ≫
          ιTensorTotalPresheaf X A B (t + 1) r c' (by omega) +
        t.negOnePow •
          (((curriedTensor
                (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
                ((underlyingPresheafComplex X A).X t)).map
              ((underlyingPresheafComplex X B).d r (r + 1)) ≫
            ιTensorTotalPresheaf X A B t (r + 1) c' (by omega)) := by
  subst h
  subst hc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.up_mk t (t + 1) rfl) r
      (t + r + 1) (by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ t (ComplexShape.up_mk r (r + 1) rfl)
      (t + r + 1) (by simp; omega)]
  have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r) = t.negOnePow := rfl
  rw [hε₁, hε₂, one_smul]

/-- `AlgebraicGeometry.RingedSite.ιTensorTotalPresheaf_comp_d` transported across the
degreewise sheafification, by naturality of its unit. -/
lemma tensorTotalTmulMap_comp_d (t r c c' : ℤ) (h : t + r = c) (hc : c + 1 = c') :
    tensorTotalTmulMap X A B t r c h ≫ ((tensorTotal X A B).d c c').val =
      ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
            ((underlyingPresheafComplex X A).d t (t + 1))).app
            ((underlyingPresheafComplex X B).X r) ≫
          tensorTotalTmulMap X A B (t + 1) r c' (by omega) +
        t.negOnePow •
          (((curriedTensor
                (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
                ((underlyingPresheafComplex X A).X t)).map
              ((underlyingPresheafComplex X B).d r (r + 1)) ≫
            tensorTotalTmulMap X A B t (r + 1) c' (by omega)) := by
  have hunit : (PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((tensorTotalPresheaf X A B).X c) ≫ ((tensorTotal X A B).d c c').val =
      (tensorTotalPresheaf X A B).d c c' ≫
        (PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((tensorTotalPresheaf X A B).X c') :=
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality
      ((tensorTotalPresheaf X A B).d c c')).symm
  refine Eq.trans (Category.assoc (ιTensorTotalPresheaf X A B t r c h)
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((tensorTotalPresheaf X A B).X c)) ((tensorTotal X A B).d c c').val) ?_
  rw [hunit]
  refine Eq.trans (Category.assoc (ιTensorTotalPresheaf X A B t r c h)
    ((tensorTotalPresheaf X A B).d c c')
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((tensorTotalPresheaf X A B).X c'))).symm ?_
  rw [ιTensorTotalPresheaf_comp_d X t r c c' h hc, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc, Category.assoc]
  rfl

/-- **The Koszul Leibniz rule for the local pure tensors.** The differential of `Tot(A ⊗_O B)`
takes the pure tensor of a section `a` of `A^t` and a section `b` of `B^r` to
`(da) ⊗ b + (-1)^t a ⊗ (db)`. -/
lemma tensorTotalSectionAt_d (U : X.C) (t r c c' : ℤ) (h : t + r = c) (hc : c + 1 = c')
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal X A B).d c c').val.app (op U) (tensorTotalSectionAt X A B U t r c h a b) =
      tensorTotalSectionAt X A B U (t + 1) r c' (by omega)
          ((A.d t (t + 1)).val.app (op U) a) b +
        t.negOnePow • tensorTotalSectionAt X A B U t (r + 1) c' (by omega) a
          ((B.d r (r + 1)).val.app (op U) b) := by
  have key := congrArg (fun φ : tensorTotalPresheafTerm X A B t r ⟶
      ((tensorTotal X A B).X c').val ↦ φ.app (op U))
    (tensorTotalTmulMap_comp_d X t r c c' h hc)
  rw [PresheafOfModules.add_app, presheaf_units_zsmul_app] at key
  refine Eq.trans (congrArg
    (fun g ↦ (ConcreteCategory.hom g)
      (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) key) ?_
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, Units.smul_def]
  rfl

end PureTensors


/-! ## The diagonal sections -/

section Diagonal

variable {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The map on sections underlying `AlgebraicGeometry.RingedSite.diagonalSliceMap`: over an
object `W` of the slice site over `U` it sends a section `l` of `L^p` to the pure tensor of the
restriction of the fixed section `k` of `K^n` with `l`. -/
noncomputable def diagonalSlicePresheafMap (U : X.C) (n p q : ℤ) (hnpq : n + p = q)
    (k : (K.X n).val.obj (op U)) :
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        (L.X p)).val.presheaf ⟶
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        ((tensorTotal X K L).X q)).val.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun l ↦ tensorTotalSectionAt X K L W.unop.left n p q hnpq
        (restrictSection X W.unop.hom k) l
      map_zero' := tensorTotalSectionAt_zero_right X W.unop.left n p q hnpq _
      map_add' := fun l l' ↦ tensorTotalSectionAt_add_right X W.unop.left n p q hnpq _ l l' }
  naturality := by
    intro W Z g
    ext l
    have hk : restrictSection X Z.unop.hom k =
        restrictSection X g.unop.left (restrictSection X W.unop.hom k) := by
      rw [← restrictSection_comp, Over.w g.unop]
    change tensorTotalSectionAt X K L Z.unop.left n p q hnpq
        (restrictSection X Z.unop.hom k) ((L.X p).val.map g.unop.left.op l) =
      ((tensorTotal X K L).X q).val.map g.unop.left.op
        (tensorTotalSectionAt X K L W.unop.left n p q hnpq
          (restrictSection X W.unop.hom k) l)
    exact (congrArg (fun z ↦ tensorTotalSectionAt X K L Z.unop.left n p q hnpq z
          ((L.X p).val.map g.unop.left.op l)) hk).trans
      (tensorTotalSectionAt_restrict X g.unop.left n p q hnpq
        (restrictSection X W.unop.hom k) l).symm

/-- The component at an object of the slice site over `U` of the homogeneous local section of
`SheafHom(L, Tot(K ⊗_O L))` determined by a section `k` of `K^n`: the morphism of sheaves of
`O|_U`-modules sending `l` to `k ⊗ l`. -/
noncomputable def diagonalSliceMap (U : X.C) (n p q : ℤ) (hnpq : n + p = q)
    (k : (K.X n).val.obj (op U)) :
    (restrictComplex X L U).X p ⟶ (restrictComplex X (tensorTotal X K L) U).X q :=
  ⟨PresheafOfModules.homMk (diagonalSlicePresheafMap X U n p q hnpq k) (fun W s l ↦
    tensorTotalSectionAt_smul_right X W.unop.left n p q hnpq s _ l)⟩

/-- `diagonalSliceMap` sends a local section of `L` to its pure tensor with the restriction of
the fixed section of `K`. -/
lemma diagonalSliceMap_app (U : X.C) (n p q : ℤ) (hnpq : n + p = q)
    (k : (K.X n).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (l : ((restrictComplex X L U).X p).val.obj W) :
    (diagonalSliceMap X U n p q hnpq k).val.app W l =
      tensorTotalSectionAt X K L W.unop.left n p q hnpq
        (restrictSection X W.unop.hom k) l := rfl

/-- The degree-`n` cochain from `L|_U` to `Tot(K ⊗_O L)|_U` determined by a section `k` of `K^n`
over `U`: in degree `p` it is the pure tensor with `k`. -/
noncomputable def diagonalCochain (U : X.C) (n : ℤ) (k : (K.X n).val.obj (op U)) :
    Cochain (restrictComplex X L U) (restrictComplex X (tensorTotal X K L) U) n :=
  Cochain.mk fun p q hpq ↦ diagonalSliceMap X U n p q (by omega) k

/-- The components of `diagonalCochain`, evaluated on a local section of `L`. -/
lemma diagonalCochain_app (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X n).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (l : ((restrictComplex X L U).X p).val.obj W) :
    ((diagonalCochain X U n (L := L) k).v p q hpq).val.app W l =
      tensorTotalSectionAt X K L W.unop.left n p q (by omega)
        (restrictSection X W.unop.hom k) l := rfl

/-- The degree-`n` section of `SheafHom(L, Tot(K ⊗_O L))` over `U` determined by a section `k`
of `K^n` over `U`. -/
noncomputable def diagonalHomSection (U : X.C) (n : ℤ) (k : (K.X n).val.obj (op U)) :
    ((sheafHomComplex X L (tensorTotal X K L)).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X L (tensorTotal X K L)).sectionsEquiv U n).symm (diagonalCochain X U n k)

/-- The cochain of `diagonalHomSection` is `diagonalCochain`. -/
lemma diagonalHomSection_cochain (U : X.C) (n : ℤ) (k : (K.X n).val.obj (op U)) :
    (sheafHomComplex X L (tensorTotal X K L)).sectionsEquiv U n
        (diagonalHomSection X U n k) = diagonalCochain X U n k :=
  ((sheafHomComplex X L (tensorTotal X K L)).sectionsEquiv U n).apply_symm_apply _

/-- Evaluating `diagonalHomSection` on a section of `L` over an object of the slice site over
`U` gives the pure tensor with the restriction of `k`. -/
lemma diagonalHomSection_applyOver (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X n).val.obj (op U)) (l : (L.X p).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X L (tensorTotal X K L)) U V i n p q hpq
        (diagonalHomSection X U n k) l =
      tensorTotalSectionAt X K L V n p q (by omega) (restrictSection X i k) l :=
  (congrArg (fun z : Cochain _ _ n ↦ ((z.v p q hpq).val.app (op (Over.mk i))) l)
      (diagonalHomSection_cochain X U n k)).trans
    (diagonalCochain_app X U n p q hpq k (op (Over.mk i)) l)

/-- Evaluating `diagonalHomSection` on a section of `L` over `U` gives the pure tensor
with `k`. -/
lemma diagonalHomSection_apply (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X n).val.obj (op U)) (l : (L.X p).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X L (tensorTotal X K L)) U n p q hpq
        (diagonalHomSection X U n k) l =
      tensorTotalSectionAt X K L U n p q (by omega) k l := by
  rw [applyHomSection, diagonalHomSection_applyOver, restrictSection_id]

/-- `diagonalHomSection` is additive in the section of `K`. -/
lemma diagonalHomSection_add (U : X.C) (n : ℤ) (k k' : (K.X n).val.obj (op U)) :
    diagonalHomSection X U n (L := L) (k + k') =
      diagonalHomSection X U n (L := L) k + diagonalHomSection X U n (L := L) k' := by
  refine homSection_ext X (sheafHomComplex X L (tensorTotal X K L)) U n
    fun p q hpq V i l ↦ ?_
  rw [applyHomSectionOver_add_left, diagonalHomSection_applyOver,
    diagonalHomSection_applyOver, diagonalHomSection_applyOver, restrictSection_add,
    tensorTotalSectionAt_add_left]

/-- `diagonalHomSection` is `O(U)`-linear in the section of `K`. -/
lemma diagonalHomSection_smul (U : X.C) (n : ℤ)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (k : (K.X n).val.obj (op U)) :
    diagonalHomSection X U n (L := L) (s • k) = s • diagonalHomSection X U n (L := L) k := by
  refine homSection_ext X (sheafHomComplex X L (tensorTotal X K L)) U n
    fun p q hpq V i l ↦ ?_
  rw [applyHomSectionOver_smul_left, diagonalHomSection_applyOver,
    diagonalHomSection_applyOver, restrictSection_smul, tensorTotalSectionAt_smul_left]

/-- `diagonalHomSection` is compatible with restriction along an arrow of the site. -/
lemma diagonalHomSection_restrict (U V : X.C) (i : V ⟶ U) (n : ℤ)
    (k : (K.X n).val.obj (op U)) :
    restrictSection X i (diagonalHomSection X U n (L := L) k) =
      diagonalHomSection X V n (restrictSection X i k) := by
  refine homSection_ext X (sheafHomComplex X L (tensorTotal X K L)) V n
    fun p q hpq W g l ↦ ?_
  rw [← applyHomSectionOver_restrict_comp X (sheafHomComplex X L (tensorTotal X K L)) U V W i g
      n p q hpq (diagonalHomSection X U n k) l,
    diagonalHomSection_applyOver, diagonalHomSection_applyOver, restrictSection_comp]

/-- **The Leibniz rule for the diagonal sections.** The differential of
`SheafHom(L, Tot(K ⊗_O L))` takes the diagonal section of `k` to the diagonal section of `dk`:
the Koszul sign of the Hom complex cancels the one of the tensor complex. -/
lemma diagonalHomSection_d (U : X.C) (n : ℤ) (k : (K.X n).val.obj (op U)) :
    ((sheafHomComplex X L (tensorTotal X K L)).obj.d n (n + 1)).val.app (op U)
        (diagonalHomSection X U n k) =
      diagonalHomSection X U (n + 1) ((K.d n (n + 1)).val.app (op U) k) := by
  refine homSection_ext X (sheafHomComplex X L (tensorTotal X K L)) U (n + 1)
    fun p q hpq V i l ↦ ?_
  rw [applyHomSectionOver_differential X (sheafHomComplex X L (tensorTotal X K L)) U V i n p
      (p + n) q rfl (by omega) (diagonalHomSection X U n k) l,
    diagonalHomSection_applyOver, diagonalHomSection_applyOver,
    diagonalHomSection_applyOver,
    tensorTotalSectionAt_d X V n p (p + n) q (by omega) (by omega),
    restrictSection_natural X (K.d n (n + 1)) i k, Int.negOnePow_succ, Units.neg_smul]
  exact add_neg_cancel_right _ _

end Diagonal

/-! ## The diagonal morphism -/

section Morphism

variable (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The degree-`n` component of the diagonal morphism: it sends a section `k` of `K^n` to the
section `l ↦ k ⊗ l` of `SheafHom(L, Tot(K ⊗_O L))^n`. -/
noncomputable def diagonalHom (n : ℤ) :
    K.X n ⟶ (sheafHomComplex X L (tensorTotal X K L)).obj.X n :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
      { toFun := fun k ↦ diagonalHomSection X U.unop n k
        map_add' := fun k k' ↦ diagonalHomSection_add X U.unop n k k'
        map_smul' := fun s k ↦ diagonalHomSection_smul X U.unop n s k }
     naturality := by
       rintro ⟨U⟩ ⟨V⟩ ⟨i : V ⟶ U⟩
       exact ModuleCat.hom_ext <| LinearMap.ext fun k ↦
         (diagonalHomSection_restrict X U V i n (L := L) k).symm }⟩

/-- **The diagonal morphism** `K ⟶ SheafHom(L, Tot(K ⊗_O L))` of Stacks 0A93, assembled from
the homogeneous local sections `l ↦ k ⊗ l`. -/
noncomputable def diagonalMap : K ⟶ (sheafHomComplex X L (tensorTotal X K L)).obj where
  f n := diagonalHom X K L n
  comm' n n' hnn := by
    obtain rfl : n + 1 = n' := hnn
    exact SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext <| LinearMap.ext fun k ↦ diagonalHomSection_d X U.unop n (L := L) k

/-- The degreewise components of `diagonalMap` act by `diagonalHomSection`. -/
lemma diagonalMap_apply (U : X.C) (n : ℤ) (k : (K.X n).val.obj (op U)) :
    ((diagonalMap X K L).f n).val.app (op U) k = diagonalHomSection X U n k := rfl

/-- **The characterisation of the diagonal morphism**: it sends a section `k` of `K^n` over `U`
to the homogeneous local section of `SheafHom(L, Tot(K ⊗_O L))` taking a section `l` of `L^p`
to the pure tensor `k ⊗ l`. -/
lemma diagonalMap_applyHomSection (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X n).val.obj (op U)) (l : (L.X p).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X L (tensorTotal X K L)) U n p q hpq
        (((diagonalMap X K L).f n).val.app (op U) k) l =
      tensorTotalSectionAt X K L U n p q (by omega) k l :=
  diagonalHomSection_apply X U n p q hpq k l

end Morphism

/-- A diagonal morphism of Stacks 0A93, characterised by its action on every homogeneous local
section: a section `k` of `K^n` over `U` is sent to the section of `SheafHom(L, Tot(K ⊗_O L))`
taking a section `l` of `L^p` to the pure tensor `k ⊗ l` in degree `n + p`. -/
structure DiagonalConstruction where
  /-- The morphism of complexes of `O`-modules given by the diagonal. -/
  diagonal
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    K ⟶ (sheafHomComplex X L (tensorTotal X K L)).obj
  /-- Homogeneous local sections act by formation of the pure tensor. -/
  diagonal_apply :
    ∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (U : X.C) (n p q : ℤ) (hpq : p + n = q) (k : (K.X n).val.obj (op U))
      (l : (L.X p).val.obj (op U)),
    applyHomSection X (sheafHomComplex X L (tensorTotal X K L)) U n p q hpq
        (((diagonal K L).f n).val.app (op U) k) l =
      tensorTotalSectionAt X K L U n p q (by omega) k l

/-- **Stacks 0A93.** For complexes `K`, `L` of modules on a ringed site there is a canonical
morphism of complexes of `O`-modules

`K ⟶ SheafHom(L, Tot(K ⊗_O L))`,

namely the one sending each homogeneous local section `k` of `K` to the local section
`l ↦ k ⊗ l` of the internal Hom complex. -/
@[stacks 0A93 "canonical diagonal morphism"]
noncomputable def diagonalConstruction : DiagonalConstruction X where
  diagonal K L := diagonalMap X K L
  diagonal_apply K L U n p q hpq k l := diagonalMap_applyHomSection X K L U n p q hpq k l

section Natural

variable {K K' L L' :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Stacks 0A93.** The diagonal morphism is natural in `K` and dinatural in `L`: a morphism
`g : L ⟶ L'` acts covariantly inside the tensor product and contravariantly in the source of
the internal Hom. -/
@[stacks 0A93 "functoriality in both complexes"]
theorem diagonalMap_natural (f : K ⟶ K') (g : L ⟶ L') :
    diagonalMap X K L ≫ homMap X (𝟙 L) (tensorTotalMap X f g) =
      f ≫ diagonalMap X K' L' ≫ homMap X g (𝟙 (tensorTotal X K' L')) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro k
  refine homSection_ext X (sheafHomComplex X L (tensorTotal X K' L')) U n
    fun p q hpq V i l ↦ ?_
  rw [HomologicalComplex.comp_f, AlgebraicGeometry.RingedSite.comp_val_app_apply',
    applyHomSectionOver_homMap X (𝟙 L) (tensorTotalMap X f g) U V i n p q hpq _ l,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AlgebraicGeometry.RingedSite.comp_val_app_apply',
    AlgebraicGeometry.RingedSite.comp_val_app_apply',
    applyHomSectionOver_homMap X g (𝟙 (tensorTotal X K' L')) U V i n p q hpq _ l,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app]
  rw [diagonalMap_apply, diagonalMap_apply, diagonalHomSection_applyOver,
    diagonalHomSection_applyOver, tensorTotalMap_tensorTotalSectionAt,
    restrictSection_natural X (f.f n) i k]
  rfl

end Natural

end AlgebraicGeometry.RingedSite

end
