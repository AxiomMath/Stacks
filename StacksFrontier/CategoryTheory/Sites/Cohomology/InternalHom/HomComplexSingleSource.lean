module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandDerivedHom

/-!
# The internal Hom complex out of a source concentrated in one degree

Let `(C, O)` be a ringed site and let `E` be a cochain complex of `O`-modules concentrated in a
single degree `k`. A degree-`n` section of the internal Hom complex `SheafHom(E, F)` of
[Stacks, Tag 0A8Z] is a degree-`n` cochain from `E|_U` to `F|_U`, and such a cochain has only
one possibly nonzero component, the one in bidegree `(k, k + n)`. So

`SheafHom(E, F)^n = SheafHom(E^k, F^{k+n})`

degreewise, by reading off that component. When the target is also concentrated in degree zero
and `k = 0` the differentials vanish on both sides and the whole complex collapses:

`SheafHom(A[0], B[0]) = SheafHom(A, B)[0]`.

Combined with [Stacks, Tag 08JH] in the form available for a source which is only *locally* a
direct summand of a finite free module
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isInvertible`) this gives
the derived statement **an invertible sheaf of modules is its own derived dual**:

`R SheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` in `D(Mod(O))` for `A` invertible.

At `B = O` the right-hand side is the dual sheaf `A^∨`, so the derived dual of an invertible
sheaf of modules is its underived dual, with no shift and no higher Ext sheaves.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComponent`: the bidegree-`(k, k + n)` component of a
  degree-`n` section of the internal Hom complex, as a morphism of sheaves of modules
  `SheafHom(E, F)^n ⟶ SheafHom(E^k, F^{k+n})`.
* `AlgebraicGeometry.RingedSite.homComponentIso`: that morphism as an isomorphism, for a source
  concentrated in degree `k`.
* `AlgebraicGeometry.RingedSite.sheafHomComplexSingleIso`: the collapse
  `SheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible`: the derived form
  `R SheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` for `A` invertible.

## Main results

* `AlgebraicGeometry.RingedSite.homComponent_isIso`: reading off the bidegree-`(k, k + n)`
  component is an isomorphism when the source is concentrated in degree `k`.
* `AlgebraicGeometry.RingedSite.isZero_internalHomSheaf`: the internal Hom sheaf into a zero
  object is zero.
* `AlgebraicGeometry.RingedSite.single_homComplex_d`: the internal Hom complex of two sheaves
  placed in degree zero has vanishing differentials.

## Implementation notes

`AlgebraicGeometry.RingedSite.homUnitEvaluation` is the special case `E^k ≅ O` of
`homComponent`, where the component is further evaluated at the unit section and the target is
`F^{k+n}` itself rather than an internal Hom sheaf out of it. This file repeats the
construction without that evaluation, because the geometry supplies invertible sources rather
than free ones: on `P^1` there is no nonzero morphism `O(1) ⟶ O^{⊕n}`, so the unit case does not
apply to the ideal sheaf of an effective Cartier divisor.

The internal Hom complex is reached only through the characterising data of
`AlgebraicGeometry.RingedSite.SheafHomComplex`, so the component morphism is built from the
local description `sectionsIso` of its sections as cochains; its `O`-linearity and its
compatibility with restriction are the `smul_natural` and `restrict_natural` clauses of that
structure, applied in the single bidegree `(k, k + n)`. Sections of `internalHomSheaf X A B`
over `U` are, definitionally, morphisms of presheaves of modules `A|_U ⟶ B|_U` on the slice
site, which is also what the cochain component is once its sheaf-morphism wrapper is removed;
that is why the three bijections composing to `homComponent_isIso` end in a wrapper-stripping
equivalence rather than in a computation.

The collapse `sheafHomComplexSingleIso` is an isomorphism of components together with the
vanishing of both differentials: the target's by `HomologicalComplex.single_obj_d`, the
source's by `AlgebraicGeometry.RingedSite.SheafHomComplex.d_eq_zero_of_single`, whose
hypothesis is discharged because a complex concentrated in one degree has zero differentials
and evaluation of a Hom section is additive in the section of the source.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
variable {E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The `(k, k + n)` component of a degree-`n` section of the internal Hom complex. -/
def homComponent (k n : ℤ) :
    (sheafHomComplex X E F).obj.X n ⟶ internalHomSheaf X (E.X k) (F.X (k + n)) where
  val := PresheafOfModules.Hom.mk
    (fun U =>
      letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
          ((restrFun X.O.obj U.unop).obj (valOf X (E.X k)) ⟶
            (restrFun X.O.obj U.unop).obj (valOf X (F.X (k + n)))) :=
        homModule X.O.obj (valOf X (E.X k)) (valOf X (F.X (k + n))) U.unop
      ModuleCat.ofHom
        { toFun := fun s =>
            ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
              s).v k (k + n) rfl).val
          map_add' := fun a b =>
            congrArg (fun c : Cochain (restrictComplex X E U.unop)
                (restrictComplex X F U.unop) n => (c.v k (k + n) rfl).val)
              (map_add (AddCommGrpCat.Hom.hom
                (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b)
          map_smul' := by
            intro r s
            ext V x
            exact (sheafHomComplex X E F).smul_natural U.unop r n k (k + n) rfl s
              V.unop.hom x })
    (fun {U V} a => ModuleCat.hom_ext <| LinearMap.ext fun s => by
      change (_ : (restrFun X.O.obj V.unop).obj (valOf X (E.X k)) ⟶
        (restrFun X.O.obj V.unop).obj (valOf X (F.X (k + n)))) = _
      ext W x
      exact ((sheafHomComplex X E F).restrict_natural a.unop n k (k + n) rfl s
        W.unop.hom x).symm)

/-- A degree-`n` cochain out of a complex concentrated in degree `k` is one morphism. -/
private def cochainSingleSourceEquiv {A : Type*} [Category A] [Preadditive A]
    (E' F' : CochainComplex A ℤ) (k n : ℤ) (hE : ∀ p, p ≠ k → IsZero (E'.X p)) :
    Cochain E' F' n ≃ (E'.X k ⟶ F'.X (k + n)) where
  toFun c := c.v k (k + n) rfl
  invFun f := Cochain.single f n
  left_inv c := by
    ext p q hpq
    by_cases hp : p = k
    · subst p
      subst q
      simp
    · exact (hE p hp).eq_of_src _ _
  right_inv f := Cochain.single_v f n rfl

/-- If `E` is concentrated in degree `k`, then `homComponent` is an isomorphism. -/
theorem homComponent_isIso (k n : ℤ) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    IsIso (homComponent X (E := E) (F := F) k n) := by
  let t := homComponent X (E := E) (F := F) k n
  have ht (U : X.Cᵒᵖ) : IsIso (t.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e₁ := (HomologicalComplex.Hom.isoApp
      ((sheafHomComplex X E F).sectionsIso U.unop) n).addCommGroupIsoToAddEquiv.toEquiv
    let e₂ := cochainSingleSourceEquiv (restrictComplex X E U.unop)
      (restrictComplex X F U.unop) k n
      (fun p hp => (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U.unop).map_isZero (hE p hp))
    let e₃ : ((restrictComplex X E U.unop).X k ⟶ (restrictComplex X F U.unop).X (k + n)) ≃
        ((internalHomSheaf X (E.X k) (F.X (k + n))).val.obj U) :=
      { toFun := fun f => f.val
        invFun := fun g => ⟨g⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact ((e₁.trans e₂).trans e₃).bijective
  let e' := PresheafOfModules.isoMk (fun U => asIso (t.val.app U))
    (fun _ _ g => t.val.naturality g)
  have : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map t) :=
    show IsIso e'.hom from inferInstance
  exact isIso_of_reflects_iso t (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The degree-`n` term of the internal Hom complex out of a source concentrated in degree `k`
is the internal Hom sheaf from that term into the degree-`k + n` term of the target. -/
def homComponentIso (k n : ℤ) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj.X n ≅ internalHomSheaf X (E.X k) (F.X (k + n)) :=
  @asIso _ _ _ _ (homComponent X (E := E) (F := F) k n) (homComponent_isIso X k n hE)

/-- The internal Hom sheaf into a zero object is zero. -/
theorem isZero_internalHomSheaf
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hB : IsZero B) :
    IsZero (internalHomSheaf X A B) := by
  rw [IsZero.iff_id_eq_zero]
  refine SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext <| LinearMap.ext fun s => ?_
  have hz : IsZero ((B.over U.unop).val) :=
    (SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U.unop)).map_isZero
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U.unop).map_isZero hB)
  exact hz.eq_of_tgt _ _

section Single

variable (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A sheaf of modules placed in degree zero. -/
abbrev sgl (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).obj M

/-- A sheaf of modules placed in degree zero has zero terms in every nonzero degree. -/
theorem isZero_sgl_X (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℤ)
    (hp : p ≠ 0) :
    IsZero ((sgl X M).X p) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp

/-- The internal Hom complex of two sheaves placed in degree zero has vanishing differentials:
the source has zero differentials, and evaluating a Hom section is additive in the section of
the source. -/
theorem single_homComplex_d (n : ℤ) :
    (sheafHomComplex X (sgl X A) (sgl X B)).obj.d n (n + 1) = 0 := by
  refine SheafHomComplex.d_eq_zero_of_single X B (sheafHomComplex X (sgl X A) (sgl X B))
    (fun U V i m p hp f x => ?_) n
  have hzero : ((sgl X A).d p (p + 1)).val.app (op V) x = 0 := by
    rw [HomologicalComplex.single_obj_d]
    exact Stacks.SheafOfModules.zero_val_app_apply _ _
  rw [hzero]
  have hadd := applyHomSectionOver_add_right X (sheafHomComplex X (sgl X A) (sgl X B))
    U V i m (p + 1) 0 (by omega) f 0 0
  simpa using hadd.symm

/-- The degree-`n` term of the internal Hom complex of two sheaves placed in degree zero is the
degree-`n` term of their internal Hom sheaf placed in degree zero: the internal Hom sheaf in
degree zero and zero elsewhere. -/
def singleComponentIso (n : ℤ) :
    (sheafHomComplex X (sgl X A) (sgl X B)).obj.X n ≅ (sgl X (internalHomSheaf X A B)).X n := by
  by_cases hn : n = 0
  · subst hn
    exact homComponentIso X 0 0 (isZero_sgl_X X A)
  · exact (IsZero.of_iso
        (isZero_internalHomSheaf X A (isZero_sgl_X X B (0 + n) (by omega)))
        (homComponentIso X 0 n (isZero_sgl_X X A))).isoZero ≪≫
      (isZero_sgl_X X (internalHomSheaf X A B) n hn).isoZero.symm

/-- **The internal Hom complex of two sheaves placed in degree zero is their internal Hom
sheaf, placed in degree zero.** -/
def sheafHomComplexSingleIso :
    (sheafHomComplex X (sgl X A) (sgl X B)).obj ≅ sgl X (internalHomSheaf X A B) :=
  HomologicalComplex.Hom.isoOfComponents (singleComponentIso X A B) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [single_homComplex_d, HomologicalComplex.single_obj_d]
    simp)

section Derived

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **An invertible sheaf of modules is its own derived dual, in the single-complex form.** -/
def derivedSheafHomSingleIsoOfIsInvertible
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property A] :
    (D.hom.obj (op (DerivedCategory.Q.obj (sgl X A)))).obj (DerivedCategory.Q.obj (sgl X B)) ≅
      DerivedCategory.Q.obj (sgl X (internalHomSheaf X A B)) :=
  (@asIso _ _ _ _ (strictlyPerfectHomComparison X D (sgl X A) (sgl X B))
      (strictlyPerfectHomComparison_isIso_of_isInvertible X D 0 A (sgl X B))).symm ≪≫
    DerivedCategory.Q.mapIso (sheafHomComplexSingleIso X A B)

end Derived

end Single

end AlgebraicGeometry.RingedSite

end
