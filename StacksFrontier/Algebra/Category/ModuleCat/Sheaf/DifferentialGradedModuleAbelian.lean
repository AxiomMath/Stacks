module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# Differential graded modules form an abelian category

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. [Stacks, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ) says that the
category `Mod(A, d)` of right differential graded `A`-modules is abelian.

This file proves that. The category and the forgetful functor to right graded modules are those
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean`; what is added here
is the preadditive structure, the degreewise kernels and cokernels, and the abelian structure
they produce.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homZero`,
  `SheafOfModules.DifferentialGradedModule.homAdd`,
  `SheafOfModules.DifferentialGradedModule.homNeg` and
  `SheafOfModules.DifferentialGradedModule.homAddCommGroup` are the additive structure on a
  hom-type, taken degreewise from the underlying cochain complexes; they make
  `DifferentialGradedModule A` preadditive, and
  `SheafOfModules.DifferentialGradedModule.add_f`, `zero_f` and `neg_f` record that each of the
  three is degreewise.

## Main results

* `SheafOfModules.DifferentialGradedModule.abelian` is Tag 0FRJ's assertion that `Mod(A, d)` is
  abelian.
* `SheafOfModules.DifferentialGradedModule.hasKernels` and
  `SheafOfModules.DifferentialGradedModule.hasCokernels` say that differential graded modules
  have kernels and cokernels, and both are formed degreewise: the kernel (resp. cokernel) of the
  underlying graded morphism carries a unique differential making the inclusion (resp.
  projection) a morphism of differential graded modules.
  `SheafOfModules.DifferentialGradedModule.hasEqualizers` is the equalizer form of the first.
* `SheafOfModules.DifferentialGradedModule.hasFiniteProducts` says that differential graded
  modules have finite products; they too are formed degreewise.
* `SheafOfModules.DifferentialGradedModule.isIso_of_componentwise`: a morphism of differential
  graded modules all of whose homogeneous components are isomorphisms is an isomorphism.
  Equivalently `SheafOfModules.forgetToGradedModule_reflectsIsomorphisms`.
* `SheafOfModules.DifferentialGradedModule.isIso_coimageImageComparison`: the coimage-image
  comparison of a morphism of differential graded modules is an isomorphism, which is what makes
  the category abelian.
* `SheafOfModules.forgetToGradedModule_additive` says that forgetting the differential is an
  additive functor, and `SheafOfModules.forgetToGradedModule_comonadic` that it is a comonadic
  left adjoint.
* `SheafOfModules.cokernel_isLocallySurjective`: the projection onto a cokernel of sheaves of
  modules is locally surjective.

## Implementation notes

**The base.** The base is an arbitrary sheaf of rings `R` on an arbitrary site rather than the
structure sheaf of a ringed site, and the universes of the site, the ring, the algebra pieces
and the module pieces are independent. A ringed site `X` is the case `R := X.ringSheaf`; nothing
below uses any property of the site beyond the two sheafification hypotheses discussed next.

**The sheafification hypotheses.** Tag 0FRJ defers the exactness of `Mod(O)` to Cohomology on
Sites, resting on the standing convention that a site admits sheafification. In Lean that
convention is not automatic, and the two conditions that make `SheafOfModules.{m} R` abelian —
`HasSheafify J AddCommGrpCat.{m}` and `J.WEqualsLocallyBijective AddCommGrpCat.{m}` — are
therefore hypotheses, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`. They are assumed only
where they are used: cokernels of differential graded modules need them, because a cokernel of
sheaves of modules is a sheafification and the degreewise cokernel of the underlying graded
module exists only under them, while kernels and the preadditive structure need nothing.

**Kernels, cokernels and finite products, degreewise.** Each of the three is obtained from the
corresponding statement for graded modules by lifting the differential. For the kernel the
degreewise inclusion is a monomorphism, so the differential of the ambient module restricts
uniquely; for the cokernel the degreewise projection is an epimorphism, so it descends uniquely.
In both cases the resulting cochain complex automatically satisfies the Leibniz rule and the
universal property, because a graded factorization through the degreewise kernel or cokernel
commutes with the differential for the same reason. Verifying the Leibniz rule for the cokernel
is the one place where a section of the cokernel cannot be named: it has one only locally, which
is why `SheafOfModules.cokernel_isLocallySurjective` is proved and the Leibniz identity is
checked on a covering sieve and glued by separatedness of the cokernel.

Finite products are not constructed by hand. `SheafOfModules.forgetToGradedModule` is a left
adjoint whose right adjoint is the cofree module, it reflects isomorphisms, and differential
graded modules have equalizers as soon as they have kernels; Beck's comonadicity theorem
therefore makes it a comonadic left adjoint, and a comonadic functor creates every limit it
preserves. Since forgetting the differential preserves all limits, every limit present in graded
modules is present in differential graded modules — finite products in particular.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### The preadditive structure -/

/-- The zero morphism of differential graded modules: the zero map in every degree. -/
instance homZero (M N : DifferentialGradedModule.{t, a, m} A) : Zero (Hom M N) :=
  ⟨{ toHomologicalComplex := 0
     map_mul := by
       intro n i U x y
       change 0 = (N.mul n i).app U 0 y
       simp }⟩

/-- Addition of morphisms of differential graded modules, degreewise. -/
instance homAdd (M N : DifferentialGradedModule.{t, a, m} A) : Add (Hom M N) :=
  ⟨fun f g =>
    { toHomologicalComplex := f.toHomologicalComplex + g.toHomologicalComplex
      map_mul := by
        intro n i U x y
        change ((f.toHomologicalComplex.f (n + i) +
          g.toHomologicalComplex.f (n + i)).val.app U) ((M.mul n i).app U x y) = _
        simp [SheafOfModules.add_val, ModuleCat.hom_add, f.map_mul, g.map_mul] }⟩

/-- Negation of a morphism of differential graded modules, degreewise. -/
instance homNeg (M N : DifferentialGradedModule.{t, a, m} A) : Neg (Hom M N) :=
  ⟨fun f =>
    { toHomologicalComplex := -f.toHomologicalComplex
      map_mul := by
        intro n i U x y
        change -((f.toHomologicalComplex.f (n + i)).val.app U
          ((M.mul n i).app U x y)) = _
        rw [f.map_mul]
        simp only [HomologicalComplex.neg_f_apply]
        change -((N.mul n i).app U ((f.toHomologicalComplex.f n).val.app U x) y) =
          (N.mul n i).app U ((-(f.toHomologicalComplex.f n)).val.app U x) y
        rw [show (-(f.toHomologicalComplex.f n)).val.app U =
          -(f.toHomologicalComplex.f n).val.app U from rfl]
        simp }⟩

/-- The degreewise additive structure makes a hom-type of differential graded modules an
additive group. -/
instance homAddCommGroup (M N : DifferentialGradedModule.{t, a, m} A) :
    AddCommGroup (Hom M N) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub f g := f + -g
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f g h := Hom.ext fun n => add_assoc _ _ _
  zero_add f := Hom.ext fun n => zero_add _
  add_zero f := Hom.ext fun n => add_zero _
  add_comm f g := Hom.ext fun n => add_comm _ _
  neg_add_cancel f := Hom.ext fun n => neg_add_cancel _
  sub_eq_add_neg f g := rfl

instance : Preadditive (DifferentialGradedModule.{t, a, m} A) where
  homGroup M N := homAddCommGroup M N
  add_comp _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.comp_add _ _ _ _ _ _

/-- Addition of morphisms of differential graded modules is degreewise. -/
@[simp]
theorem add_f {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) (n : ℤ) :
    (f + g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n + g.toHomologicalComplex.f n := rfl

/-- The zero morphism of differential graded modules is zero in every degree. -/
@[simp]
theorem zero_f (M N : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (0 : M ⟶ N).toHomologicalComplex.f n = 0 := rfl

/-- Negation of a morphism of differential graded modules is degreewise. -/
@[simp]
theorem neg_f {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    (-f).toHomologicalComplex.f n = -f.toHomologicalComplex.f n := rfl

end DifferentialGradedModule

/-- Forgetting the differential of a right differential graded module is an additive functor. -/
instance forgetToGradedModule_additive (A : DifferentialGradedAlgebra.{t, a} R) :
    (forgetToGradedModule.{t, a, m} A).Additive where
  map_add := GradedModule.Hom.ext fun n => by
    rw [forgetToGradedModule_map_app, DifferentialGradedModule.add_f]
    rfl

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Componentwise isomorphisms -/

/-- A morphism of differential graded modules whose homogeneous components are all isomorphisms
is an isomorphism: the degreewise inverses already commute with the differential and with the
action, the first because they are the inverses of a morphism of cochain complexes and the
second because the action is determined on sections. -/
theorem isIso_of_componentwise {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N)
    (hf : ∀ n : ℤ, IsIso (f.toHomologicalComplex.f n)) : IsIso f := by
  have (n : ℤ) : IsIso (f.toHomologicalComplex.f n) := hf n
  have hcomplex : IsIso f.toHomologicalComplex :=
    HomologicalComplex.Hom.isIso_of_components _
  let g : Hom N M :=
    { toHomologicalComplex := inv f.toHomologicalComplex
      map_mul := by
        have : IsIso f.toHomologicalComplex := hcomplex
        intro n p U x b
        have hpoint (k : ℤ) (y : (N.complex.X k).val.obj U) :
            (f.toHomologicalComplex.f k).val.app U
              ((inv (f.toHomologicalComplex.f k)).val.app U y) = y :=
          congrArg (fun q => (q.val.app U) y) (IsIso.inv_hom_id (f.toHomologicalComplex.f k))
        have hinj : Function.Injective
            ((f.toHomologicalComplex.f (n + p)).val.app U) := by
          apply (ModuleCat.mono_iff_injective _).1
          exact (inferInstance : Mono
            ((SheafOfModules.evaluation R U).map (f.toHomologicalComplex.f (n + p))))
        apply hinj
        change (f.toHomologicalComplex.f (n + p)).val.app U
          (((inv f.toHomologicalComplex).f (n + p)).val.app U
            ((N.mul n p).app U x b)) = _
        simp only [HomologicalComplex.Hom.inv_f_apply]
        rw [f.map_mul, hpoint (n + p) ((N.mul n p).app U x b), hpoint n x] }
  refine ⟨⟨g, Hom.ext fun n => ?_, Hom.ext fun n => ?_⟩⟩
  · change f.toHomologicalComplex.f n ≫ (inv f.toHomologicalComplex).f n = 𝟙 _
    simp
  · change (inv f.toHomologicalComplex).f n ≫ f.toHomologicalComplex.f n = 𝟙 _
    simp

end DifferentialGradedModule

/-- Forgetting the differential reflects isomorphisms: a morphism of differential graded modules
whose underlying graded morphism is invertible is invertible. -/
instance forgetToGradedModule_reflectsIsomorphisms (A : DifferentialGradedAlgebra.{t, a} R) :
    (forgetToGradedModule.{t, a, m} A).ReflectsIsomorphisms where
  reflects {_ _} f hf := by
    refine DifferentialGradedModule.isIso_of_componentwise f fun n => ?_
    have := hf
    exact inferInstanceAs (IsIso ((GradedModule.pieceFunctor A.toGradedAlgebra n).map
      ((forgetToGradedModule A).map f)))

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Degreewise kernels -/

/-- A degreewise family of morphisms of sheaves of modules commutes with transport along an
equality of degrees. -/
private lemma app_gradedCast {K L : ℤ → SheafOfModules.{m} R} (φ : ∀ n, K n ⟶ L n) {n n' : ℤ}
    (h : n = n') (U : Cᵒᵖ) (x : (K n).val.obj U) :
    (φ n').val.app U (gradedCast (fun q => (K q).val.obj U) h x) =
      gradedCast (fun q => (L q).val.obj U) h ((φ n).val.app U x) := by
  subst h; rfl

/-- Restriction of sections commutes with transport along an equality of degrees. -/
private lemma restriction_gradedCast {K : ℤ → SheafOfModules.{m} R} {U V : Cᵒᵖ}
    (g : V.unop ⟶ U.unop) {n n' : ℤ} (h : n = n') (x : (K n).val.obj U) :
    (K n').val.map g.op (gradedCast (fun q => (K q).val.obj U) h x) =
      gradedCast (fun q => (K q).val.obj V) h ((K n).val.map g.op x) := by
  subst h; rfl

/-- **Differential graded modules have kernels, formed degreewise.** The kernel of the
underlying graded morphism carries a unique differential for which its inclusion is a morphism
of differential graded modules, because that inclusion is degreewise a monomorphism; the
resulting object is then a kernel in the category of differential graded modules, since a graded
factorization through it automatically commutes with the differential. -/
instance hasKernels : HasKernels (DifferentialGradedModule.{t, a, m} A) where
  has_limit := by
    classical
    intro M N f
    obtain ⟨K, ι, hι, hlim, hfactor⟩ :=
      GradedModule.exists_kernel_degreewise ((forgetToGradedModule A).map f)
    dsimp only [forgetToGradedModule] at ι hι hlim hfactor
    let lim n := (hlim n).some
    have (n : ℤ) : Mono (ι.app n) := mono_of_isLimit_fork (lim n)
    have hd (n n' : ℤ) :
        (ι.app n ≫ M.complex.d n n') ≫ f.toHomologicalComplex.f n' = 0 := by
      rw [Category.assoc, ← f.toHomologicalComplex.comm, ← Category.assoc]
      exact (congrArg (fun g => g ≫ N.complex.d n n') (hι n)).trans zero_comp
    let d (n n' : ℤ) : K.piece n ⟶ K.piece n' :=
      (KernelFork.IsLimit.lift' (lim n') (ι.app n ≫ M.complex.d n n') (hd n n')).1
    have hdι (n n' : ℤ) : d n n' ≫ ι.app n' = ι.app n ≫ M.complex.d n n' :=
      (KernelFork.IsLimit.lift' (lim n') (ι.app n ≫ M.complex.d n n') (hd n n')).2
    let Cx : CochainComplex (SheafOfModules.{m} R) ℤ :=
      { X := K.piece
        d := d
        shape := by
          intro n n' h
          apply (cancel_mono (ι.app n')).1
          rw [hdι, M.complex.shape n n' h, comp_zero, zero_comp]
        d_comp_d' := by
          intro n n' n'' _ _
          apply (cancel_mono (ι.app n'')).1
          rw [Category.assoc, hdι, ← Category.assoc, hdι, Category.assoc,
            M.complex.d_comp_d, comp_zero, zero_comp] }
    have hinj (n : ℤ) (U : Cᵒᵖ) : Function.Injective ((ι.app n).val.app U) := by
      apply (ModuleCat.mono_iff_injective _).1
      exact (inferInstance : Mono ((SheafOfModules.evaluation R U).map (ι.app n)))
    have hdapp (n n' : ℤ) (U : Cᵒᵖ) (x : (K.piece n).val.obj U) :
        (ι.app n').val.app U ((d n n').val.app U x) =
          (M.complex.d n n').val.app U ((ι.app n).val.app U x) :=
      congrArg (fun g : K.piece n ⟶ M.complex.X n' => g.val.app U x) (hdι n n')
    let D : DifferentialGradedModule.{t, a, m} A :=
      { complex := Cx
        mul n p :=
          { app := K.smul n p
            map_smul_left := K.smul_smul_left n p
            map_smul_right := K.smul_smul_right n p
            naturality := K.smul_naturality n p }
        mul_assoc := K.smul_mul
        mul_one := K.smul_one
        leibniz := by
          intro n p U x b
          apply hinj (n + p + 1) U
          change (ι.app (n + p + 1)).val.app U
            ((d (n + p) (n + p + 1)).val.app U (K.smul n p U x b)) = _
          rw [hdapp, ι.map_smul]
          simp only [map_add, map_zsmul, Cx, app_gradedCast]
          rw [ι.map_smul, ι.map_smul, hdapp]
          exact M.leibniz n p U ((ι.app n).val.app U x) b }
    let j : D ⟶ M :=
      { toHomologicalComplex :=
          { f := ι.app
            comm' := fun n n' _ => (hdι n n').symm }
        map_mul := ι.map_smul }
    have hj : j ≫ f = 0 := Hom.ext hι
    have lift (P : DifferentialGradedModule.{t, a, m} A) (g : P ⟶ M)
        (hg : g ≫ f = 0) : ∃! h : P ⟶ D, h ≫ j = g := by
      obtain ⟨h, hh, huniq⟩ := hfactor ((forgetToGradedModule A).obj P)
        ((forgetToGradedModule A).map g)
        (fun n => congrArg (fun k : P ⟶ N => k.toHomologicalComplex.f n) hg)
      dsimp only [forgetToGradedModule] at h hh huniq
      have hhapp n : h.app n ≫ ι.app n = g.toHomologicalComplex.f n :=
        congrArg (fun k => k.app n) hh
      let k : P ⟶ D :=
        { toHomologicalComplex :=
            { f := h.app
              comm' := by
                intro n n' _
                apply (cancel_mono (ι.app n')).1
                change (h.app n ≫ d n n') ≫ ι.app n' =
                  (P.complex.d n n' ≫ h.app n') ≫ ι.app n'
                rw [Category.assoc, hdι, ← Category.assoc, hhapp,
                  Category.assoc, hhapp, g.toHomologicalComplex.comm] }
          map_mul := h.map_smul }
      refine ⟨k, Hom.ext hhapp, ?_⟩
      intro l hl
      refine Hom.ext fun n => ?_
      have hlg : (forgetToGradedModule A).map l ≫ ι =
          (forgetToGradedModule A).map g :=
        GradedModule.Hom.ext fun q =>
          congrArg (fun s : P ⟶ M => s.toHomologicalComplex.f q) hl
      exact congrArg (fun s => s.app n) (huniq _ hlg)
    exact ⟨⟨KernelFork.ofι j hj, KernelFork.IsLimit.ofι j hj
      (fun {P} g hg => (lift P g hg).choose)
      (fun {P} g hg => (lift P g hg).choose_spec.1)
      (fun {P} g hg l hl => (lift P g hg).unique hl (lift P g hg).choose_spec.1)⟩⟩

end DifferentialGradedModule

/-! ### Cokernels of sheaves of modules are locally surjective -/

/-- **The projection onto a cokernel of sheaves of modules is locally surjective.** A cokernel
of sheaves of modules is the sheafification of the presheaf cokernel, and the presheaf cokernel
is sectionwise surjective; local surjectivity is what survives the sheafification, and it is
what lets a section of a cokernel be named locally. -/
theorem cokernel_isLocallySurjective [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {M N Q : SheafOfModules.{m} R} (f : M ⟶ N)
    (p : N ⟶ Q) (hp : f ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hp)) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map p.val) := by
  let G : SheafOfModules.{m} R ⥤ PresheafOfModules.{m} R.obj :=
    SheafOfModules.forget.{m} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let S : PresheafOfModules.{m} R.obj ⥤ SheafOfModules.{m} R :=
    PresheafOfModules.sheafification.{m} (𝟙 R.obj)
  let adj : S ⊣ G := PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)
  have : Functor.PreservesZeroMorphisms S := by infer_instance
  let i : G ⋙ S ≅ 𝟭 (SheafOfModules.{m} R) := asIso adj.counit
  let f₀ := G.map f
  let p₀ := cokernel.π f₀
  let h₀ := cokernel.condition f₀
  let c₀ := CokernelCofork.ofπ p₀ h₀
  have hc₀ : IsColimit c₀ := cokernelIsCokernel f₀
  let c₁ := CokernelCofork.map c₀ S
  have hc₁ : IsColimit c₁ := CokernelCofork.mapIsColimit c₀ hc₀ S
  have hinvNat : f ≫ i.inv.app N = i.inv.app M ≫ (G ⋙ S).map f := by
    simpa using i.inv.naturality f
  let p' : N ⟶ S.obj (cokernel f₀) := i.inv.app N ≫ S.map p₀
  have hzero' : f ≫ p' = 0 := by
    dsimp only [p']
    rw [← Category.assoc, hinvNat, Category.assoc, Functor.comp_map, ← S.map_comp,
      cokernel.condition f₀, S.map_zero, comp_zero]
  have hc' : IsColimit (CokernelCofork.ofπ p' hzero') := by
    let c' {T : SheafOfModules.{m} R} (g : N ⟶ T) (hg : f ≫ g = 0) :
        CokernelCofork (S.map f₀) := by
      apply CokernelCofork.ofπ (i.hom.app N ≫ g)
      have hhomNat : (G ⋙ S).map f ≫ i.hom.app N = i.hom.app M ≫ f := by
        simpa using i.hom.naturality f
      calc
        S.map f₀ ≫ (i.hom.app N ≫ g) =
            (S.map f₀ ≫ i.hom.app N) ≫ g := by simp [Category.assoc]
        _ = (i.hom.app M ≫ f) ≫ g := by
          change ((G ⋙ S).map f ≫ i.hom.app N) ≫ g = _
          rw [hhomNat]
        _ = 0 := by simp [Category.assoc, hg]
    have hdesc {T : SheafOfModules.{m} R} (g : N ⟶ T) (hg : f ≫ g = 0) :
        S.map p₀ ≫ hc₁.desc (c' g hg) = i.hom.app N ≫ g :=
      hc₁.fac (c' g hg) WalkingParallelPair.one
    refine CokernelCofork.IsColimit.ofπ p' hzero'
      (fun {T} g hg => hc₁.desc (c' g hg)) (fun {T} g hg => ?_) (fun {T} g hg b hb => ?_)
    · calc
        p' ≫ hc₁.desc (c' g hg) = i.inv.app N ≫ (S.map p₀ ≫ hc₁.desc (c' g hg)) := by
          simp [p', Category.assoc]
        _ = i.inv.app N ≫ (i.hom.app N ≫ g) := by rw [hdesc g hg]
        _ = g := by simp
    · have hb' : S.map p₀ ≫ b = i.hom.app N ≫ g := by
        simpa [p', Category.assoc] using congrArg (fun k => i.hom.app N ≫ k) hb
      refine hc₁.hom_ext fun j => ?_
      cases j with
      | zero => simp
      | one =>
          change S.map p₀ ≫ b = S.map p₀ ≫ hc₁.desc (c' g hg)
          rw [hb', hdesc g hg]
  let e := hc'.coconePointUniqueUpToIso hc
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (S.map p₀)) := by
    change Sheaf.IsLocallySurjective ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf R.obj).map p₀))
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    exact Presheaf.isLocallySurjective_of_surjective J _
      fun U => PresheafOfModules.surjective_of_epi p₀ U
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (i.inv.app N)) :=
    inferInstance
  have hloc : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p) := by
    have hfac : p' ≫ e.hom = p :=
      IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc WalkingParallelPair.one
    rw [← hfac, Functor.map_comp]
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p') := by
      dsimp only [p']
      rw [Functor.map_comp]
      infer_instance
    infer_instance
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
    ((SheafOfModules.toSheaf R).map p)).mp hloc

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Degreewise cokernels -/

/-- **Differential graded modules have cokernels, formed degreewise.** The cokernel of the
underlying graded morphism carries a unique differential for which its projection is a morphism
of differential graded modules, because that projection is degreewise an epimorphism; the
resulting object is then a cokernel in the category of differential graded modules, since a
graded factorization out of it automatically commutes with the differential.

The Leibniz rule is the only identity that cannot be checked on a named section of the cokernel:
`SheafOfModules.cokernel_isLocallySurjective` produces a covering sieve on which a section does
lift, the identity is checked there, and separatedness of the cokernel glues it. -/
instance hasCokernels [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    HasCokernels (DifferentialGradedModule.{t, a, m} A) where
  has_colimit := by
    classical
    intro M N f
    let F := forgetToGradedModule A
    let fG := F.map f
    obtain ⟨Q, π, hπ, hcolim, hfactor⟩ := GradedModule.exists_cokernel_degreewise fG
    dsimp only [fG, F, forgetToGradedModule] at π hπ hcolim hfactor
    let hc (n : ℤ) := (hcolim n).some
    have hπEpi (n : ℤ) : Epi (π.app n) := Cofork.IsColimit.epi (hc n)
    have hzeroMap (n : ℤ) : f.toHomologicalComplex.f n ≫ π.app n = 0 := hπ n
    have hdiff (n n' : ℤ) :
        f.toHomologicalComplex.f n ≫ (N.complex.d n n' ≫ π.app n') = 0 := by
      calc
        f.toHomologicalComplex.f n ≫ (N.complex.d n n' ≫ π.app n') =
            (f.toHomologicalComplex.f n ≫ N.complex.d n n') ≫ π.app n' := by
              simp [Category.assoc]
        _ = (M.complex.d n n' ≫ f.toHomologicalComplex.f n') ≫ π.app n' := by
              rw [Category.assoc, ← f.toHomologicalComplex.comm, ← Category.assoc]
        _ = 0 := by
              calc
                (M.complex.d n n' ≫ f.toHomologicalComplex.f n') ≫ π.app n' =
                    M.complex.d n n' ≫ (f.toHomologicalComplex.f n' ≫ π.app n') := by
                      simp [Category.assoc]
                _ = M.complex.d n n' ≫ 0 := by rw [hzeroMap]
                _ = 0 := by simp
    let d (n n' : ℤ) : Q.piece n ⟶ Q.piece n' :=
      (hc n).desc (CokernelCofork.ofπ (N.complex.d n n' ≫ π.app n') (hdiff n n'))
    have hdπ (n n' : ℤ) : π.app n ≫ d n n' = N.complex.d n n' ≫ π.app n' :=
      (hc n).fac (CokernelCofork.ofπ (N.complex.d n n' ≫ π.app n') (hdiff n n'))
        WalkingParallelPair.one
    let Cx : CochainComplex (SheafOfModules.{m} R) ℤ :=
      { X := Q.piece
        d := d
        shape := by
          intro n n' h
          apply (cancel_epi (π.app n)).1
          rw [hdπ, N.complex.shape n n' h]
          exact zero_comp
        d_comp_d' := by
          intro n n' n'' _ _
          apply (cancel_epi (π.app n)).1
          calc
            π.app n ≫ (d n n' ≫ d n' n'') =
                (π.app n ≫ d n n') ≫ d n' n'' := by simp [Category.assoc]
            _ = (N.complex.d n n' ≫ π.app n') ≫ d n' n'' := by rw [hdπ]
            _ = N.complex.d n n' ≫ (π.app n' ≫ d n' n'') := by simp [Category.assoc]
            _ = N.complex.d n n' ≫ (N.complex.d n' n'' ≫ π.app n'') := by rw [hdπ]
            _ = (N.complex.d n n' ≫ N.complex.d n' n'') ≫ π.app n'' := by
                  simp
            _ = 0 := by
                rw [N.complex.d_comp_d]
                exact zero_comp }
    let D : DifferentialGradedModule.{t, a, m} A :=
      { complex := Cx
        mul n p :=
          { app := Q.smul n p
            map_smul_left := Q.smul_smul_left n p
            map_smul_right := Q.smul_smul_right n p
            naturality := Q.smul_naturality n p }
        mul_assoc := Q.smul_mul
        mul_one := Q.smul_one
        leibniz := by
          intro n p U x b
          let Fp := PresheafOfModules.toPresheaf R.obj
          have hlocal : Presheaf.IsLocallySurjective J (Fp.map (π.app n).val) :=
            cokernel_isLocallySurjective (f.toHomologicalComplex.f n) (π.app n)
              (hzeroMap n) (hc n)
          let Sv := Presheaf.imageSieve (Fp.map (π.app n).val) x
          have hSv : Sv ∈ J U.unop := by
            have : Presheaf.IsLocallySurjective J (Fp.map (π.app n).val) := hlocal
            exact Presheaf.imageSieve_mem J (Fp.map (π.app n).val) x
          apply (Q.piece (n + p + 1)).isSheaf.isSeparated U.unop Sv hSv
          intro V g hg
          obtain ⟨y, hy⟩ := hg
          have hyType : ToType ((Fp.obj (N.complex.X n).val).obj (Opposite.op V)) =
              (N.complex.X n).val.obj (Opposite.op V) :=
            PresheafOfModules.toPresheaf_obj_coe
              (R := R.obj) (M := (N.complex.X n).val) (Opposite.op V)
          let yM : (N.complex.X n).val.obj (Opposite.op V) := hyType ▸ y
          let bV : (A.complex.X p).val.obj (Opposite.op V) :=
            (A.complex.X p).val.map g.op b
          have hy' : (π.app n).val.app (Opposite.op V) yM =
              (Q.piece n).val.map g.op x := by
            have hyM : (yM : ToType ((Fp.obj (N.complex.X n).val).obj
                (Opposite.op V))) = y := by
              dsimp [yM]
            rw [← hyM] at hy
            change (((Fp.map (π.app n).val).app (Opposite.op V)).hom) yM =
              ((Fp.obj (Q.piece n).val).map g.op).hom x at hy
            exact ((PresheafOfModules.toPresheaf_map_app_apply
              (π.app n).val (Opposite.op V) yM).symm.trans hy).trans rfl
          have hdπApp (r s : ℤ) (z : (N.complex.X r).val.obj (Opposite.op V)) :
              (d r s).val.app (Opposite.op V) ((π.app r).val.app (Opposite.op V) z) =
                (π.app s).val.app (Opposite.op V)
                  ((N.complex.d r s).val.app (Opposite.op V) z) := by
            simpa using congrArg (fun w : N.complex.X r ⟶ Q.piece s =>
              (w.val.app (Opposite.op V)) z) (hdπ r s)
          have hnatD (z : (Q.piece (n + p)).val.obj U) :
              (Q.piece (n + p + 1)).val.map g.op
                  ((d (n + p) (n + p + 1)).val.app U z) =
                (d (n + p) (n + p + 1)).val.app (Opposite.op V)
                  ((Q.piece (n + p)).val.map g.op z) :=
            (PresheafOfModules.naturality_apply (d (n + p) (n + p + 1)).val g.op z).symm
          have hnatDn (z : (Q.piece n).val.obj U) :
              (Q.piece (n + 1)).val.map g.op ((d n (n + 1)).val.app U z) =
                (d n (n + 1)).val.app (Opposite.op V) ((Q.piece n).val.map g.op z) :=
            (PresheafOfModules.naturality_apply (d n (n + 1)).val g.op z).symm
          have hnatA : (A.complex.X (p + 1)).val.map g.op
                ((A.complex.d p (p + 1)).val.app U b) =
              (A.complex.d p (p + 1)).val.app (Opposite.op V) bV :=
            (PresheafOfModules.naturality_apply (A.complex.d p (p + 1)).val g.op b).symm
          change (Q.piece (n + p + 1)).val.map g.op
              ((d (n + p) (n + p + 1)).val.app U ((Q.smul n p U) x b)) = _
          rw [hnatD, Q.smul_naturality n p g.op x b, ← hy']
          have hleft :
              (d (n + p) (n + p + 1)).val.app (Opposite.op V)
                  ((Q.smul n p (Opposite.op V)
                    ((π.app n).val.app (Opposite.op V) yM) bV)) =
                (π.app (n + p + 1)).val.app (Opposite.op V)
                  ((N.complex.d (n + p) (n + p + 1)).val.app (Opposite.op V)
                    ((N.mul n p).app (Opposite.op V) yM bV)) := by
            calc
              _ = (d (n + p) (n + p + 1)).val.app (Opposite.op V)
                  ((π.app (n + p)).val.app (Opposite.op V)
                    ((N.mul n p).app (Opposite.op V) yM bV)) := by
                    rw [← π.map_smul n p (Opposite.op V) yM bV]
              _ = _ := hdπApp (n + p) (n + p + 1)
                ((N.mul n p).app (Opposite.op V) yM bV)
          have hN := N.leibniz n p (Opposite.op V) yM bV
          have hNmap := congrArg ((π.app (n + p + 1)).val.app (Opposite.op V)) hN
          simp only [map_add, map_zsmul] at hNmap
          rw [app_gradedCast (fun q => π.app q) (add_right_comm n 1 p)
            (Opposite.op V)] at hNmap
          rw [app_gradedCast (fun q => π.app q) (add_assoc n p 1).symm
            (Opposite.op V)] at hNmap
          simp only [π.map_smul] at hNmap
          rw [← hdπApp n (n + 1) yM] at hNmap
          have hright :
              (Q.piece (n + p + 1)).val.map g.op
                  (gradedCast (fun q => (Q.piece q).val.obj U) (add_right_comm n 1 p)
                    ((Q.smul (n + 1) p U) ((d n (n + 1)).val.app U x) b) +
                    (Int.negOnePow n : ℤ) •
                    gradedCast (fun q => (Q.piece q).val.obj U) (add_assoc n p 1).symm
                      ((Q.smul n (p + 1) U) x
                        ((A.complex.d p (p + 1)).val.app U b))) =
                gradedCast (fun q => (Q.piece q).val.obj (Opposite.op V))
                    (add_right_comm n 1 p)
                    ((Q.smul (n + 1) p (Opposite.op V))
                      ((d n (n + 1)).val.app (Opposite.op V)
                        ((π.app n).val.app (Opposite.op V) yM)) bV) +
                  (Int.negOnePow n : ℤ) •
                    gradedCast (fun q => (Q.piece q).val.obj (Opposite.op V))
                      (add_assoc n p 1).symm
                      ((Q.smul n (p + 1) (Opposite.op V))
                        ((π.app n).val.app (Opposite.op V) yM)
                        ((A.complex.d p (p + 1)).val.app (Opposite.op V) bV)) := by
            simp only [map_add, map_zsmul]
            congr 1
            · rw [restriction_gradedCast, Q.smul_naturality, hnatDn, ← hy']
              rfl
            · rw [restriction_gradedCast, Q.smul_naturality, ← hy']
              have hnatA' := hnatA
              change (A.toGradedAlgebra.piece (p + 1)).val.map g.op
                  ((A.complex.d p (p + 1)).val.app U b) = _ at hnatA'
              rw [hnatA']
              rfl
          change (d (n + p) (n + p + 1)).val.app (Opposite.op V)
              ((Q.smul n p (Opposite.op V)
                ((π.app n).val.app (Opposite.op V) yM) bV)) = _
          rw [hleft]
          change (π.app (n + p + 1)).val.app (Opposite.op V)
              ((N.complex.d (n + p) (n + p + 1)).val.app (Opposite.op V)
                ((N.mul n p).app (Opposite.op V) yM bV)) =
            (Q.piece (n + p + 1)).val.map g.op
              (gradedCast (fun q => (Q.piece q).val.obj U) (add_right_comm n 1 p)
                ((Q.smul (n + 1) p U) ((d n (n + 1)).val.app U x) b) +
                (Int.negOnePow n : ℤ) •
                gradedCast (fun q => (Q.piece q).val.obj U) (add_assoc n p 1).symm
                  ((Q.smul n (p + 1) U) x
                    ((A.complex.d p (p + 1)).val.app U b)))
          rw [hright]
          exact hNmap }
    let j : N ⟶ D :=
      { toHomologicalComplex :=
          { f := π.app
            comm' := fun n n' _ => hdπ n n' }
        map_mul := π.map_smul }
    have hj : f ≫ j = 0 := Hom.ext fun n => hπ n
    have desc (P : DifferentialGradedModule.{t, a, m} A) (g : N ⟶ P) (hg : f ≫ g = 0) :
        ∃! h : D ⟶ P, j ≫ h = g := by
      obtain ⟨h, hh, huniq⟩ := hfactor ((forgetToGradedModule A).obj P)
        ((forgetToGradedModule A).map g)
        (fun n => congrArg (fun k : M ⟶ P => k.toHomologicalComplex.f n) hg)
      dsimp only [forgetToGradedModule] at h hh huniq
      have hhapp n : π.app n ≫ h.app n = g.toHomologicalComplex.f n :=
        congrArg (fun k => k.app n) hh
      let k : D ⟶ P :=
        { toHomologicalComplex :=
            { f := h.app
              comm' := by
                intro n n' _
                apply (cancel_epi (π.app n)).1
                calc
                  π.app n ≫ (h.app n ≫ P.complex.d n n') =
                      (π.app n ≫ h.app n) ≫ P.complex.d n n' := by simp [Category.assoc]
                  _ = g.toHomologicalComplex.f n ≫ P.complex.d n n' := by rw [hhapp]
                  _ = N.complex.d n n' ≫ g.toHomologicalComplex.f n' :=
                      g.toHomologicalComplex.comm n n'
                  _ = N.complex.d n n' ≫ (π.app n' ≫ h.app n') := by rw [hhapp]
                  _ = (π.app n ≫ D.complex.d n n') ≫ h.app n' := by
                    rw [hdπ]
                    simp [Category.assoc]
                  _ = π.app n ≫ (D.complex.d n n' ≫ h.app n') := by simp [Category.assoc] }
          map_mul := h.map_smul }
      refine ⟨k, Hom.ext hhapp, ?_⟩
      intro l hl
      refine Hom.ext fun n => ?_
      have hlg : π ≫ (forgetToGradedModule A).map l = (forgetToGradedModule A).map g :=
        GradedModule.Hom.ext fun q =>
          congrArg (fun s : N ⟶ P => s.toHomologicalComplex.f q) hl
      exact congrArg (fun s => s.app n) (huniq _ hlg)
    exact ⟨⟨CokernelCofork.ofπ j hj, CokernelCofork.IsColimit.ofπ j hj
      (fun {P} g hg => (desc P g hg).choose)
      (fun {P} g hg => (desc P g hg).choose_spec.1)
      (fun {P} g hg l hl => (desc P g hg).unique hl (desc P g hg).choose_spec.1)⟩⟩

/-! ### Finite products -/

/-- Differential graded modules have equalizers: they are preadditive and have kernels. -/
instance hasEqualizers : HasEqualizers (DifferentialGradedModule.{t, a, m} A) :=
  Preadditive.hasEqualizers_of_hasKernels

end DifferentialGradedModule

/-- **Forgetting the differential is a comonadic left adjoint.** Its right adjoint is the cofree
differential graded module, it reflects isomorphisms, and differential graded modules have
equalizers; Beck's comonadicity theorem supplies the rest. -/
noncomputable instance forgetToGradedModule_comonadic
    (A : DifferentialGradedAlgebra.{t, a} R) :
    ComonadicLeftAdjoint (forgetToGradedModule.{t, a, m} A) := by
  have : Comonad.HasEqualizerOfIsCosplitPair (forgetToGradedModule.{t, a, m} A) :=
    ⟨fun _ _ => inferInstance⟩
  letI : Comonad.PreservesLimitOfIsCosplitPair (forgetToGradedModule.{t, a, m} A) :=
    ⟨fun _ _ => inferInstance⟩
  exact Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (forgetAdjunction A)

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- **Differential graded modules have finite products, formed degreewise.** Forgetting the
differential is comonadic and preserves all limits, so it creates them: every limit that exists
for graded modules exists for differential graded modules, and finite products of graded modules
are themselves degreewise. -/
instance hasFiniteProducts [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    HasFiniteProducts (DifferentialGradedModule.{t, a, m} A) where
  out n := by
    let : CreatesLimitsOfShape (Discrete (Fin n)) (forgetToGradedModule.{t, a, m} A) :=
      comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _
    exact ⟨fun K => hasLimit_of_created K (forgetToGradedModule.{t, a, m} A)⟩

/-! ### The abelian structure -/

/-- The coimage-image comparison of a morphism of differential graded modules is an isomorphism,
because it is one after forgetting the differential: that functor is additive and preserves both
limits and colimits, graded modules are abelian, and a morphism of differential graded modules
whose components are isomorphisms is an isomorphism. -/
theorem isIso_coimageImageComparison [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  let F := forgetToGradedModule.{t, a, m} A
  have hcmp := Abelian.PreservesCoimageImageComparison.iso F f
  refine isIso_of_componentwise (Abelian.coimageImageComparison f) fun n => ?_
  have hmap : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso hcmp.hom]
    infer_instance
  have : IsIso (F.map (Abelian.coimageImageComparison f)) := hmap
  exact inferInstanceAs (IsIso ((GradedModule.pieceFunctor A.toGradedAlgebra n).map
    (F.map (Abelian.coimageImageComparison f))))

/-- **The category of right differential graded modules over a sheaf of differential graded
algebras is abelian.**

Kernels and cokernels are formed degreewise, finite products are created by forgetting the
differential, and the coimage-image comparison of a morphism is an isomorphism because it is one
after forgetting the differential. -/
noncomputable instance abelian [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    Abelian (DifferentialGradedModule.{t, a, m} A) := by
  have : ∀ {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N),
      IsIso (Abelian.coimageImageComparison f) := fun f => isIso_coimageImageComparison f
  exact Abelian.ofCoimageImageComparisonIsIso

end DifferentialGradedModule

end SheafOfModules
