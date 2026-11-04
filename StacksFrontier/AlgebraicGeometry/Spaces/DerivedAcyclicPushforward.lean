module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections

/-!
# Derived direct image of a complex of modules with right-acyclic terms on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, and
let `K` be a cochain complex of quasi-coherent `𝒪_X`-modules on the small étale site each of
whose terms is right acyclic for `f_*`.  Then the termwise direct image `f_* K` computes the
derived direct image: the canonical comparison `f_* K ⟶ Rf_* K` is invertible in `D(𝒪_Y)`.

Invertibility is tested on cohomology sheaves.  Fix a degree `q` and replace `K` by its stupid
truncation `σ^{≥a}K` with `a < q` and `a + N ≤ q`, where `N` is an integer bounding the
cohomological amplitude of `Rf_*` on objects with quasi-coherent cohomology.  The truncation is
bounded below with right-acyclic terms, so the comparison is invertible there by Leray's
acyclicity criterion; and both `f_*` and `Rf_*` see `σ^{≥a}K → K` as an isomorphism on `H^q`,
the first because the map is already a degreewise isomorphism above `a` and the second because
the third term of the stupid truncation triangle lies in `D^{≤a-1}`, which `Rf_*` carries into
`D^{≤a+N-2}`.

## Main results

* `AlgebraicGeometry.Space.isIso_to_rightDerived_of_termwise_acyclic`: the canonical comparison
  from the termwise direct image to any right derived direct image is invertible at a complex of
  quasi-coherent `𝒪_X`-modules with right-acyclic terms.

## Supporting results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_stupidTruncLE_X` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_stupidTruncGE_X`: the terms of a stupid
  truncation of a complex of quasi-coherent modules are quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_derived_homology`: the cohomology of such a
  complex is quasi-coherent, in the complex and in the derived category respectively.
* `AlgebraicGeometry.Space.isIso_homologyFunctor_map_rightDerived_stupidTrunc`: above the bound
  the derived functor sees `σ^{≥a}K → K` as an isomorphism on `H^q`.

## Implementation notes

*No `stacks` attribute is claimed.*  The content is [Stacks, Tag 0G9N], which is a statement
about schemes and is already registered there, on
`AlgebraicGeometry.isIso_to_rightDerived_of_termwise_acyclic`.  What is below is that statement
read for the small étale modules of an algebraic space; it is not a clause of a spaces-side
source statement, so nothing here carries a tag.

*The two geometric inputs are hypotheses.*  The scheme-side proof first restricts to an affine
open of the target, because the integer `N` of [Stacks, Tag 01XJ] exists only over a
quasi-compact base.  Here the bound is the explicit hypothesis `hUpper`, stated globally, and
right acyclicity of the terms is the explicit hypothesis `hacyclic`; both are to be discharged
elsewhere, so the whole localization apparatus of the scheme-side file — the comparison of the
derived direct image with restriction to an open — is absent and the derived-category argument
is run with `Rf` itself.

*What is reused.*  Everything beyond quasi-coherence of truncations and of cohomology is already
generic over abelian categories, in `Stacks.DerivedAcyclic`: the stupid truncation triangle, the
bound `D^{≤a}` on a truncation from above, triangulatedness of a right derived functor, right
acyclicity of the terms of a truncation from below, the termwise cohomology comparison, and the
bounded-below Leray step `Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`.

*The closure properties.*  Quasi-coherence of `𝒪_X`-modules on an algebraic space is closed
under kernels and cokernels unconditionally, by
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_algebraicSpace` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_algebraicSpace`, and
contains zero by `SheafOfModules.isQuasicoherentOnSite_containsZero`.  The three `private`
helpers below are therefore stated with those closure classes rather than with
`CategoryTheory.ObjectProperty.IsWeakSerreClass`, which is not available here without further
input and which the argument does not use.

*Universes and instances.*  The module universe is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.  `Modules.{u, u}` is
`SheafOfModules` at a module universe below the universe `u + 1` of the objects of the site, so
instance search for `Abelian`, `IsGrothendieckAbelian` or `EnoughInjectives` there stalls on a
universe constraint; `attribute [local instance 5000] SheafOfModules.instAbelian` and the two
universe-pinned theorems `AlgebraicGeometry.Space.isGrothendieckAbelian_modules` and
`AlgebraicGeometry.Space.enoughInjectives_modules` are registered locally for that reason.
`HasDerivedCategory` is left as an instance binder, so the statements hold for whichever derived
category a consumer has chosen.

## References

* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

/-! ### Closure of an object property along truncations and cohomology -/

/-- The cohomology of a complex whose terms satisfy an object property closed under kernels and
cokernels satisfies it too: the cycles are a kernel of a map between two terms and the
cohomology is a cokernel of a map into the cycles. -/
private lemma prop_homology_of_prop_X {A : Type*} [Category* A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, P (K.X n)) (i : ℤ) :
    P (K.homology i) :=
  P.prop_of_isColimit_cokernelCofork
    (K.homologyIsCokernel ((ComplexShape.up ℤ).prev i) i rfl) (hK _)
    (P.prop_of_isLimit_kernelFork
      (K.cyclesIsKernel i ((ComplexShape.up ℤ).next i) rfl) (hK i) (hK _))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

/-! ### Quasi-coherence of truncations and of cohomology -/

/-- The terms of a stupid truncation of a complex of quasi-coherent `𝒪_X`-modules are
quasi-coherent: each is either a term of the complex or zero. -/
private lemma isQuasicoherentOnSite_stupidTrunc_X {ι : Type*} {c : ComplexShape ι}
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) (e : c.Embedding (ComplexShape.up ℤ))
    [e.IsRelIff] (i : ℤ) : ((K.stupidTrunc e).X i).IsQuasicoherentOnSite := by
  by_cases hi : ∃ j, e.f j = i
  · obtain ⟨j, hj⟩ := hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso (K.stupidTruncXIso e hj).symm (hqc i)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (K.isZero_stupidTrunc_X e i (by simpa using hi))

/-- The terms of a stupid truncation in degrees `≤ a` of a complex of quasi-coherent
`𝒪_X`-modules are quasi-coherent: each is either a term of the complex or zero. -/
theorem isQuasicoherentOnSite_stupidTruncLE_X
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) (a i : ℤ) :
    ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_stupidTrunc_X B S hS K hqc _ i

/-- The terms of a stupid truncation in degrees `≥ a` of a complex of quasi-coherent
`𝒪_X`-modules are quasi-coherent: each is either a term of the complex or zero. -/
theorem isQuasicoherentOnSite_stupidTruncGE_X
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) (a i : ℤ) :
    ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_stupidTrunc_X B S hS K hqc _ i

/-- The cohomology of a cochain complex of quasi-coherent `𝒪_X`-modules is quasi-coherent:
quasi-coherence on an algebraic space is closed under kernels and cokernels. -/
theorem isQuasicoherentOnSite_homology
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) (i : ℤ) :
    (K.homology i).IsQuasicoherentOnSite :=
  prop_homology_of_prop_X (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) K hqc i

/-- The cohomology sheaves in the derived category of a complex of quasi-coherent `𝒪_X`-modules
are quasi-coherent: they are the cohomology of the complex itself, computed by
`DerivedCategory.homologyFunctorFactors`. -/
theorem isQuasicoherentOnSite_derived_homology
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)]
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) :
    ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
      (DerivedCategory.Q.obj K)).IsQuasicoherentOnSite := fun i =>
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS X.1 X.2) i).app K).symm
    (isQuasicoherentOnSite_homology B S hS K hqc i)

/-! ### The derived functor on a stupid truncation -/

/-- Above the bound `N` the derived functor sees `σ^{≥a}K → K` as an isomorphism on `H^q`: the
third term of the stupid truncation triangle lies in `D^{≤a-1}`, so its image lies in
`D^{≤a+N-2}`, which `q` exceeds. -/
theorem isIso_homologyFunctor_map_rightDerived_stupidTrunc
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)]
    {T : Type*} [Category* T] [Abelian T] [HasDerivedCategory T]
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ DerivedCategory T)
    [Rf.CommShift ℤ] [Rf.IsTriangulated] (N : ℤ)
    (hUpper : ∀ (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite) →
      E.IsLE d → (Rf.obj E).IsLE (d + N - 1))
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) (a q : ℤ) (ha : a + N ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor T q).map
      (Rf.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
          (ComplexShape.up ℤ)).map
          (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)))))) := by
  let tail := K.stupidTrunc (ComplexShape.embeddingUpIntLE (a - 1))
  have hTail : (Rf.obj (DerivedCategory.Q.obj tail)).IsLE (a - 1 + N - 1) :=
    hUpper (DerivedCategory.Q.obj tail) (a - 1)
      (isQuasicoherentOnSite_derived_homology B S hS tail
        (isQuasicoherentOnSite_stupidTruncLE_X B S hS K hqc (a - 1)))
      (Stacks.DerivedAcyclic.isLE_stupidTruncLE K (a - 1))
  let Tri := (DerivedCategory.Qh ⋙ Rf).mapTriangle.obj
    (Stacks.DerivedAcyclic.stupidTruncTriangleh K (a - 1))
  have hTri : Tri ∈ distTriang (DerivedCategory T) :=
    (DerivedCategory.Qh ⋙ Rf).map_distinguished _
      (Stacks.DerivedAcyclic.stupidTruncTriangleh_distinguished K (a - 1))
  have hTail' : Tri.obj₃.IsLE (a - 1 + N - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (Rf.mapIso ((DerivedCategory.quotientCompQhIso
        (Modules.{u, u} B S hS X.1 X.2)).symm.app tail)) (a - 1 + N - 1)
  have hepi : Epi ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    ((DerivedCategory.homologyFunctor T 0).homologySequence_epi_shift_map_mor₁_iff
      Tri hTri q).2 ((Tri.obj₃.isZero_of_isLE (a - 1 + N - 1) q (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    ((DerivedCategory.homologyFunctor T 0).homologySequence_mono_shift_map_mor₁_iff
      Tri hTri (q - 1) q (by omega)).2
      ((Tri.obj₃.isZero_of_isLE (a - 1 + N - 1) (q - 1) (by omega)).eq_of_src _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    isIso_of_mono_of_epi _
  change IsIso ((DerivedCategory.homologyFunctor T q).map
    ((DerivedCategory.Qh ⋙ Rf).map
      ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)).map
        (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (a - 1 + 1)))))) at hiso
  rw [show a - 1 + 1 = a by omega] at hiso
  simpa only [Functor.comp_map] using hiso

/-! ### The comparison at a complex with right-acyclic terms -/

/-- **[Stacks, Tag 0G9N] for the small étale modules of an algebraic space.**  Let `f : X ⟶ Y` be
a morphism of algebraic spaces over `S` and let `K` be a cochain complex of quasi-coherent
`𝒪_X`-modules each of which is right acyclic for `f_*`.  Then `f_* K` represents `Rf_* K` in
`D(𝒪_Y)`: the canonical comparison from the termwise direct image to any right derived direct
image is an isomorphism at `K`.

The two geometric inputs are hypotheses: `hacyclic`, that the terms are right acyclic, and
`hUpper`, the bound on the cohomological amplitude of `Rf_*` on objects with quasi-coherent
cohomology.

No `stacks` attribute: Tag 0G9N is a statement about schemes and is registered there, on
`AlgebraicGeometry.isIso_to_rightDerived_of_termwise_acyclic`. -/
theorem isIso_to_rightDerived_of_termwise_acyclic
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)] (f : X ⟶ Y)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite)
    (hacyclic : ∀ n, (modulePushforward B S hS f).rightAcyclic (K.X n))
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (N : ℕ)
    (hUpper : ∀ (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite) →
      E.IsLE d → (Rf.obj E).IsLE (d + N - 1)) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ)).obj K)) := by
  let F := modulePushforward B S hS f
  let : Rf.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor F Rf α
  rw [DerivedCategory.isIso_iff]
  intro q
  let Φ := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) q
  let a : ℤ := min (q - 1) (q - N)
  let g : _ ⟶ K := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)
  let v := (HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
    (ComplexShape.up ℤ)).map g
  have ha₁ : a < q := by
    dsimp [a]
    omega
  have ha₂ : a + (N : ℤ) ≤ q := by
    dsimp [a]
    omega
  have hleft : IsIso (Φ.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)) :=
    Stacks.DerivedAcyclic.isIso_homologyFunctor_map_termwise_stupidTrunc F K a q ha₁
  have hright : IsIso (Φ.map (Rf.map (DerivedCategory.Qh.map v))) :=
    isIso_homologyFunctor_map_rightDerived_stupidTrunc B S hS Rf (N : ℤ) hUpper K hqc a q ha₂
  have htail : IsIso (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic F Rf α _
      (Stacks.DerivedAcyclic.plus_stupidTruncGE K a)
      (Stacks.DerivedAcyclic.rightAcyclic_stupidTruncGE F K hacyclic a)
  have hcomp : IsIso
      (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v) ≫
        Φ.map (α.app ((HomotopyCategory.quotient _ _).obj K))) := by
    rw [← Functor.map_comp, α.naturality v, Functor.map_comp]
    show IsIso (Φ.map (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) ≫
      Φ.map (Rf.map (DerivedCategory.Qh.map v)))
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v))
    (Φ.map (α.app ((HomotopyCategory.quotient _ _).obj K)))

end AlgebraicGeometry.Space

end
