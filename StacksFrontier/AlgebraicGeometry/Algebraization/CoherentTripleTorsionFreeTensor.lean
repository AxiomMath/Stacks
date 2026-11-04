module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeSnake
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul

/-!
# The quotient by `f` of a twist is the twist of the quotient, and the last clause of the snake

`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeSnake` reduced the
`f`-torsion-freeness of the quotient — the fifth clause of
`Stacks.Algebraization.HasHilbertInductionStep` — to monicity of
`(Stacks.Algebraization.smulSnakeInput φ c).L₃.f`, the map that multiplication by the chosen
section of `L` induces on the two quotients by `f`. This file discharges that hypothesis, and
with it the clause.

## The two identifications, and that neither needed anything new

The map `(smulSnakeInput φ c).L₃.f` is a map between *two cokernels of multiplication by `f`*:
the third row of a snake input is the cokernel of its vertical morphism, taken in
`CategoryTheory.ShortComplex`, and the two cokernel presentations it carries are
`ShortComplex.SnakeInput.h₃τ₁` and `h₃τ₂`. What the induction step has a monicity theorem for is
the map `(F/fF) ⊗ L^{⊗ n} ⟶ (F/fF) ⊗ L^{⊗ n+1}`,
`Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` with `F` replaced by
`F/fF`. The two are identified here, and both halves of the identification were already in the
repository:

* monicity of a map between cokernels does not depend on which cokernel presentations it is read
  through — `Stacks.Algebraization.mono_of_isColimit_cokernelCofork` below, which is the general
  statement replacing the `CategoryTheory.IsColimit.coconePointUniqueUpToIso` bookkeeping an
  earlier reading of
  `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction` described;
* and `(F/fF) ⊗ L^{⊗ n}` *is* a cokernel of multiplication by `f` on `F ⊗ L^{⊗ n}`, because
  tensoring on the right preserves finite colimits and commutes with multiplication by a global
  section. An earlier reading of that file, and of
  `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeSnake`, recorded that
  exactness of `- ⊗ L^{⊗ n}` was "recorded nowhere in either tree for this spelling of the
  tensor product". **That is false in both halves.** The tensor product the twists of a coherent
  triple use is `Stacks.RelativeVeryAmple.tensorModules`, whose right-handed functor spelling is
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules`, as
  `Stacks.Algebraization.tensorRightModules_map` records, and that functor is
  `AlgebraicGeometry.SheafOfModules.sheafTensorRight X.sheaf` on the nose, by `rfl`. So:

  - right exactness is
    `Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits`,
    [Stacks, Tag 05NB], **with no hypothesis at all** — not even invertibility of `L`, which the
    hand-off expected to be the key. (Invertibility does give it independently, through
    `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules_preservesFiniteColimits`
    and the equivalence of [Stacks, Tag 0FFM],
    `CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence`; the unconditional
    statement is used here because it is weaker in hypotheses and equally close to hand.)
  - and the compatibility with multiplication by `f` is
    `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`, restated below as
    `Stacks.Algebraization.tensorModulesMap_smulPowHom_one`.

## Main results

* `Stacks.Algebraization.mono_of_isColimit_cokernelCofork`: monicity of the map induced on two
  cokernels is independent of the cokernel presentations used to read it off.
* `Stacks.Algebraization.tensorModulesMap_smulPowHom_one`: **multiplication by a global section
  of `𝒪_X` commutes with tensoring**, at the tensor-product spelling the twists of a coherent
  triple are written in.
* `Stacks.Algebraization.isColimitCokernelCoforkTensor`: **`(F/cF) ⊗ P` is a cokernel of
  multiplication by `c` on `F ⊗ P`**, the quotient map being the quotient map tensored with `P`.
* `Stacks.Algebraization.mono_smulSnakeInput_L₃_f`: **the hypothesis of
  `Stacks.Algebraization.mono_smulPowHom_cokernel_of_mono`, discharged.**
* `Stacks.Algebraization.isFTorsionFree_cokernel_tensorModulesMap`: the two combined — the
  quotient of `F ⊗ P₁ ⟶ F ⊗ P₂` is `f`-torsion-free as soon as the same map on `F/fF` is a
  monomorphism.
* `Stacks.Algebraization.CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ`:
  **the fifth clause of `Stacks.Algebraization.HasHilbertInductionStep`**, the
  `f`-torsion-freeness of the quotient of the induction step's short exact sequence.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules)
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.SheafOfModules (globalSectionToEnd terminalSection)

universe u

namespace Stacks.Algebraization

/-! ### Monicity between cokernels, read through any presentation -/

/-- A cokernel cofork of one morphism is one of any morphism equal to it, read through any
projection equal to its own. Needed because the *type* of a cokernel cofork mentions both the
morphism and the projection, so the two presentations compared below — one coming from a snake
input, one from a colimit-preserving functor — are not of the same type until the two
multiplications by `f` and the two quotient maps have been identified. -/
public def isColimitCokernelCoforkCongr {C : Type*} [Category C] [HasZeroMorphisms C]
    {M N : C} {α α' : M ⟶ M} (hα : α = α') {p p' : M ⟶ N} (hp : p = p')
    (w : α ≫ p = 0) (w' : α' ≫ p' = 0)
    (h : IsColimit (CokernelCofork.ofπ (f := α) p w)) :
    IsColimit (CokernelCofork.ofπ (f := α') p' w') := by
  subst hα hp
  exact h

/-- **Monicity of the map induced on two cokernels does not depend on the presentations it is
read through.** Given a commuting square `φ` between `α` and `β` and two cokernel presentations
of each of `α` and `β`, the two induced maps are conjugate by the comparison isomorphisms of the
presentations — each square being checked by cancelling the epimorphism that a cokernel
projection is — so one is a monomorphism exactly when the other is. -/
public theorem mono_of_isColimit_cokernelCofork {C : Type*} [Category C] [HasZeroMorphisms C]
    {M N P₁ P₂ Q₁ Q₂ : C} {α : M ⟶ M} {β : N ⟶ N} {φ : M ⟶ N}
    {p₁ : M ⟶ P₁} {w₁ : α ≫ p₁ = 0} (h₁ : IsColimit (CokernelCofork.ofπ p₁ w₁))
    {p₂ : N ⟶ P₂} {w₂ : β ≫ p₂ = 0} (h₂ : IsColimit (CokernelCofork.ofπ p₂ w₂))
    {q₁ : M ⟶ Q₁} {v₁ : α ≫ q₁ = 0} (k₁ : IsColimit (CokernelCofork.ofπ q₁ v₁))
    {q₂ : N ⟶ Q₂} {v₂ : β ≫ q₂ = 0} (k₂ : IsColimit (CokernelCofork.ofπ q₂ v₂))
    {g : P₁ ⟶ P₂} (hg : φ ≫ p₂ = p₁ ≫ g)
    {g' : Q₁ ⟶ Q₂} (hg' : φ ≫ q₂ = q₁ ≫ g') (hmono : Mono g') : Mono g := by
  have : Epi p₁ := epi_of_isColimit_cofork h₁
  let e₁ : P₁ ≅ Q₁ := IsColimit.coconePointUniqueUpToIso h₁ k₁
  let e₂ : P₂ ≅ Q₂ := IsColimit.coconePointUniqueUpToIso h₂ k₂
  have hp₁ : p₁ ≫ e₁.hom = q₁ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom h₁ k₁ WalkingParallelPair.one
  have hp₂ : p₂ ≫ e₂.hom = q₂ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom h₂ k₂ WalkingParallelPair.one
  have hsq : g ≫ e₂.hom = e₁.hom ≫ g' := by
    refine (cancel_epi p₁).1 ?_
    rw [← Category.assoc, ← hg, Category.assoc, hp₂, hg', ← hp₁, Category.assoc]
  have : Mono (g ≫ e₂.hom) := by
    rw [hsq]
    exact mono_comp _ _
  exact mono_of_mono g e₂.hom

/-! ### Multiplication by a global section, against the tensor product -/

/-- Multiplication by a global section is the natural endomorphism of the identity functor that
the section's restrictions give, with no power taken. -/
public theorem smulPowHom_one_eq (X : Scheme.{u}) (G : X.Modules) (c : Γ(X, ⊤)) :
    smulPowHom G c 1 =
      (globalSectionToEnd X.ringCatSheaf
        (terminalSection X.ringCatSheaf ⊤ isTerminalTop c)).app G := by
  rw [smulPowHom, pow_one]
  rfl

/-- **Multiplication by a global section of `𝒪_X` commutes with tensoring on the right**, at the
spelling `Stacks.RelativeVeryAmple.tensorModules` the twists of a coherent triple are written in.

This is `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`: the functor
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules X P` *is*
`AlgebraicGeometry.SheafOfModules.sheafTensorRight X.sheaf P`, by `rfl`, both being the composite
of the forgetful functor to presheaves of modules, the objectwise tensor product with `P`, and
sheafification. -/
public theorem tensorModulesMap_smulPowHom_one (X : Scheme.{u}) (M P : X.Modules)
    (c : Γ(X, ⊤)) :
    tensorModulesMap X (smulPowHom M c 1) (𝟙 P) = smulPowHom (tensorModules X M P) c 1 :=
  let : ∀ U, IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) :=
    fun U => inferInstanceAs (IsMulCommutative (X.presheaf.obj U))
  (tensorRightModules_map X P (smulPowHom M c 1)).symm.trans
    ((congrArg (fun t : M ⟶ M => (tensorRightModules X P).map t)
        (smulPowHom_one_eq X M c)).trans
      ((AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd X.sheaf P
          (terminalSection X.ringCatSheaf ⊤ isTerminalTop c) M).trans
        (smulPowHom_one_eq X (tensorModules X M P) c).symm))

/-- The quotient map of `F` by `c` tensored with `P` kills multiplication by `c` on `F ⊗ P`. -/
public theorem smulPowHom_comp_tensorModulesMap_cokernel_π (X : Scheme.{u}) (F P : X.Modules)
    (c : Γ(X, ⊤)) :
    smulPowHom (tensorModules X F P) c 1 ≫
        tensorModulesMap X (cokernel.π (smulPowHom F c 1)) (𝟙 P) = 0 := by
  have : (tensorRightModules X P).PreservesZeroMorphisms :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms _ X.sheaf P
  rw [← tensorRightModules_map X P (cokernel.π _), 
    ← (tensorRightModules_map X P (smulPowHom F c 1)).trans
      (tensorModulesMap_smulPowHom_one X F P c),
    ← Functor.map_comp, cokernel.condition, Functor.map_zero]

/-- **`(F/cF) ⊗ P` is a cokernel of multiplication by `c` on `F ⊗ P`**, the quotient map being
the quotient map of `F` tensored with `P`. This is right exactness of `- ⊗ P`, [Stacks, Tag
05NB], which holds with no hypothesis on `P`, together with
`Stacks.Algebraization.tensorModulesMap_smulPowHom_one` to identify the image of multiplication
by `c` with multiplication by `c`. -/
public def isColimitCokernelCoforkTensor (X : Scheme.{u}) (F P : X.Modules) (c : Γ(X, ⊤)) :
    IsColimit (CokernelCofork.ofπ (f := smulPowHom (tensorModules X F P) c 1)
      (tensorModulesMap X (cokernel.π (smulPowHom F c 1)) (𝟙 P))
      (smulPowHom_comp_tensorModulesMap_cokernel_π X F P c)) := by
  haveI : (tensorRightModules X P).PreservesZeroMorphisms :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms _ X.sheaf P
  haveI : PreservesFiniteColimits (tensorRightModules X P) :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits _ X.sheaf P
  exact isColimitCokernelCoforkCongr
    ((tensorRightModules_map X P (smulPowHom F c 1)).trans
      (tensorModulesMap_smulPowHom_one X F P c))
    (tensorRightModules_map X P (cokernel.π (smulPowHom F c 1))) _ _
    (isColimitCoforkMapOfIsColimit' (tensorRightModules X P)
      (cokernel.condition (smulPowHom F c 1)) (cokernelIsCokernel _))

/-! ### The hypothesis of the snake step, discharged -/

/-- **The map a snake input of multiplication by `c` induces on the two quotients by `c` is a
monomorphism as soon as the same map on `F/cF` is.** The map in question is
`(Stacks.Algebraization.smulSnakeInput φ c).L₃.f` for `φ = F ⊗ m`, the hypothesis of
`Stacks.Algebraization.mono_smulPowHom_cokernel_of_mono`; the map it is identified with is
`(F/cF) ⊗ m`, which for the induction step of [Stacks, Tag 0F27] is multiplication by the chosen
section of `L` on `F/fF`.

Both of the snake input's own cokernel presentations are
`CategoryTheory.ShortComplex.SnakeInput.h₃τ₁` and `h₃τ₂`, the comparison with the tensor
presentations of `Stacks.Algebraization.isColimitCokernelCoforkTensor` is
`Stacks.Algebraization.mono_of_isColimit_cokernelCofork`, and the square it needs is the
functoriality of the tensor product in its two variables separately. -/
public theorem mono_smulSnakeInput_L₃_f {X : Scheme.{u}} (F P₁ P₂ : X.Modules)
    (m : P₁ ⟶ P₂) (c : Γ(X, ⊤)) [Mono (tensorModulesMap X (𝟙 F) m)]
    (hmono : Mono (tensorModulesMap X (𝟙 (cokernel (smulPowHom F c 1))) m)) :
    Mono (smulSnakeInput (tensorModulesMap X (𝟙 F) m) c).L₃.f := by
  refine mono_of_isColimit_cokernelCofork
    (smulSnakeInput (tensorModulesMap X (𝟙 F) m) c).h₃τ₁
    (smulSnakeInput (tensorModulesMap X (𝟙 F) m) c).h₃τ₂
    (isColimitCokernelCoforkTensor X F P₁ c) (isColimitCokernelCoforkTensor X F P₂ c)
    (smulSnakeInput (tensorModulesMap X (𝟙 F) m) c).v₂₃.comm₁₂.symm ?_ hmono
  show tensorModulesMap X (𝟙 F) m ≫
      tensorModulesMap X (cokernel.π (smulPowHom F c 1)) (𝟙 P₂) =
    tensorModulesMap X (cokernel.π (smulPowHom F c 1)) (𝟙 P₁) ≫
      tensorModulesMap X (𝟙 (cokernel (smulPowHom F c 1))) m
  rw [tensorModulesMap_comp, tensorModulesMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-! ### `f`-torsion-freeness of the quotient -/

/-- The global scalar of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeSnake` and the scalar over
`⊤` of `Stacks.Algebraization.scalarOnOpen` are the same section, on the nose. Recorded because
the quotient `F/fF` is spelled with the first in the snake and with the second everywhere the
associated points of that quotient are produced —
`Stacks.Divisors.associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum` and
`Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` — so without this a
consumer would look for a comparison that is not needed. -/
public theorem scalarOnOpen_top (A : Type u) [CommRing A] [IsLocalRing A] (f : A) :
    scalarOnOpen A f ⊤ = scalarGlobal A f := rfl

/-- **The quotient of `F ⊗ P₁ ⟶ F ⊗ P₂` is `f`-torsion-free as soon as the same map on `F/fF` is
a monomorphism.** This is
`Stacks.Algebraization.isFTorsionFree_cokernel_of_mono` with its hypothesis supplied by
`Stacks.Algebraization.mono_smulSnakeInput_L₃_f`. -/
public theorem isFTorsionFree_cokernel_tensorModulesMap (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    {P₁ P₂ : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (m : P₁ ⟶ P₂)
    [Mono (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme (𝟙 F) m)]
    (hN : IsFTorsionFree A f
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme F P₂))
    (hmono : Mono (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme
      (𝟙 (cokernel (smulPowHom F (scalarGlobal A f) 1))) m)) :
    IsFTorsionFree A f
      (cokernel (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme (𝟙 F) m)) :=
  isFTorsionFree_cokernel_of_mono A f _ hN
    (mono_smulSnakeInput_L₃_f F P₁ P₂ m (scalarGlobal A f) hmono)

/-- **The fifth clause of `Stacks.Algebraization.HasHilbertInductionStep`: the quotient of the
induction step's short exact sequence is `f`-torsion-free.**

The left-hand map of that sequence is
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`, whose punctured-spectrum member is
`T.F ⊗ (multiplication by σ on the powers of L)`; the hypothesis `hmono` is the monicity of the
same map with `T.F` replaced by `T.F / f T.F`, which is
`Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` at that module — and that is
exactly why the induction step chooses its section off `Ass(F) ∪ Ass(F/fF)` and not merely off
`Ass(F)`. The `f`-torsion-freeness of the target, which the snake step also needs, is carried by
the twist `T.twistZ L hL (n + 1)` itself. -/
public theorem CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A} (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) (hmonoφ : Mono (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onPunctured)
    (hmono : letI := hL.invertible_F
      Mono (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme
        (𝟙 (cokernel (smulPowHom T.F (scalarGlobal A f) 1)))
        (mulSectionPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F σ n))) :
    IsFTorsionFree A f (cokernel (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onPunctured) := by
  let := hL.invertible_F
  have : Mono (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme (𝟙 T.F)
      (mulSectionPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F σ n)) := hmonoφ
  exact isFTorsionFree_cokernel_tensorModulesMap A f T.F
    (mulSectionPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F σ n)
    (T.twistZ L hL (n + 1)).torsionFree hmono

/-- **The fifth clause of `Stacks.Algebraization.HasHilbertInductionStep`, with its hypothesis
read back to the associated points of `F/fF`.** This is
`Stacks.Algebraization.CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ` with
`hmono` supplied by `Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` at the
module `F/fF` — the same theorem that
`Stacks.Algebraization.CoherentTriple.mono_onPunctured_mulSectionTwistZ` applies at `F`. The two
nonvanishing hypotheses are the two halves of the union `Ass(F) ∪ Ass(F/fF)` that
`Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` delivers, which is why
the induction step chooses its section off that union. -/
public theorem CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ_of_nonvanishing
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) (hmonoφ : Mono (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onPunctured)
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (hq : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).IsQuasicoherent)
    (hq' : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
          (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
        L.F).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (cokernel (smulPowHom T.F (scalarGlobal A f) 1)),
      ∃ W : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L.F
          (L.F.unitHomEquiv σ)) :
    IsFTorsionFree A f (cokernel (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onPunctured) := by
  let := hL.invertible_F
  have : IsLocallyNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι
  exact CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ T L hL σ σ₀ hcompat n
    hmonoφ (mono_tensorModulesMap_id_mulSectionPowScheme
      (cokernel (smulPowHom T.F (scalarGlobal A f) 1)) L.F n σ hq hq' ψ hW)

end Stacks.Algebraization

end
