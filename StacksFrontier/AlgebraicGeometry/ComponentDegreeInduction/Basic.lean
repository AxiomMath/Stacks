module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The inductive step of [Stacks, Tag 0AYW]: the degree splits along the ideal of the reduction

The second paragraph of the proof of [Stacks, Tag 0AYW] treats an irreducible proper scheme `X`
of dimension at most one over a field. Writing `C = X_{red}` for its reduction, `ℐ` for the ideal
of `C` and `e` for the least exponent with `ℐ^{e+1} = 0`, it argues by induction on `e`. At each
step it sets `ℱ = ℐ^e`, regarded as a coherent module on `C` ([Stacks, Tag 087T]), takes `X'` to
be the closed subscheme cut out by `ℐ^e`, and uses the short exact sequence

`0 ⟶ ℱ ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 0`

of `𝒪_X`-modules, whose outer terms are pushed forward from `C` and from `X'`.

This file proves the arithmetic of that step, in the generality in which the step is actually
used: for **any** short exact sequence of that shape — outer terms the direct images of a
coherent module on one closed subscheme and of the structure sheaf of another — the degree of a
finite locally free `ℰ` splits as

`deg(ℰ) = r · deg(ℰ|_C) + deg(ℰ|_{X'})`

where `r` is the number that [Stacks, Tag 0AYV] attaches to `ℱ`. Nothing about `ℐ`, about
reducedness, about irreducibility or about the exponent `e` enters: the step is a computation
with Euler characteristics, and those three facts are what produce the sequence, not what the
computation uses.

The source's `m = r + m'` and the inductive hypothesis `deg(ℰ|_{X'}) = m' · deg(ℰ|_C)` then give
`deg(ℰ) = m · deg(ℰ|_C)`, which is the conclusion of the tag for irreducible `X`; that last
substitution is recorded as `curveDegree_eq_mul_of_shortExact_pushforward` below.

## The four inputs, and which of them the library has

* **Additivity of `χ`** along the sequence and along its tensor product with `ℰ`
  ([Stacks, Tag 08AA]). Available as
  `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`, whose only
  hypothesis is the finite dimensionality of [Stacks, Tag 02O6]; that is carried here as the
  hypothesis `h02O6`, in the shape the dévissage reductions of
  `StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/BaseCases.lean` produce it.
* **Exactness of `− ⊗ ℰ`**, because `ℰ` is finite locally free hence flat:
  `AlgebraicGeometry.Scheme.Modules.isFlat_of_isFiniteLocallyFree` and
  `Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor`. Unconditional.
* **The projection formula and the cohomology comparison along a closed immersion**, which turn
  the two outer Euler characteristics on `X` into Euler characteristics on `C` and on `X'`:
  `AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion` and
  `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`. Unconditional.
* **[Stacks, Tag 0AYV] on `C`**, carried as the hypothesis `h0AYV`. This is the one genuinely
  absent input. It is stated here exactly as
  the `AlgebraicGeometry` declaration whose name is
  `exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage`
  concludes it, with `r` left as a natural number rather than written as a fibre rank, so that a
  caller supplies `r := AlgebraicGeometry.Scheme.Modules.fiberRank ℱ (genericPoint C)` and no
  irreducibility instance is needed to state the step.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `curveDegree_eq_add_of_shortExact_pushforward`: `deg(ℰ) = r · deg(ℰ|_C) + deg(ℰ|_{X'})`.
* `curveDegree_eq_mul_of_shortExact_pushforward`: the same with the inductive hypothesis
  `deg(ℰ|_{X'}) = m' · deg(ℰ|_C)` and `m = r + m'` substituted, giving
  `deg(ℰ) = m · deg(ℰ|_C)`.

## Implementation notes

**`AlgebraicGeometry.curveDegree` is unfolded to its defining alternating sum, and the
Euler-characteristic statements are converted into it by `curveDegree_eq_eulerCharacteristic_sub`,
which holds by `rfl`.** The degree is defined without a coherence hypothesis while `χ` carries
one, so the conversion is where the coherence witnesses of `ℰ`, of `𝒪_X` and of `𝒪_{X'}` are
consumed. They are arguments rather than instances for the reason recorded in
`StacksFrontier/AlgebraicGeometry/ClosedImmersionEuler/Basic.lean`.

**The rank instances on the restrictions are supplied in the statement, not assumed.**
`deg(ℰ|_C)` and `deg(ℰ|_{X'})` need `ℰ|_C` and `ℰ|_{X'}` to be finite locally free of rank `n`,
which is `AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback` rather than an instance; it is
passed positionally with `@`, so the statement adds no hypothesis beyond the one on `ℰ`.

**No attribute for [Stacks, Tag 0AYW] is attached.** These statements carry the short exact
sequence, the finiteness of [Stacks, Tag 02O6] and [Stacks, Tag 0AYV] as hypotheses, and the
second also carries the inductive hypothesis; none of the three is the tag, and the tag's own
conclusion is a sum over the one-dimensional components of an arbitrary `X`.

## What this leaves open in [Stacks, Tag 0AYW]

Two of the three ingredients of the second paragraph are theorems. The length computation
`m = r + m'` at the generic point is
`Stacks.AlgebraicGeometry.ComponentDegrees.componentMultiplicity_eq_fiberRank_add_of_shortExact`,
and the first paragraph — the reduction of an arbitrary `X` to an irreducible one — is
`AlgebraicGeometry.exists_curveDegree_eq_sum_irreducibleComponent`. What is left is the short
exact sequence, and the induction on `e` that consumes it.

**Every ingredient of that sequence is in the library; what is missing is only the assembly.**
The ideal sheaf of the reduction, its powers, the subschemes they cut out and the nilpotence of
[Stacks, Tag 01Y9] are all available:

* the ideal sheaf of the reduction is `AlgebraicGeometry.Scheme.nilradical`, with the reduction
  itself `AlgebraicGeometry.Scheme.reduction` and `AlgebraicGeometry.Scheme.reductionι`;
* its powers are the `Pow` instance on `AlgebraicGeometry.Scheme.IdealSheafData`, computed by
  `AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow`; the subschemes they cut out are
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, and
  `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` is the closed immersion between two of
  them;
* the nilpotence `ℐ^{e+1} = 0` is `AlgebraicGeometry.exists_nilradical_pow_succ_eq_bot` of
  `StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic`, and [Stacks, Tag 01Y9] itself is
  `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`;
* the generic closed-immersion sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_*𝒪_D ⟶ 0` is
  `Stacks.IdealSheafSequence.divisorIdeal_shortExact`, and its first term is the subsheaf
  `Stacks.Algebraization.idealModule` of the structure sheaf by
  `Stacks.Algebraization.idealPowerMultiple_unit_eq_kernel`, whose sections over an affine open
  `U` are the ideal `D(U)` by `Stacks.Algebraization.idealModule_obj_affine`;
* [Stacks, Tag 087T], which rewrites that first term as a direct image from the reduction as
  soon as `ℐ` annihilates it, is
  `AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero`, with the annihilation
  predicate `Stacks.ClosedImmersion.AnnihilatedByKer` and its affine-open criterion
  `Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`.

So what the sequence still needs is the one affine-local statement that `ℐ` annihilates
`ℐ^e·𝒪_X` when `ℐ^{e+1} = 0`. It is elementary, and the obstruction to writing it down is
notational: the sections of `Stacks.ClosedImmersion.idealSheaf` are spelled over
`RingedSpaceModuleAdjunction.structureSheafRing` of the ringed space while
`Stacks.ClosedImmersion.AnnihilatedByKer` is spelled over
`AlgebraicGeometry.Scheme.ringCatSheaf`, and the scalar action of one spelling does not find its
instances in the other. The induction on `e` needs, besides the sequence, the nilradical of
`(ℐ^e).subscheme` to be the image of `ℐ`; `AlgebraicGeometry.Scheme.IdealSheafData.map` and
`.comap` have no compatibility with `*` or `^`, so that comparison has to be made affine-locally
too.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X C W : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The inductive step of [Stacks, Tag 0AYW]: the degree splits along a short exact sequence
`0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_W ⟶ 0`.**

For `j : C ⟶ X` and `i : W ⟶ X` closed immersions, `ℱ` coherent on `C`, and `ℰ` finite locally
free of rank `n` on `X`,

`deg(ℰ) = r · deg(ℰ|_C) + deg(ℰ|_W)`

where `r` is the coefficient that [Stacks, Tag 0AYV] attaches to `ℱ` on `C`, carried here as the
hypothesis `h0AYV`. The finiteness of [Stacks, Tag 02O6] on `X` is carried as `h02O6`.

The proof is the computation of the source: tensoring the sequence with the flat module `ℰ` and
adding Euler characteristics twice,

`χ(ℰ) - n·χ(𝒪_X) = [χ(ℱ ⊗ ℰ|_C) + χ(ℰ|_W)] - n·[χ(ℱ) + χ(𝒪_W)]`,

and the bracket on the left becomes `r · deg(ℰ|_C) + n · χ(ℱ)` by `h0AYV`, cancelling the
`n · χ(ℱ)` on the right. -/
theorem curveDegree_eq_add_of_shortExact_pushforward [IsProper f] [IsLocallyNoetherian X]
    (j : C ⟶ X) [IsClosedImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    (hX : topologicalKrullDim X ≤ 1) (hC : topologicalKrullDim C ≤ 1)
    (hW : topologicalKrullDim W ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : C.Modules) (hF : SheafOfModules.IsCoherent F)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOW : SheafOfModules.IsCoherent (SheafOfModules.unit W.ringCatSheaf))
    (hEC : SheafOfModules.IsCoherent ((Scheme.Modules.pullback j).obj E))
    (hEW : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E))
    (α : (Scheme.Modules.pushforward j).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (β : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (r : ℕ)
    (h0AYV : @eulerCharacteristic k _ C (j ≫ f) _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
                (((Scheme.Modules.pullback j).obj E))).obj (F)))
          (@SheafOfModules.tensorSheaf_isCoherent C.toRingedSpace _ F hEC hF) =
        (r : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
            (isFiniteLocallyFreeOfRank_pullback j E n) +
          (n : ℤ) * @eulerCharacteristic k _ C (j ≫ f) _ F hF) :
    curveDegree k f hX E n =
      (r : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
          (isFiniteLocallyFreeOfRank_pullback j E n) +
        @curveDegree k _ W (i ≫ f) _ hW ((Scheme.Modules.pullback i).obj E) n
          (isFiniteLocallyFreeOfRank_pullback i E n) := by
  classical
  set S : ShortComplex X.Modules := ShortComplex.mk α β w with hSdef
  -- coherence of the three terms of the sequence
  have hpushF : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward j).obj F) :=
    @isCoherent_pushforward_of_isClosedImmersion C X j _ _ F hF
  have hpushOW : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) :=
    @isCoherent_pushforward_of_isClosedImmersion W X i _ _ _ hOW
  -- additivity along the sequence itself
  have hadd : @eulerCharacteristic k _ X f _ S.X₂ hOX =
      @eulerCharacteristic k _ X f _ S.X₁ hpushF +
        @eulerCharacteristic k _ X f _ S.X₃ hpushOW :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ S hS
      hpushF hOX hpushOW (h02O6 _ hpushF) (h02O6 _ hpushOW)
  -- the sequence tensored with `E` is again short exact, `E` being flat
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ E n (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X E hfl
  obtain ⟨h0, hse⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor S E hS hflat
  have c : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj G).obj E)).IsCoherent :=
    fun G hG => @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace G E hG hE
  have c₁ := c S.X₁ hpushF
  have c₂ := c S.X₂ hOX
  have c₃ := c S.X₃ hpushOW
  have haddT : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (S.X₂)).obj (E))) c₂ =
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                (S.X₁)).obj (E))) c₁ +
        @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                (S.X₃)).obj (E))) c₃ :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse c₁ c₂ c₃
      (h02O6 _ c₁) (h02O6 _ c₃)
  -- the four identifications of Euler characteristics across the two closed immersions
  have e₁ : @eulerCharacteristic k _ X f _ S.X₁ hpushF =
      @eulerCharacteristic k _ C (j ≫ f) _ F hF :=
    eulerCharacteristic_pushforward_of_isClosedImmersion k j f F hF hpushF
  have e₃ : @eulerCharacteristic k _ X f _ S.X₃ hpushOW =
      @eulerCharacteristic k _ W (i ≫ f) _ (SheafOfModules.unit W.ringCatSheaf) hOW :=
    eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hOW hpushOW
  have t₁ : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (S.X₁)).obj (E))) c₁ =
      @eulerCharacteristic k _ C (j ≫ f) _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
              (F)).obj (((Scheme.Modules.pullback j).obj E))))
        (@SheafOfModules.tensorSheaf_isCoherent C.toRingedSpace F _ hF hEC) :=
    eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k j f F E hF hE hpushF hEC
  have t₃ : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (S.X₃)).obj (E))) c₃ =
      @eulerCharacteristic k _ W (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEW :=
    eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k i f E hE hOW
      hpushOW hEW
  have t₂ : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (S.X₂)).obj (E))) c₂ =
      @eulerCharacteristic k _ X f _ E hE :=
    eulerCharacteristic_unit_tensorSheaf k f E hE hOX
  -- the swap putting `h0AYV` in the argument order the projection formula produces
  have tcomm : @eulerCharacteristic k _ C (j ≫ f) _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
              (F)).obj (((Scheme.Modules.pullback j).obj E))))
        (@SheafOfModules.tensorSheaf_isCoherent C.toRingedSpace F _ hF hEC) =
      @eulerCharacteristic k _ C (j ≫ f) _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pullback j).obj E))).obj (F)))
        (@SheafOfModules.tensorSheaf_isCoherent C.toRingedSpace _ F hEC hF) :=
    @eulerCharacteristic_tensorSheaf_comm k _ C (j ≫ f) _ F _ hF hEC
  -- assemble
  have hdegX : curveDegree k f hX E n =
      @eulerCharacteristic k _ X f _ E hE -
        (n : ℤ) * @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf) hOX :=
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hX E n _ hE hOX
  have hdegW : @curveDegree k _ W (i ≫ f) _ hW ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) =
      @eulerCharacteristic k _ W (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEW -
        (n : ℤ) * @eulerCharacteristic k _ W (i ≫ f) _
          (SheafOfModules.unit W.ringCatSheaf) hOW :=
    @curveDegree_eq_eulerCharacteristic_sub k _ W (i ≫ f) _ hW _ n
      (isFiniteLocallyFreeOfRank_pullback i E n) hEW hOW
  rw [hdegX, hdegW, ← t₂, haddT, t₁, t₃, tcomm, h0AYV, hadd, e₁, e₃]
  ring

/-- **The inductive step of [Stacks, Tag 0AYW], with the inductive hypothesis substituted.**
Under the hypotheses of `AlgebraicGeometry.curveDegree_eq_add_of_shortExact_pushforward`,
together with the source's length identity `m = r + m'` and the inductive hypothesis
`deg(ℰ|_W) = m' · deg(ℰ|_C)`, the degree on `X` is `m · deg(ℰ|_C)`.

This is the conclusion of [Stacks, Tag 0AYW] for an irreducible `X`, where `C` is the reduction
and `m` its multiplicity — modulo what the module docstring lists as still open. -/
theorem curveDegree_eq_mul_of_shortExact_pushforward [IsProper f] [IsLocallyNoetherian X]
    (j : C ⟶ X) [IsClosedImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    (hX : topologicalKrullDim X ≤ 1) (hC : topologicalKrullDim C ≤ 1)
    (hW : topologicalKrullDim W ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : C.Modules) (hF : SheafOfModules.IsCoherent F)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOW : SheafOfModules.IsCoherent (SheafOfModules.unit W.ringCatSheaf))
    (hEC : SheafOfModules.IsCoherent ((Scheme.Modules.pullback j).obj E))
    (hEW : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E))
    (α : (Scheme.Modules.pushforward j).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (β : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (r : ℕ)
    (h0AYV : @eulerCharacteristic k _ C (j ≫ f) _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
                (((Scheme.Modules.pullback j).obj E))).obj (F)))
          (@SheafOfModules.tensorSheaf_isCoherent C.toRingedSpace _ F hEC hF) =
        (r : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
            (isFiniteLocallyFreeOfRank_pullback j E n) +
          (n : ℤ) * @eulerCharacteristic k _ C (j ≫ f) _ F hF)
    (m m' : ℕ) (hm : m = r + m')
    (hind : @curveDegree k _ W (i ≫ f) _ hW ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) =
      (m' : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
        (isFiniteLocallyFreeOfRank_pullback j E n)) :
    curveDegree k f hX E n =
      (m : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
        (isFiniteLocallyFreeOfRank_pullback j E n) := by
  rw [curveDegree_eq_add_of_shortExact_pushforward k f j i hX hC hW E n F hF hE hOX hOW hEC hEW
      α β w hS h02O6 r h0AYV, hind, hm]
  push_cast
  ring

end AlgebraicGeometry

end
