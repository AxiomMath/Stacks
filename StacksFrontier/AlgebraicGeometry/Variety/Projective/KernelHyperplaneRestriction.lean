module

public import StacksFrontier.Algebra.Homology.ShortComplex.CokernelOfMonoMorphism
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionFiniteFamily
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackFreeIso
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelRegularityBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a short exact sequence of modules to a hyperplane

Let `s` be a global section of `𝒪(1)` on `ℙⁿ_k` and let `i : H ⟶ ℙⁿ_k` be the hyperplane it cuts
out. Pullback along `i` is only right exact, so the restriction of a short exact sequence

`0 ⟶ 𝒦 ⟶ ℰ ⟶ ℱ ⟶ 0`

of `𝒪`-modules need not stay short exact. It does when `s` avoids the associated points of all
three terms, and that is what this file proves. It is the step the induction on the dimension in
[Stacks, Tag 08AG] needs: there `ℰ = 𝒪^{⊕r}` is free and `𝒦` is the kernel of a surjection onto
`ℱ`, and the conclusion says that `i^*𝒦` is again the kernel of a surjection of a free module
onto `i^*ℱ`, so that the inductive hypothesis applies to it on the hyperplane.

## Main results

* `AlgebraicGeometry.mono_pullback_hyperplaneι_map_f`: **the restriction of the first map stays a
  monomorphism.** This is the whole content; the hypotheses are that multiplication by `s` is a
  monomorphism on each of the three terms.
* `AlgebraicGeometry.mono_pullback_map_of_isoComp`: the same conclusion after the hyperplane is
  reparametrised by an isomorphism of schemes — for `ℙⁿ_k` that reparametrisation is
  [Stacks, Tag 089Z], which presents the hyperplane as `ℙ^{n-1}_k`.
* `AlgebraicGeometry.shortExact_map_pullback_of_mono`: a short exact sequence whose restriction
  has monic first map restricts to a short exact sequence, pullback of modules being a left
  adjoint.
* `AlgebraicGeometry.epi_pullbackFreeQuotientHom_and_nonempty_iso`: **the restricted kernel is
  again the kernel of a surjection of `𝒪^{⊕r}`**, which is what makes the inductive hypothesis of
  [Stacks, Tag 08AG] applicable to it. Its two definitions are
  `AlgebraicGeometry.pullbackFreeModulesIso`, the restriction of `𝒪^{⊕r}`, and
  `AlgebraicGeometry.pullbackFreeQuotientHom`, the restricted quotient map read out of `𝒪^{⊕r}`.
* `AlgebraicGeometry.isMRegular_of_iso`: `m`-regularity transports along an isomorphism of
  coherent sheaves.
* `AlgebraicGeometry.hilbertPolynomial_sub_eq_of_restrictionSequence`: the Hilbert polynomial of
  the restriction of a coherent sheaf to the hyperplane is the first difference of its own, read
  off one given restriction sequence.

## The mathematics

The argument is the source's, and it is [Stacks, Tag 010H] on the ladder of multiplications by
`s`:

```
0 ⟶ 𝒦(-1) ⟶ ℰ(-1) ⟶ ℱ(-1) ⟶ 0
       |         |        |
0 ⟶   𝒦   ⟶    ℰ   ⟶   ℱ   ⟶ 0
```

whose rows are the given sequence and its twist by `-1` — short exact because the twist is an
equivalence of categories — and whose vertical maps are multiplication by `s`, a morphism of
short exact sequences by
`…ProjectiveSpaceSectionFiniteFamily.twistSectionMulNegOne_naturality`. The right-hand vertical
is a monomorphism, so `CategoryTheory.ShortComplex.shortExact_cokernelShortComplex` makes the
sequence of cokernels of the verticals short exact. Each of those cokernels is the restriction to
the hyperplane: the sequence of [Stacks, Tag 08A0] exhibits `𝒢 ⟶ i_* i^* 𝒢` as a cokernel of
multiplication by `s`
(`…ProjectiveSpaceSectionMultiplication.exists_cokernelIso_hyperplaneUnit`), and the
identification is compatible with the three maps because that arrow is the unit of `i^* ⊣ i_*`,
which is natural. So `i_* i^* ` of the first map is a monomorphism, and `i_*` is faithful along a
closed immersion ([Stacks, Tag 08KS],
`Stacks.ClosedImmersion.faithful_pushforward`), so the first map itself is one.

No hypothesis on the base: the three monicity hypotheses are exactly what a section avoiding the
associated points of the three terms provides, by
`…ProjectiveSpaceHyperplaneSection.mono_twistSectionMulNegOne_of_nonvanishing`.

## References

* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 010H](https://stacks.math.columbia.edu/tag/010H)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 08A1](https://stacks.math.columbia.edu/tag/08A1)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily
  (twistSectionMulNegOne_naturality)

universe u

namespace AlgebraicGeometry

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.tensorMonoidal

/-! ### The restriction of the first map of a short exact sequence -/

/-- **Multiplication by a global section of `𝒪(1)` restricts a short exact sequence of modules on
`ℙⁿ_k` to a sequence whose first map is still a monomorphism.** The hypotheses are that
multiplication by `s` is a monomorphism `𝒢(-1) ⟶ 𝒢` on each of the three terms `𝒢` of the
sequence, which for a coherent `𝒢` says that the hyperplane `V(s)` contains no associated point
of it.

See the module documentation for the argument: the ladder of multiplications by `s` has monic
right-hand column, so its cokernels form a short exact sequence; those cokernels are the direct
images of the restrictions, compatibly with the maps because the comparison arrow is the unit of
the adjunction; and the direct image along a closed immersion is faithful. -/
theorem mono_pullback_hyperplaneι_map_f (k : Type u) [Field k] (n : ℕ)
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    {S : ShortComplex (projectiveSpaceOverRing n (CommRingCat.of k)).Modules}
    (hS : S.ShortExact)
    (h₁ : Mono (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s))
    (h₂ : Mono (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₂ s))
    (h₃ : Mono (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₃ s)) :
    Mono ((Scheme.Modules.pullback
      (hyperplaneι n (Spec (CommRingCat.of k)) s)).map S.f) := by
  have := h₁
  have := h₂
  have hT : (S.map (twistFunctorModules k n (-1))).ShortExact :=
    hS.map_of_exact (twistFunctorModules k n (-1))
  have comm₁ : twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s ≫ S.f
      = (twistFunctorModules k n (-1)).map S.f ≫
        twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₂ s :=
    (twistSectionMulNegOne_naturality n (Spec (CommRingCat.of k)) S.f s).symm
  have comm₂ : twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₂ s ≫ S.g
      = (twistFunctorModules k n (-1)).map S.g ≫
        twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₃ s :=
    (twistSectionMulNegOne_naturality n (Spec (CommRingCat.of k)) S.g s).symm
  have hmono : Mono (S.cokernelShortComplex comm₁ comm₂).f :=
    (@ShortComplex.shortExact_cokernelShortComplex _ _ _ S _ _ _ _ _ _ _ _
      comm₁ comm₂ _ hT hS h₃).mono_f
  have key := fun F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules =>
    exists_cokernelIso_hyperplaneUnit n (Spec (CommRingCat.of k)) F s
      (twistSectionMulNegOne_comp_hyperplaneUnit n (Spec (CommRingCat.of k)) F s)
      (isIso_unit_app_cokernel_twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s)
  obtain ⟨e₁, he₁⟩ := key S.X₁
  obtain ⟨e₂, he₂⟩ := key S.X₂
  have hπ : cokernel.π (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s) ≫
        (S.cokernelShortComplex comm₁ comm₂).f
      = S.f ≫ cokernel.π (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₂ s) :=
    cokernel.π_desc _ _ _
  have h1 : cokernel.π (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s) ≫
        ((S.cokernelShortComplex comm₁ comm₂).f ≫ e₂.hom)
      = S.f ≫ hyperplaneUnit n (Spec (CommRingCat.of k)) S.X₂ s :=
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ e₂.hom) hπ).trans <|
      (Category.assoc _ _ _).trans <| congrArg (S.f ≫ ·) he₂
  have h2 : cokernel.π (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s) ≫
        (e₁.hom ≫ (Scheme.Modules.pushforward
          (hyperplaneι n (Spec (CommRingCat.of k)) s)).map
          ((Scheme.Modules.pullback (hyperplaneι n (Spec (CommRingCat.of k)) s)).map S.f))
      = S.f ≫ hyperplaneUnit n (Spec (CommRingCat.of k)) S.X₂ s :=
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) he₁).trans <|
      (Scheme.Modules.pullbackPushforwardAdjunction
        (hyperplaneι n (Spec (CommRingCat.of k)) s)).unit_naturality S.f
  have hsq : (S.cokernelShortComplex comm₁ comm₂).f ≫ e₂.hom
      = e₁.hom ≫ (Scheme.Modules.pushforward (hyperplaneι n (Spec (CommRingCat.of k)) s)).map
        ((Scheme.Modules.pullback (hyperplaneι n (Spec (CommRingCat.of k)) s)).map S.f) :=
    (cancel_epi (cokernel.π
      (twistSectionMulNegOne n (Spec (CommRingCat.of k)) S.X₁ s))).mp (h1.trans h2.symm)
  have := Stacks.ClosedImmersion.faithful_pushforward
    (hyperplaneι n (Spec (CommRingCat.of k)) s)
  refine (Scheme.Modules.pushforward
    (hyperplaneι n (Spec (CommRingCat.of k)) s)).mono_of_mono_map ?_
  rw [(Iso.eq_inv_comp e₁).mpr hsq.symm]
  exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso e₁.inv) _
    (@mono_comp _ _ _ _ _ _ hmono _ (IsIso.mono_of_iso e₂.hom))

/-! ### Reparametrising the hyperplane, and short exactness of the restriction -/

/-- **A monomorphism of restrictions along a morphism stays one after the source is
reparametrised.** If `i^*a` is a monomorphism and `j = φ ≫ i` with `φ` an isomorphism of schemes,
then `j^*a` is a monomorphism: `j^* ≅ φ^* ∘ i^*` by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, and pullback along an isomorphism is an
equivalence of categories (`AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`) and so left
exact.

This is the companion of `AlgebraicGeometry.pullback_eq_zero_of_isoComp` for monicity; on
`ℙⁿ_k` the reparametrisation is the identification of the hyperplane with `ℙ^{n-1}_k` of
[Stacks, Tag 089Z]. -/
theorem mono_pullback_map_of_isoComp {Pm Hy Y : Scheme.{u}} (φ : Pm ≅ Hy) (i : Hy ⟶ Y)
    {A B : Y.Modules} (a : A ⟶ B) (h : Mono ((Scheme.Modules.pullback i).map a)) :
    Mono ((Scheme.Modules.pullback (φ.hom ≫ i)).map a) := by
  have := h
  have : Mono ((Scheme.Modules.pullback φ.hom).map ((Scheme.Modules.pullback i).map a)) :=
    preserves_mono_of_preservesLimit _ _
  have heq : (Scheme.Modules.pullback (φ.hom ≫ i)).map a
      = (Scheme.Modules.pullbackComp φ.hom i).inv.app A ≫
        (Scheme.Modules.pullback φ.hom).map ((Scheme.Modules.pullback i).map a) ≫
        (Scheme.Modules.pullbackComp φ.hom i).hom.app B :=
    (NatIso.naturality_1 (Scheme.Modules.pullbackComp φ.hom i) a).symm
  rw [heq]
  infer_instance

/-- **A short exact sequence whose restriction has monic first map restricts to a short exact
sequence.** Pullback of modules is a left adjoint, so it carries the presentation of the third
term as a cokernel of the first map to a presentation of the restricted third term as a cokernel
of the restricted first map; that gives exactness in the middle and surjectivity on the right,
and monicity on the left is the hypothesis.

This is `Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_kernelSequence` with its
geometric monicity input abstracted: there it comes from the quotient being invertible, here it is
`AlgebraicGeometry.mono_pullback_hyperplaneι_map_f`. -/
theorem shortExact_map_pullback_of_mono {X X' : Scheme.{u}} (g : X' ⟶ X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hm : Mono ((Scheme.Modules.pullback g).map S.f)) :
    (S.map (Scheme.Modules.pullback g)).ShortExact := by
  have hc : IsColimit (CokernelCofork.ofπ (S.map (Scheme.Modules.pullback g)).g
      (S.map (Scheme.Modules.pullback g)).zero) :=
    CokernelCofork.mapIsColimit _ hS.gIsCokernel (Scheme.Modules.pullback g)
  exact ShortComplex.ShortExact.mk'
    ((S.map (Scheme.Modules.pullback g)).exact_of_g_is_cokernel hc) hm
    (Limits.epi_of_isColimit_cofork hc)

/-! ### The restriction of the kernel of a surjection from a free module -/

/-- **The rank-`r` free module, as the free module on a lifted index type.** `𝒪^{⊕r}` is spelled
as the coproduct of `r` copies of the structure sheaf (`AlgebraicGeometry.freeModules`), indexed
by `Fin r`; Mathlib's `SheafOfModules.free` asks for an index type in the universe of the sheaf.
The two are the same coproduct read along `Equiv.ulift`. -/
def freeModulesIsoFree (X : Scheme.{u}) (r : ℕ) :
    (∐ fun _ : Fin r => Stacks.Ample.unitModule X) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) :=
  Limits.Sigma.whiskerEquiv (g := fun _ : ULift.{u} (Fin r) => Stacks.Ample.unitModule X)
    Equiv.ulift.symm fun _ => Iso.refl _

/-- **The pullback of `𝒪^{⊕r}` is `𝒪^{⊕r}`.** Pullback of modules carries the structure sheaf
to the structure sheaf and preserves coproducts, being a left adjoint; this is
`AlgebraicGeometry.Grassmannian.pullbackFreeIso` read at the coproduct spelling of
`AlgebraicGeometry.freeModules`, which is the spelling in which a surjection onto a coherent
sheaf is stated, and for an arbitrary morphism of schemes rather than only a hyperplane. -/
@[sga "4 IV 13.4" "special case"]
def pullbackFreeModulesIso {X Y : Scheme.{u}} (g : X ⟶ Y) (r : ℕ) :
    (Scheme.Modules.pullback g).obj (∐ fun _ : Fin r => Stacks.Ample.unitModule Y) ≅
      ∐ fun _ : Fin r => Stacks.Ample.unitModule X :=
  (Scheme.Modules.pullback g).mapIso (freeModulesIsoFree Y r) ≪≫
    Grassmannian.pullbackFreeIso g r ≪≫ (freeModulesIsoFree X r).symm

/-- **The restriction along `g` of the quotient map `𝒪^{⊕r} ⟶ 𝒬`, read as a map out of
`𝒪^{⊕r}`**: the restriction of `q` precomposed with
`AlgebraicGeometry.pullbackFreeModulesIso`. -/
def pullbackFreeQuotientHom {X Y : Scheme.{u}} (g : X ⟶ Y) {r : ℕ} {Q : Y.Modules}
    (q : (∐ fun _ : Fin r => Stacks.Ample.unitModule Y) ⟶ Q) :
    (∐ fun _ : Fin r => Stacks.Ample.unitModule X) ⟶ (Scheme.Modules.pullback g).obj Q :=
  (pullbackFreeModulesIso g r).inv ≫ (Scheme.Modules.pullback g).map q

/-- **The restriction of a presentation `0 ⟶ 𝒦 ⟶ 𝒪^{⊕r} ⟶ 𝒬 ⟶ 0` is a presentation.** If the
restriction along `g` of the kernel sequence of an epimorphism `q : 𝒪^{⊕r} ⟶ 𝒬` is short exact,
then it is the kernel sequence of `AlgebraicGeometry.pullbackFreeQuotientHom g q`, which is again
an epimorphism out of the free module of rank `r`.

This is what the induction of [Stacks, Tag 08AG] applies its inductive hypothesis to: the
restricted kernel is once more the kernel of a surjection of the rank-`r` free module onto a
coherent sheaf. -/
theorem epi_pullbackFreeQuotientHom_and_nonempty_iso {X Y : Scheme.{u}} (g : X ⟶ Y) {r : ℕ}
    {Q : Y.Modules} (q : (∐ fun _ : Fin r => Stacks.Ample.unitModule Y) ⟶ Q)
    (hse : ((ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
      (Scheme.Modules.pullback g)).ShortExact) :
    Epi (pullbackFreeQuotientHom g q) ∧
      Nonempty ((Scheme.Modules.pullback g).obj (kernel q) ≅
        kernel (pullbackFreeQuotientHom g q)) := by
  have hzero : ((Scheme.Modules.pullback g).map (kernel.ι q) ≫
        (pullbackFreeModulesIso g r).hom) ≫ pullbackFreeQuotientHom g q = 0 := by
    rw [pullbackFreeQuotientHom, Category.assoc, Iso.hom_inv_id_assoc,
      ← CategoryTheory.Functor.map_comp, kernel.condition,
      CategoryTheory.Functor.map_zero]
  have hT : (ShortComplex.mk ((Scheme.Modules.pullback g).map (kernel.ι q) ≫
      (pullbackFreeModulesIso g r).hom) (pullbackFreeQuotientHom g q) hzero).ShortExact := by
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk
        (S₁ := (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
          (Scheme.Modules.pullback g))
        (Iso.refl _) (pullbackFreeModulesIso g r) (Iso.refl _) ?_ ?_) hse
    · simp
    · simp [pullbackFreeQuotientHom]
  exact ⟨hT.epi_g, ⟨IsLimit.conePointUniqueUpToIso hT.fIsKernel
    (limit.isLimit (parallelPair (pullbackFreeQuotientHom g q) 0))⟩⟩

/-! ### Regularity and the Hilbert polynomial along the restriction -/

/-- **`m`-regularity only depends on the isomorphism class of a coherent sheaf.** The twists of
isomorphic sheaves are isomorphic, and cohomology is a functor. There is no such transport in the
library: `AlgebraicGeometry.IsMRegular` is an `abbrev` for a conjunction of vanishing statements,
and this unfolds it and moves each one across the induced isomorphism of cohomology groups. -/
theorem isMRegular_of_iso (k : Type u) [Field k] (n : ℕ)
    {F G : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules} (hFc : F.IsCoherent)
    (hGc : G.IsCoherent) (e : F ≅ G) {m : ℤ} (hF : @IsMRegular k _ n F hFc m) :
    @IsMRegular k _ n G hGc m := fun i hi hin =>
  (hF i hi hin).of_iso
    ((Hfunctor (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf ⊤ i).mapIso
      ((twistFunctorModules k n (m - i)).mapIso e.symm))

/-- **The first difference of the Hilbert polynomial of `𝒬` is the Hilbert polynomial of the
restriction of `𝒬` to a hyperplane**, read off one restriction sequence

`0 ⟶ 𝒬(d-1) ⟶ 𝒬(d) ⟶ j_*(𝒢(d)) ⟶ 0`

at the degree `d`. This is the displayed equation in the proof of [Stacks, Tag 08AC], and in
[Stacks, Tag 08AG] it is what identifies the Hilbert polynomial of the restricted quotient as
`P(t) - P(t-1)`.

Additivity of the Euler characteristic along the sequence is
`AlgebraicGeometry.hilbertPolynomial_sub_eq_eulerCharacteristic_of_shortExact'`, and the passage
from `ℙ^{n+1}_k` down to `ℙⁿ_k` is [Stacks, Tag 089W] along the affine morphism `j`, which lies
over `Spec k`. Compare `AlgebraicGeometry.exists_coherent_hilbertPolynomial_sub_eq`, which is this
with the hyperplane and the restriction chosen rather than given. -/
@[sga "6 XIII 1.7" "partial"]
theorem hilbertPolynomial_sub_eq_of_restrictionSequence (k : Type u) [Field k] (n : ℕ)
    {j : projectiveSpaceOverRing n (CommRingCat.of k) ⟶
      projectiveSpaceOverRing (n + 1) (CommRingCat.of k)} [IsAffineHom j]
    (hj : j ≫ (projectiveSpaceOverRing (n + 1) (CommRingCat.of k) ↘
        Spec (CommRingCat.of k)) =
      projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
    (Q : (projectiveSpaceOverRing (n + 1) (CommRingCat.of k)).Modules) [Q.IsCoherent]
    (G : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) (hG : G.IsCoherent) (d : ℤ)
    {S : ShortComplex (projectiveSpaceOverRing (n + 1) (CommRingCat.of k)).Modules}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (e₁ : S.X₁ ≅ projectiveTwist (n + 1) Q (d - 1))
    (e₂ : S.X₂ ≅ projectiveTwist (n + 1) Q d)
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward j).obj (projectiveTwist n G d)) :
    hilbertPolynomial k (n + 1) Q d - hilbertPolynomial k (n + 1) Q (d - 1)
      = @hilbertPolynomial k _ n G hG d := by
  have := hG
  have hcomp : IsProper (j ≫ (projectiveSpaceOverRing (n + 1) (CommRingCat.of k) ↘
      Spec (CommRingCat.of k))) := by
    rw [hj]
    infer_instance
  have : IsProper j :=
    IsProper.of_comp j (projectiveSpaceOverRing (n + 1) (CommRingCat.of k) ↘
      Spec (CommRingCat.of k))
  have hpm : IsProper (projectiveSpaceOverRing n (CommRingCat.of k) ↘
    Spec (CommRingCat.of k)) := inferInstance
  have h3 : (projectiveTwist n G d).IsCoherent := isCoherent_projectiveTwist n G d
  have : (projectiveTwist n G d).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have h4 : ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward j (projectiveTwist n G d)
  have heq : eulerCharacteristic k (projectiveSpaceOverRing (n + 1) (CommRingCat.of k) ↘
        Spec (CommRingCat.of k)) ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
      = @hilbertPolynomial k _ n G hG d := by
    rw [eulerCharacteristic_pushforward_of_isAffineHom k j
      (projectiveSpaceOverRing (n + 1) (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (projectiveTwist n G d) h3 h4]
    exact eulerCharacteristic_congr_structureMorphism k hj hcomp hpm
      (projectiveTwist n G d) h3
  exact (hilbertPolynomial_sub_eq_eulerCharacteristic_of_shortExact' k (n + 1) Q d hS e₁ e₂).trans
    ((eulerCharacteristic_eq_of_iso k _ e₃).trans heq)

end AlgebraicGeometry

end
