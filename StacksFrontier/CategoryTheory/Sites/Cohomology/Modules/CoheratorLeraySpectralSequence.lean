module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.LeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSectionsOverGamma
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray spectral sequence of the quasi-coherent direct image

Let `f : 𝒳 → 𝒴` be a quasi-compact and quasi-separated morphism of algebraic stacks and `ℱ` a
quasi-coherent module on `𝒳`.  **Stacks 0782** asserts the existence of a spectral sequence

`E_2^{p,q} = H^p(𝒴, R^q f_{QCoh,*} ℱ)  ⟹  H^{p+q}(𝒳, ℱ)`,

where `R^q f_{QCoh,*}` is the higher direct image *in the quasi-coherent sense* of
[Stacks, Tag 077A]: the composite `Q ∘ R^q f_* ∘ i` of the ordinary higher direct image with
the coherator `Q` of [Stacks, Tag 0778], **not** the plain `R^q f_*`.

The source's proof is two steps, and both are carried out here.

1. The Leray spectral sequence of [Stacks, Tag 0732] has `E_2^{p,q} = H^p(𝒴, R^q f_* ℱ)` and
   abuts to `H^{p+q}(𝒳, ℱ)`.  That is
   `Stacks.Cohomology.Leray.exists_leraySpectralSequence`, proved in
   `StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/LeraySpectralSequence.lean`, and it is
   the machine instantiated below: the spectral sequence produced here *is* the one it
   produces, and the abutment clause is its abutment clause unchanged.
2. The adjunction map `Q 𝓖 ⟶ 𝓖` has parasitic kernel and cokernel ([Stacks, Tag 0779] part
   (2)), and a parasitic module has vanishing cohomology ([Stacks, Tag 0775] part (1)); so the
   two second pages agree, `H^p(𝒴, Q(R^q f_* ℱ)) = H^p(𝒴, R^q f_* ℱ)`.  The source calls this
   step formal and does not spell it out.  It is spelled out here, as
   `Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel`: a morphism whose
   kernel and cokernel are acyclic for a right derived functor is an isomorphism on that
   derived functor in every degree, by the long exact sequence of [Stacks, Tag 05TE] applied
   to the two short exact sequences of the coimage-image factorisation.

## Main definitions

* `Stacks.Cohomology.Leray.quasicoherentHigherDirectImage`: the quasi-coherent higher direct
  image `R^q f_{QCoh,*} = Q ∘ H^q ∘ Rf_*`, the composite [Stacks, Tag 077A] prescribes, for a
  coherator `Q` supplied as data.

## Main results

* `Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel`: **a morphism with
  acyclic kernel and cokernel is an isomorphism on every higher right derived functor.**  No
  tag; it is a plain lemma of homological algebra, the formal step of the source's proof.
* `Stacks.Cohomology.Leray.exists_quasicoherentLeraySpectralSequence`: the argument of
  **Stacks 0782** for a morphism of ringed topoi and an abstract coreflection: the spectral
  sequence with second page `H^p(𝒴, Q(R^q f_* K))` abutting to `H^{p+q}(𝒳, K)`.  Stacks 0782
  itself, for algebraic stacks, is
  `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentLeraySpectralSequence` in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentLeraySpectralSequence.lean`.

## What is instantiated, and what is carried

The statement is made for a morphism of **ringed topoi**, which is the generality in which the
Leray spectral sequence of [Stacks, Tag 0732] is available in this development, with the
coherator and the parasitic modules supplied as data and hypotheses.  Concretely the input is

* a coreflection `incl ⊣ coherator` of `Mod(𝒪_𝒴)` onto a category `𝒬` playing `QCoh(𝒪_𝒴)` —
  this is the adjunction of [Stacks, Tag 0778], whose counit is the adjunction map
  `Q 𝓖 ⟶ 𝓖` the source uses, so no new comparison morphism is introduced;
* a class `Parasitic` of objects of `Mod(𝒪_𝒴)` — the parasitic modules of
  [Stacks, Tag 0773];
* `hker` and `hcoker`, that the kernel and the cokernel of `Q 𝓖 ⟶ 𝓖` are parasitic — this is
  [Stacks, Tag 0779] part (2);
* `hvanish`, that a parasitic module has vanishing cohomology — this is [Stacks, Tag 0775]
  part (1).

**Relation to algebraic stacks.**  This version lives at `RingedTopos.{u, u, u}` — a site whose
objects and morphisms live in `Type u` — whereas the ringed topos of an algebraic stack,
`AlgebraicGeometry.Stack.FlatFppf.fppfRingedTopos`, is a `RingedTopos.{u, u + 1, u}`, so the
theorem here does not specialise to a morphism of algebraic stacks.  The statement of
[Stacks, Tag 0782] for algebraic stacks is proved separately, with the coherator of
[Stacks, Tag 0778], the higher direct images of [Stacks, Tag 077A] and the inputs
[Stacks, Tag 0779] part (2) and [Stacks, Tag 0775] part (1) all instantiated, as
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentLeraySpectralSequence` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentLeraySpectralSequence.lean`.

The definition `Stacks.Cohomology.Leray.quasicoherentHigherDirectImage` below is the composite
`Q ∘ R^q f_*` for a coherator `Q` supplied as data; the algebraic-stack higher direct images of
[Stacks, Tag 077A] are `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`.

## Reading the statements

As in `LeraySpectralSequence.lean`, cohomology is read in abelian groups: `H^p(𝒴, -)` is
`(Stacks.Cohomology.Leray.globalSectionsAb Y).rightDerivedPlus p` and the abutment is the
hypercohomology `H^n(𝒳, ℱ)` of a bounded below complex.  The statement is made for an object
of `D⁺(Mod(𝒪_𝒳))`; the source's single quasi-coherent module is such an object placed in
degree zero.

The second page is identified in every bidegree `(p, q) : ℤ × ℤ`, as in [Stacks, Tag 0732]
itself: the source states it in the first quadrant, and outside the degrees `p ≥ 0` the two
readings of the second page agree because both vanish, by
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`.  The vanishing hypothesis `hvanish`
is nevertheless asked for only in the degrees `p ≥ 0`, which is the range in which
[Stacks, Tag 0775] supplies it.  The abutment is over all `n : ℤ` and is the one
[Stacks, Tag 0732] supplies, untouched.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0782](https://stacks.math.columbia.edu/tag/0782)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology

universe v₁ v₂ u₁ u₂

/-! ### A morphism with acyclic kernel and cokernel -/

section AcyclicComparison

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (G : A ⥤ B) [G.Additive]

/-- The long exact sequence of the higher right derived functors of `G`, in the `ℤ`-indexed
convention `R ⁱ G = H ⁱ ∘ RG ∘ (·[0])`: this is [Stacks, Tag 05TE] part (1) at the canonical
`δ`-functor structure, and the tuple is used below three terms at a time. -/
public theorem rightDerivedPlusExactness :
    (∀ {S : ShortComplex A}, S.ShortExact → Mono ((G.rightDerivedPlus 0).map S.f)) ∧
      (∀ {S : ShortComplex A} (_ : S.ShortExact) (i : ℕ),
        ∃ hz : (G.rightDerivedPlus i).map S.f ≫ (G.rightDerivedPlus i).map S.g = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex A} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : (G.rightDerivedPlus i).map S.g ≫ DerivedIndexing.canonicalδ G hS i = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex A} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : DerivedIndexing.canonicalδ G hS i ≫ (G.rightDerivedPlus (i + 1)).map S.f = 0,
          (ShortComplex.mk _ _ hz).Exact) := by
  obtain ⟨-, hmono, hex, hexl, hexr, -⟩ :=
    (Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal G
      (DerivedIndexing.derivedDeltaFunctorStructure G) (DerivedIndexing.canonicalδ G)
      (fun _ _ => rfl)).1
  exact ⟨hmono, hex, hexl, hexr⟩

/-- In a short exact sequence whose first term is `G`-acyclic in the degrees `n` and `n + 1`,
the second map induces an isomorphism on `R ⁿ G`.  Injectivity comes from exactness of
`R ⁿ G(X₁) → R ⁿ G(X₂) → R ⁿ G(X₃)` and surjectivity from exactness of
`R ⁿ G(X₂) → R ⁿ G(X₃) → R ⁿ⁺¹ G(X₁)`. -/
private theorem isIso_rightDerivedPlus_map_g {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h₀ : IsZero ((G.rightDerivedPlus (n : ℤ)).obj S.X₁))
    (h₁ : IsZero ((G.rightDerivedPlus ((n : ℤ) + 1)).obj S.X₁)) :
    IsIso ((G.rightDerivedPlus (n : ℤ)).map S.g) := by
  obtain ⟨-, hex, hexl, -⟩ := rightDerivedPlusExactness G
  have : Mono ((G.rightDerivedPlus (n : ℤ)).map S.g) :=
    (hex hS n).choose_spec.mono_g (h₀.eq_of_src _ _)
  have : Epi ((G.rightDerivedPlus (n : ℤ)).map S.g) :=
    (hexl hS n).choose_spec.epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a short exact sequence whose third term is `G`-acyclic in every degree, the first map
induces an isomorphism on `R ⁿ G`.  Surjectivity comes from exactness of
`R ⁿ G(X₁) → R ⁿ G(X₂) → R ⁿ G(X₃)`; injectivity in degree zero is the monomorphism clause of
the `δ`-functor and in degree `m + 1` is exactness of
`R ᵐ G(X₃) → R ᵐ⁺¹ G(X₁) → R ᵐ⁺¹ G(X₂)`. -/
private theorem isIso_rightDerivedPlus_map_f {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : ∀ m : ℕ, IsZero ((G.rightDerivedPlus (m : ℤ)).obj S.X₃)) :
    IsIso ((G.rightDerivedPlus (n : ℤ)).map S.f) := by
  obtain ⟨hmono, hex, -, hexr⟩ := rightDerivedPlusExactness G
  have hepi : Epi ((G.rightDerivedPlus (n : ℤ)).map S.f) :=
    (hex hS n).choose_spec.epi_f ((h n).eq_of_tgt _ _)
  have hm : Mono ((G.rightDerivedPlus (n : ℤ)).map S.f) := by
    match n with
    | 0 => exact hmono hS
    | (m + 1) =>
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      exact (hexr hS m).choose_spec.mono_g ((h m).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- The nonnegative degrees of
`Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel`, which is where the
long exact sequence lives. -/
private theorem isIso_rightDerivedPlus_map_of_isZero_nat {M N : A} (u : M ⟶ N)
    (hker : ∀ n : ℕ, IsZero ((G.rightDerivedPlus (n : ℤ)).obj (kernel u)))
    (hcoker : ∀ n : ℕ, IsZero ((G.rightDerivedPlus (n : ℤ)).obj (cokernel u))) (n : ℕ) :
    IsIso ((G.rightDerivedPlus (n : ℤ)).map u) := by
  have hS₁ : (ShortComplex.mk (kernel.ι u) (cokernel.π (kernel.ι u)) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel (kernel.ι u) }
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π u)) (cokernel.π u) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_kernel (cokernel.π u) }
  have hker' : IsZero ((G.rightDerivedPlus ((n : ℤ) + 1)).obj (kernel u)) := by
    have := hker (n + 1)
    rwa [Nat.cast_add, Nat.cast_one] at this
  have h₁ : IsIso ((G.rightDerivedPlus (n : ℤ)).map (Abelian.coimage.π u)) :=
    isIso_rightDerivedPlus_map_g G hS₁ n (hker n) hker'
  have h₂ : IsIso ((G.rightDerivedPlus (n : ℤ)).map (Abelian.image.ι u)) :=
    isIso_rightDerivedPlus_map_f G hS₂ n hcoker
  have h₃ : IsIso ((G.rightDerivedPlus (n : ℤ)).map (Abelian.coimageImageComparison u)) :=
    inferInstance
  rw [← Abelian.coimage_image_factorisation u, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A morphism whose kernel and cokernel are acyclic is an isomorphism on every higher right
derived functor.**  Let `G : 𝒜 ⥤ ℬ` be an additive functor between abelian categories with `𝒜`
having enough injectives, and let `u : M ⟶ N` be a morphism of `𝒜` with `R ⁿ G(Ker u) = 0` and
`R ⁿ G(Coker u) = 0` for every `n ≥ 0`.  Then `R ⁿ G(u)` is an isomorphism for every `n : ℤ`.

In the nonnegative degrees the proof is the coimage-image factorisation `u = π ≫ c ≫ ι` of
`CategoryTheory.Abelian.coimage_image_factorisation`: `π` is the third map of the short exact
sequence `0 → Ker u → M → Coim u → 0` and `ι` the first map of `0 → Im u → N → Coker u → 0`,
each therefore an isomorphism on `R ⁿ G` by the two one-sided statements above, while the
coimage-image comparison `c` is already an isomorphism because the category is abelian.  In the
negative degrees both sides vanish, by
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`, so no hypothesis is needed there.

This is the step [Stacks, Tag 0782] performs when it concludes that the two second pages agree
"formally"; the long exact sequence it uses is the one of [Stacks, Tag 05TE]. -/
theorem isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel {M N : A} (u : M ⟶ N)
    (hker : ∀ n : ℕ, IsZero ((G.rightDerivedPlus (n : ℤ)).obj (kernel u)))
    (hcoker : ∀ n : ℕ, IsZero ((G.rightDerivedPlus (n : ℤ)).obj (cokernel u))) (n : ℤ) :
    IsIso ((G.rightDerivedPlus n).map u) := by
  rcases lt_or_ge n 0 with hn | hn
  · have hM := G.isZero_rightDerivedPlus_of_neg M n hn
    have hN := G.isZero_rightDerivedPlus_of_neg N n hn
    rw [hM.eq_of_src ((G.rightDerivedPlus n).map u) (hM.iso hN).hom]
    infer_instance
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact isIso_rightDerivedPlus_map_of_isZero_nat G u hker hcoker m

end AcyclicComparison

namespace Leray

/-! ### The quasi-coherent higher direct images, and Stacks 0782 -/

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [PreservesFiniteLimits
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} AddCommGrpCat.{u}]
  [HasDerivedCategory.{u}
    (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))]
  [((globalSectionsFunctor.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The quasi-coherent higher direct image `R ^q f_{QCoh,*}`**, the composite
[Stacks, Tag 077A] prescribes: take the ordinary higher direct image `H ^q ∘ Rf_*` and apply
the coherator `coherator` of [Stacks, Tag 0778].  The coherator is supplied as data, so this
names the recipe rather than proving anything about it.  The higher direct images of
[Stacks, Tag 077A] for a 1-morphism of algebraic stacks, with their properties, are
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage` and the declarations
of `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentPushforward.lean`. -/
def quasicoherentHigherDirectImage {𝒬 : Type u₁} [Category.{v₁} 𝒬]
    (coherator : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ 𝒬) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤ 𝒬 :=
  (pushforwardModules f).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        Y.O)) q ⋙
      coherator

/-- **The Leray spectral sequence for a coherator-type direct image, for a morphism of ringed
topoi**, read in abelian groups: the argument of **Stacks 0782** over an abstract coreflection.
The statement of Stacks 0782 for a quasi-compact quasi-separated 1-morphism of algebraic
stacks is `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentLeraySpectralSequence`,
which does not use this theorem.

Let `f : (Sh(C), 𝒪_C) → (Sh(D), 𝒪_D)` be a morphism of ringed topoi, in the role of a
quasi-compact quasi-separated morphism `f : 𝒳 → 𝒴` of algebraic stacks, and let `K` be a
bounded below complex of `𝒪_C`-modules, standing for the quasi-coherent module `ℱ` placed in
degree zero.  Suppose given

* a coreflection `incl ⊣ coherator` of `Mod(𝒪_D)` onto a category `𝒬`: this is the coherator
  of **Stacks 0778**, `Q : LQCoh^fbc(𝒪_𝒴) ⥤ QCoh(𝒪_𝒴)`, with its adjunction, whose counit
  `Q 𝓖 ⟶ 𝓖` is the adjunction map the source's proof uses;
* a class `Parasitic` of modules on `D`: the parasitic modules of **Stacks 0773**;
* `hker` and `hcoker`: the kernel and the cokernel of the counit are parasitic, which is
  **Stacks 0779** part (2);
* `hvanish`: a parasitic module has vanishing cohomology, which is **Stacks 0775** part (1).

Then there is a spectral sequence with

`E_2^{p,q} = H^p(𝒴, R^q f_{QCoh,*} ℱ)`

converging to `H^{p+q}(𝒳, ℱ)`, where `R^q f_{QCoh,*}` is
`Stacks.Cohomology.Leray.quasicoherentHigherDirectImage`, the composite of **Stacks 077A**.

The spectral sequence is the one of **Stacks 0732**,
`Stacks.Cohomology.Leray.exists_leraySpectralSequence`, and its abutment clause is that
theorem's abutment clause unchanged.  What is added is the identification of its second page:
`Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel` turns the counit
`Q(R^q f_* ℱ) ⟶ R^q f_* ℱ`, whose kernel and cokernel are acyclic by `hker`, `hcoker` and
`hvanish`, into an isomorphism `H^p(𝒴, Q(R^q f_* ℱ)) ≅ H^p(𝒴, R^q f_* ℱ)` in every degree.
That is precisely the step the source performs and calls formal.

This theorem lives at `RingedTopos.{u, u, u}`, while the ringed topos of an algebraic stack has
its site one universe up, so it does not specialise to algebraic stacks; the algebraic-stack
statement is proved directly in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentLeraySpectralSequence.lean`. -/
@[sga "4 V 5.3" "more general", sga "4 V 5.4" "special case"]
theorem exists_quasicoherentLeraySpectralSequence {𝒬 : Type u₁} [Category.{v₁} 𝒬]
    (incl : 𝒬 ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (coherator : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ 𝒬)
    (adj : incl ⊣ coherator)
    (Parasitic : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hvanish : ∀ P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic P → ∀ p : ℕ,
      IsZero (((globalSectionsAb Y).rightDerivedPlus (p : ℤ)).obj P))
    (hker : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic (kernel (adj.counit.app M)))
    (hcoker : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic (cokernel (adj.counit.app M)))
    (K : DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((globalSectionsAb Y).rightDerivedPlus p).obj
          (incl.obj ((quasicoherentHigherDirectImage f coherator q).obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
          ((globalSectionsAb X).rightDerivedFunctorPlus.obj K)) := by
  obtain ⟨E, hE₂, habuts⟩ := exists_leraySpectralSequence f K
  refine ⟨E, fun p q => ?_, habuts⟩
  have hiso := fun M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) =>
    isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel (globalSectionsAb Y) (adj.counit.app M)
      (fun n => hvanish _ (hker _) n) (fun n => hvanish _ (hcoker _) n) p
  exact ⟨(hE₂ p q).some ≪≫ (@asIso _ _ _ _ _ (hiso _)).symm⟩

end

end Leray

end Stacks.Cohomology

end
