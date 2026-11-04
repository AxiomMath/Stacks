module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CoheratorLeraySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RelativeLeraySpectralSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Leray spectral sequence of the quasi-coherent direct image

Let `f : 𝒳 → 𝒴` and `g : 𝒴 → 𝒵` be quasi-compact and quasi-separated morphisms of algebraic
stacks and let `ℱ` be a quasi-coherent sheaf on `𝒳`.  **Stacks 0783** asserts the existence of a
spectral sequence

`E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)  ⟹  R^{p+q}(g ∘ f)_{QCoh,*} ℱ`,

where `R^i (-)_{QCoh,*}` is the higher direct image *in the quasi-coherent sense* of
[Stacks, Tag 077A]: the composite `Q ∘ R^i (-)_* ∘ i` of the ordinary higher direct image with
the coherator `Q` of [Stacks, Tag 0778], **not** the plain `R^i (-)_*`.

The source's proof is four steps, and all four are carried out here.

1. The relative Leray spectral sequence of [Stacks, Tag 0734] has `E_2^{p,q} = R^p g_*(R^q f_*ℱ)`
   and abuts to `R^{p+q}(g ∘ f)_*ℱ`.  That is
   `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`, proved in
   `StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/RelativeLeraySpectralSequence.lean`, and
   it is the machine instantiated below: the spectral sequence produced here is its image, and
   the abutment clause is its abutment clause transported.
2. The coherator `Q_𝒵` is exact, [Stacks, Tag 0779] part (3), so it may be applied to the whole
   spectral sequence.  That transport is
   `CategoryTheory.SpectralSequence.map` and `CategoryTheory.SpectralSequence.AbutsTo.map`, which
   is where the exactness is consumed; it is asked for as the three instance hypotheses
   `Additive`, `PreservesHomology` and `PreservesMonomorphisms` on `Q_𝒵`.
3. What remains is the identification of the second page, for which it suffices to know that
   `Q_𝒵(R^p g_*(R^q f_*ℱ)) = Q_𝒵(R^p g_*(Q_𝒴(R^q f_*ℱ)))`.  The source calls this step formal
   and does not spell it out.
4. It holds because the kernel and the cokernel of the adjunction map `Q_𝒴 𝓖 ⟶ 𝓖` are parasitic
   ([Stacks, Tag 0779] part (2)) while `R^p g_*` carries a parasitic module to a parasitic one
   ([Stacks, Tag 0775] part (2)) and `Q_𝒵` kills the parasitic modules
   ([Stacks, Tag 0779] part (1)).  Spelling it out is
   `Stacks.Cohomology.isIso_map_rightDerivedPlus_map_of_isZero_kernel_cokernel` below.

## Main definitions

* `Stacks.Cohomology.Leray.quasicoherentRelativeHigherDirectImage`: the quasi-coherent higher
  direct image `R^p g_{QCoh,*} = Q ∘ R^p g_* ∘ i` as a functor between the two quasi-coherent
  categories, the composite [Stacks, Tag 077A] prescribes, for a coherator supplied as data.

## Main results

* `Stacks.Cohomology.isIso_map_rightDerivedPlus_map_of_isZero_kernel_cokernel`: **a morphism
  whose kernel and cokernel become acyclic after an exact functor is applied is an isomorphism
  on that exact functor composed with every higher right derived functor.**  No tag; it is a
  plain lemma of homological algebra, the formal step of the source's proof.  It generalizes
  `Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel`, which is the case
  of an identity post-composition, and it is a genuine generalization rather than a corollary:
  the vanishing available here is of `Q(R ⁿ G(Ker u))`, not of `R ⁿ G(Ker u)`, so the long exact
  sequence has to be mapped through `Q` before the acyclicity can be used.
* `Stacks.Cohomology.Leray.exists_quasicoherentRelativeLeraySpectralSequence`: **Stacks 0783**,
  the spectral sequence with second page `R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)` abutting to
  `R^{p+q}(g ∘ f)_{QCoh,*} ℱ`.

## The page is `E₂`, not `E₁`

The second page of the source is delivered as a second page.  The engine of
[Stacks, Tag 0734] identifies its own `E_2`, and transport along `Q_𝒵` preserves the page
numbering, so no renumbering is performed anywhere below and no `E₁` reading is involved.  This
is unlike `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatCoveringSpectralSequence.lean`,
where [Stacks, Tag 0784] is formalized in its `E₁` form.

## What is instantiated, and what is carried

The statement is made for morphisms of **ringed topoi**, which is the generality in which the
relative Leray spectral sequence of [Stacks, Tag 0734] is available in this development, with
the two coherators and the parasitic modules supplied as data and hypotheses.  Concretely the
input is

* a coreflection `inclY ⊣ coheratorY` of `Mod(𝒪_D)` onto a category `𝒬_Y` playing
  `QCoh(𝒪_𝒴)` — this is the adjunction of [Stacks, Tag 0778], whose counit is the adjunction
  map `Q_𝒴 𝓖 ⟶ 𝓖` the source uses, so no new comparison morphism is introduced;
* an exact functor `coheratorZ` from `Mod(𝒪_E)` to a category `𝒬_Z` playing `QCoh(𝒪_𝒵)` —
  the coherator of [Stacks, Tag 0778] on `𝒵` together with its exactness,
  [Stacks, Tag 0779] part (3);
* a class `Parasitic` of objects of `Mod(𝒪_D)` — the parasitic modules of
  [Stacks, Tag 0773];
* `hker` and `hcoker`, that the kernel and the cokernel of `Q_𝒴 𝓖 ⟶ 𝓖` are parasitic — this
  is [Stacks, Tag 0779] part (2);
* `hvanish`, that `Q_𝒵 ∘ R^p g_*` kills a parasitic module.  This is the conjunction of the two
  statements the source cites at this point: [Stacks, Tag 0775] part (2), that `R^p g_*` carries
  a parasitic module to a parasitic one, and [Stacks, Tag 0779] part (1), that the kernel of the
  coherator is exactly the parasitic modules.  It is asked for only in the degrees `p ≥ 0`, which
  is the range in which [Stacks, Tag 0775] supplies it.

**Why the geometry is carried rather than instantiated.**  Every piece named above is present in
this development for an algebraic stack, and none of them can be plugged in, for the reasons the
module documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CoheratorLeraySpectralSequence.lean` sets
out for the absolute case, which apply here unchanged: [Stacks, Tag 0734] is formalized at
`RingedTopos.{u, u, u}` — a site whose objects *and* morphisms live in `Type u` — whereas the
ringed topos of an algebraic stack is `AlgebraicGeometry.Stack.FlatFppf.fppfRingedTopos`, of type
`RingedTopos.{u, u + 1, u}`; and the coherator
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` ([Stacks, Tag 0778]), the higher direct
images `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` and the parasitic vanishing of
[Stacks, Tag 0775] are formalized over three mutually incomparable categories of modules.

**[Stacks, Tag 0775] part (2) is absent from the library**, which is why it is a hypothesis and
not a citation.  The file
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticCohomologyVanishing.lean`
proves part (1) only, and records that part (2) needs the description of `R^i f_*` as the
sheafification of `y ↦ H^i_τ(V ×_{y,𝒴} 𝒳, pr^{-1}ℱ)`, which this development does not have in
any form; the fibre-product reading of [Stacks, Tag 075G] that would supply it is not the
derived-presheaf form formalized at
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/HigherDirectImage.lean`.

**[Stacks, Tag 077A] is not proved here**, and is absent from the library.  That proposition
constructs `f_{QCoh,*}` as a right adjoint of quasi-coherent pullback for a quasi-compact
quasi-separated morphism and shows the `R^i f_{QCoh,*}` form a `δ`-functor; the
quasi-compactness and quasi-separatedness of `f` and `g` enter 0783 only through it.  What is
used here is only its *definition* of `R^i (-)_{QCoh,*}` as `Q ∘ R^i (-)_* ∘ i`, reproduced as
`Stacks.Cohomology.Leray.quasicoherentHigherDirectImage` for the inner factor and as
`Stacks.Cohomology.Leray.quasicoherentRelativeHigherDirectImage` for the outer one.

[Stacks, Tag 0771], which the source cites to know that every term of the spectral sequence lies
in `LQCoh^fbc(𝒪_𝒵)`, is not needed in this reading and is not assumed: the coherators here are
defined on the whole of `Mod(𝒪_D)` and `Mod(𝒪_E)`, which is what stands in for the fact, proved
there, that the terms lie in the domain of the coherator.

## Reading the statements

As in `RelativeLeraySpectralSequence.lean`, the composite `g ∘ f` is presented by a third
morphism `gf` together with a comparison `τ` of the geometric direct images, because a morphism
of ringed topoi has an abstract direct image and the direct image of a composite is only
canonically isomorphic to the composite of the direct images.  The statement is made for an
object of `D⁺(Mod(𝒪_C))`; the source's single quasi-coherent sheaf is such an object placed in
degree zero.  The second page is identified in every bidegree `(p, q) : ℤ × ℤ`, and the abutment
is over all `n : ℤ`, both exactly as [Stacks, Tag 0734] supplies them.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0782](https://stacks.math.columbia.edu/tag/0782)
* [Stacks Project, Tag 0783](https://stacks.math.columbia.edu/tag/0783)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Acyclicity after an exact functor -/

section AcyclicComparison

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (G : A ⥤ B) [G.Additive] (Q : B ⥤ C) [Q.Additive] [Q.PreservesHomology]
  [Q.PreservesMonomorphisms]

omit [Q.PreservesMonomorphisms] in
/-- In a short exact sequence whose first term has `Q(R ⁿ G(-))` vanishing in the degrees `n` and
`n + 1`, the second map induces an isomorphism on `Q ∘ R ⁿ G`. -/
private theorem isIso_map_rightDerivedPlus_map_g {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h₀ : IsZero (Q.obj ((G.rightDerivedPlus (n : ℤ)).obj S.X₁)))
    (h₁ : IsZero (Q.obj ((G.rightDerivedPlus ((n : ℤ) + 1)).obj S.X₁))) :
    IsIso (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.g)) := by
  obtain ⟨-, hex, hexl, -⟩ := rightDerivedPlusExactness G
  have : Mono (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.g)) :=
    ((hex hS n).choose_spec.map Q).mono_g (h₀.eq_of_src _ _)
  have : Epi (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.g)) :=
    ((hexl hS n).choose_spec.map Q).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a short exact sequence whose third term has `Q(R ⁿ G(-))` vanishing in every degree, the
first map induces an isomorphism on `Q ∘ R ⁿ G`. -/
private theorem isIso_map_rightDerivedPlus_map_f {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : ∀ m : ℕ, IsZero (Q.obj ((G.rightDerivedPlus (m : ℤ)).obj S.X₃))) :
    IsIso (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.f)) := by
  obtain ⟨hmono, hex, -, hexr⟩ := rightDerivedPlusExactness G
  have hepi : Epi (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.f)) :=
    ((hex hS n).choose_spec.map Q).epi_f ((h n).eq_of_tgt _ _)
  have hm : Mono (Q.map ((G.rightDerivedPlus (n : ℤ)).map S.f)) := by
    match n with
    | 0 =>
      have := hmono hS
      exact Q.map_mono _
    | (m + 1) =>
      rw [Nat.cast_add_one]
      exact ((hexr hS m).choose_spec.map Q).mono_g ((h m).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- The nonnegative degrees of
`Stacks.Cohomology.isIso_map_rightDerivedPlus_map_of_isZero_kernel_cokernel`. -/
private theorem isIso_map_rightDerivedPlus_map_of_isZero_nat {M N : A} (u : M ⟶ N)
    (hker : ∀ n : ℕ, IsZero (Q.obj ((G.rightDerivedPlus (n : ℤ)).obj (kernel u))))
    (hcoker : ∀ n : ℕ, IsZero (Q.obj ((G.rightDerivedPlus (n : ℤ)).obj (cokernel u)))) (n : ℕ) :
    IsIso (Q.map ((G.rightDerivedPlus (n : ℤ)).map u)) := by
  have hS₁ : (ShortComplex.mk (kernel.ι u) (cokernel.π (kernel.ι u)) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel (kernel.ι u) }
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π u)) (cokernel.π u) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_kernel (cokernel.π u) }
  have h₁ : IsIso (Q.map ((G.rightDerivedPlus (n : ℤ)).map (Abelian.coimage.π u))) :=
    isIso_map_rightDerivedPlus_map_g G Q hS₁ n (hker n) (by exact_mod_cast hker (n + 1))
  have h₂ : IsIso (Q.map ((G.rightDerivedPlus (n : ℤ)).map (Abelian.image.ι u))) :=
    isIso_map_rightDerivedPlus_map_f G Q hS₂ n hcoker
  rw [← Abelian.coimage_image_factorisation u, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A morphism whose kernel and cokernel are acyclic after an exact functor is applied is an
isomorphism on that functor composed with every higher right derived functor.**  Let
`G : 𝒜 ⥤ ℬ` be an additive functor between abelian categories with `𝒜` having enough injectives,
let `Q : ℬ ⥤ 𝒞` be exact, and let `u : M ⟶ N` be a morphism of `𝒜` with `Q(R ⁿ G(Ker u)) = 0` and
`Q(R ⁿ G(Coker u)) = 0` for every `n ≥ 0`.  Then `Q(R ⁿ G(u))` is an isomorphism for every
`n : ℤ`.

This is the step [Stacks, Tag 0783] performs when it concludes that
`Q_𝒵(R^p g_*(R^q f_*ℱ)) = Q_𝒵(R^p g_*(Q_𝒴(R^q f_*ℱ)))`.

The case `Q = 𝟭` is `Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel`. -/
theorem isIso_map_rightDerivedPlus_map_of_isZero_kernel_cokernel {M N : A} (u : M ⟶ N)
    (hker : ∀ n : ℕ, IsZero (Q.obj ((G.rightDerivedPlus (n : ℤ)).obj (kernel u))))
    (hcoker : ∀ n : ℕ, IsZero (Q.obj ((G.rightDerivedPlus (n : ℤ)).obj (cokernel u))))
    (n : ℤ) : IsIso (Q.map ((G.rightDerivedPlus n).map u)) := by
  rcases lt_or_ge n 0 with hn | hn
  · have hM := Functor.map_isZero Q (G.isZero_rightDerivedPlus_of_neg M n hn)
    have hN := Functor.map_isZero Q (G.isZero_rightDerivedPlus_of_neg N n hn)
    rw [hM.eq_of_src (Q.map ((G.rightDerivedPlus n).map u)) (hM.iso hN).hom]
    infer_instance
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact isIso_map_rightDerivedPlus_map_of_isZero_nat G Q u hker hcoker m

end AcyclicComparison

namespace Leray

/-! ### The quasi-coherent relative higher direct images, and Stacks 0783 -/

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)

/-- **The quasi-coherent higher direct image `R ^p g_{QCoh,*}` as a functor between the two
quasi-coherent categories**, the composite [Stacks, Tag 077A] prescribes: include a
quasi-coherent module into all modules by `incl`, take the ordinary higher direct image
`R ^p g_*`, and apply the coherator `coherator` of [Stacks, Tag 0778].  Both the inclusion and
the coherator are supplied as data, so this names the recipe rather than proving anything about
it; in particular it does **not** prove [Stacks, Tag 077A], which asserts that this is a right
adjoint of quasi-coherent pullback and that these functors form a `δ`-functor.

This is the companion of `Stacks.Cohomology.Leray.quasicoherentHigherDirectImage`, which is the
same recipe read on `D⁺(Mod(𝒪_C))` rather than on a quasi-coherent category. -/
def quasicoherentRelativeHigherDirectImage {𝒬Y : Type u₁} [Category.{v₁} 𝒬Y]
    {𝒬Z : Type u₂} [Category.{v₂} 𝒬Z]
    (incl : 𝒬Y ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (coherator : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⥤ 𝒬Z) (p : ℤ) :
    𝒬Y ⥤ 𝒬Z :=
  incl ⋙ (pushforwardModules g).rightDerivedPlus p ⋙ coherator

variable (gf : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ gf.toToposHom.pushforward)
  (hτ : fSharpSetComp f g ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
    fSharpSet gf)

include τ hτ in
/-- **Stacks 0783, the relative Leray spectral sequence for the quasi-coherent direct image.**
Let `f : (Sh(C), 𝒪_C) → (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) → (Sh(E), 𝒪_E)` be morphisms of
ringed topoi standing for quasi-compact quasi-separated morphisms `f : 𝒳 → 𝒴` and `g : 𝒴 → 𝒵` of
algebraic stacks, with `g ∘ f` presented as their composite by a comparison `τ` of the geometric
direct images, and let `K` be a bounded below complex of `𝒪_C`-modules, standing for the
quasi-coherent sheaf `ℱ` placed in degree zero.  Suppose given

* a coreflection `inclY ⊣ coheratorY` of `Mod(𝒪_D)` onto a category `𝒬_Y`: this is the coherator
  of **Stacks 0778**, `Q_𝒴 : LQCoh^fbc(𝒪_𝒴) ⥤ QCoh(𝒪_𝒴)`, with its adjunction, whose counit
  `Q_𝒴 𝓖 ⟶ 𝓖` is the adjunction map the source's proof uses;
* an exact functor `coheratorZ` from `Mod(𝒪_E)` to a category `𝒬_Z`: the coherator of
  **Stacks 0778** on `𝒵`, exact by **Stacks 0779** part (3), which is the functor the source
  applies to the whole spectral sequence;
* a class `Parasitic` of modules on `D`: the parasitic modules of **Stacks 0773**;
* `hker` and `hcoker`: the kernel and the cokernel of the counit are parasitic, which is
  **Stacks 0779** part (2);
* `hvanish`: `Q_𝒵 ∘ R^p g_*` kills a parasitic module, which is **Stacks 0775** part (2)
  followed by **Stacks 0779** part (1).

Then there is a spectral sequence with

`E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)`

converging to `R^{p+q}(g ∘ f)_{QCoh,*} ℱ`, where the two quasi-coherent higher direct images are
`Stacks.Cohomology.Leray.quasicoherentRelativeHigherDirectImage` and
`Stacks.Cohomology.Leray.quasicoherentHigherDirectImage`, the composites of **Stacks 077A**, and
the abutment is `Q_𝒵` applied to `R^{p+q}(g ∘ f)_*ℱ`, which is the same composite in degree
`p + q`.

See the module documentation for why the coherators and the cited lemmas are carried as
hypotheses rather than instantiated. -/
@[stacks 0783 "the E₂ page R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ) and convergence, FOR RINGED TOPOI, \
not algebraic stacks, hence NOT a generalization: 0734 is proved at RingedTopos.{u,u,u}, a \
stack's is {u,u+1,u}. Carried: the 0778 coherators, 0779(3)(2)(1) and 0775(2), the last absent \
here; 077A is absent too, only its recipe Q ∘ R^i(-)_* ∘ i is reused. See the module docstring",
  ega "0 12.2.4" "more general",
  sga "2 VIII 3.1" "more general",
  sga "4 V 5.3" "more general",
  sga "4 V 5.4" "more general",
  sga "4½ Arcata 2.3.3" "more general"]
theorem exists_quasicoherentRelativeLeraySpectralSequence {𝒬Y : Type u₁} [Category.{v₁} 𝒬Y]
    {𝒬Z : Type u₂} [Category.{v₂} 𝒬Z] [Abelian 𝒬Z]
    (inclY : 𝒬Y ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (coheratorY : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ 𝒬Y)
    (adjY : inclY ⊣ coheratorY)
    (coheratorZ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⥤ 𝒬Z)
    [coheratorZ.Additive] [coheratorZ.PreservesHomology] [coheratorZ.PreservesMonomorphisms]
    (Parasitic : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hvanish : ∀ P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic P → ∀ p : ℕ,
        IsZero (coheratorZ.obj (((pushforwardModules g).rightDerivedPlus (p : ℤ)).obj P)))
    (hker : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic (kernel (adjY.counit.app M)))
    (hcoker : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      Parasitic (cokernel (adjY.counit.app M)))
    (K : DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence 𝒬Z 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        (quasicoherentRelativeHigherDirectImage g inclY coheratorZ p).obj
          ((quasicoherentHigherDirectImage f coheratorY q).obj K))) ∧
      SpectralSequence.AbutsTo E (fun n => coheratorZ.obj
        ((DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) n).obj
            ((pushforwardModules gf).rightDerivedFunctorPlus.obj K))) := by
  obtain ⟨E, hE₂, habuts⟩ := exists_relativeLeraySpectralSequence f g gf τ hτ K
  refine ⟨E.map coheratorZ, fun p q => ?_, habuts.map coheratorZ⟩
  have hiso : IsIso (coheratorZ.map (((pushforwardModules g).rightDerivedPlus p).map
      (adjY.counit.app ((DerivedCategory.Plus.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj
          ((pushforwardModules f).rightDerivedFunctorPlus.obj K))))) :=
    isIso_map_rightDerivedPlus_map_of_isZero_kernel_cokernel (pushforwardModules g) coheratorZ _
      (fun n => hvanish _ (hker _) n) (fun n => hvanish _ (hcoker _) n) p
  exact ⟨coheratorZ.mapIso (hE₂ p q).some ≪≫ (@asIso _ _ _ _ _ hiso).symm⟩

end

end Leray

end Stacks.Cohomology

end
