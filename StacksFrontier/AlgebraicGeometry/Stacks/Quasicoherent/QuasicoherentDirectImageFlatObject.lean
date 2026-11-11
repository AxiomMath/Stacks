module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ColimitsOfQuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction

/-!
# Direct images and quasi-coherent direct images agree at a flat object (Stacks 0GQQ)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks over a
scheme `S`, let `y` be an object of `𝒴` which is flat (**Stacks 0H14**), and let `ℱ` be an object
of `QCoh(𝒪_𝒳)`.  **Stacks 0GQQ** says

`(f_*ℱ)(y) = (f_{QCoh,*}ℱ)(y)` and `(R^i f_*ℱ)(y) = (R^i f_{QCoh,*}ℱ)(y)` for all `i ∈ ℤ`.

The equality is realized by the counit `ε : i Q(𝓖) ⟶ 𝓖` of the adjunction of **Stacks 0778** at
`𝓖 = R^i f_*(i ℱ)`: by the construction of **Stacks 077A** the domain of `ε` is
`i (R^i f_{QCoh,*} ℱ)` and its codomain is `R^i f_*(i ℱ)`, so the component of `ε` at `y` *is*
the canonical comparison of the two modules of sections the source equates.  What is asserted
below is that this canonical map is invertible, never the bare existence of an isomorphism.

## Main results

* `AlgebraicGeometry.Stack.isIso_app_of_isParasitic`: a map of presheaves of `𝒪_𝒳`-modules whose
  kernel and cokernel are parasitic (**Stacks 0773**) is invertible on sections over a flat
  object.  This is the whole of the step the source leaves implicit, and it is unconditional.
* `AlgebraicGeometry.Stack.isIso_app_quasicoherentDirectImageOfEtale_counit`: **Stacks 0GQQ**,
  covering `f_*` and every `R^i f_*` at once.

## Carried versus proved

What is **proved** is `AlgebraicGeometry.Stack.isIso_app_of_isParasitic` and the instantiation of
it at the counit: a parasitic presheaf of modules has vanishing module of sections at every flat
object, and evaluation at an object of the site preserves finite limits and finite colimits of
presheaves of modules, hence carries kernel to kernel and cokernel to cokernel; so the comparison
is injective and surjective at `y`, and a bijective map of modules is invertible.  Note that this
argument has to be run on *presheaves* of modules: on sheaves the cokernel is a sheafification,
and vanishing of the sheaf cokernel's sections at `y` would not be enough.

Three things are **carried**, each a named result of the source which this library does not have.

* The *middle* direct image on `LQCoh^fbc` is carried as data `D`, exactly as in
  `AlgebraicGeometry.Stack.quasicoherentDirectImageOfEtale`, which is the composite of
  **Stacks 077A** this file's conclusion is about.  It is `f_*` when `D` is the étale direct image
  and `R^i f_*` when `D` is its `i`-th right derived functor, so one statement covers both halves
  of the source.  The reason it is data is recorded at that definition: **Stacks 077A** is proved
  on the fppf sites at module universe `u`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageDeltaFunctor`), but on
  the étale-site category this file is stated over the composite cannot be assembled from what
  is available, because
  `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` produces modules with sections in
  `u + 1` while `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules` pins them
  to `u`.
* `hker` and `hcoker` are **Stacks 0779** part (2) — parasiticity of the kernel and of the
  cokernel of the counit — read in the abelian category of presheaves of modules.  Part (2) *is*
  proved, as
  `AlgebraicGeometry.Stack.isParasitic_of_isLimit_kernelFork_flatBaseChangeQuasicoherator` and
  its cokernel companion, but it does not discharge these two hypotheses, and the two halves fail
  for different reasons.  For the kernel, the library's form concludes about the point of an
  arbitrary kernel fork taken *inside* `LQCoh^fbc(𝒪_𝒴)`; identifying that point with the kernel
  of the counit computed in the ambient category is **Stacks 0771** part (2), the weak Serre
  subcategory property, which the library does not have — the same gap
  `AlgebraicGeometry.Stack.isLimitKernelForkFlatBaseChangeQuasicoherator` records for
  **Stacks 0GQL** part (3).  For the cokernel the gap is wider: the cokernel inside
  `LQCoh^fbc(𝒪_𝒴)`, like the one in `Mod(𝒪_𝒴)`, is a sheafification of the presheaf cokernel, so
  the library's conclusion is about a quotient of the object `hcoker` speaks of and does not bound
  its sections.  Both are therefore carried at the presheaf level, which is the level
  `AlgebraicGeometry.Stack.IsParasitic` is stated at and the level the one-line argument of the
  source consumes; this is the same reading
  `AlgebraicGeometry.Stack.isIso_restrictModuleFunctorToSmallEtale_map_of_isParasitic` carries,
  the step of **Stacks 0GQK** that is independent of the coherator (**Stacks 0GQK** itself is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_restrict_coheratorAdjunction_counit`).

Neither of `hker` and `hcoker` is the conclusion in disguise: both are conditions on the kernel
and the cokernel alone, they mention no object of `𝒴` and no flatness, and the step from them to
the conclusion — that parasiticity at the single flat object `y` already forces bijectivity
there — is what is proved.

Quasi-compactness (**Stacks 050U**) and quasi-separatedness (**Stacks 04YW**) of `f` are
hypotheses of the tagged statement, as they are of the source, but the argument does not
consume them, and they are named `_hqc` and `_hqs` to record that.  The source spends them on
**Stacks 077A**, to produce the middle direct image, and that functor is carried as data here, so
the two conditions stand behind the data.

## Implementation notes

The source of `f` is presented strictly, its structure functor written as the morphism's functor
followed by the structure functor of the target, which is the presentation
`AlgebraicGeometry.Stack.quasicoherentDirectImageOfEtale` uses.  The universes are those of
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`: the site of a stack is a `Type (u + 1)`
with morphisms in `Type u`, essentially `u`-small, and the module sections live in `u`.

The parasitic condition is stated for the étale name of the structure sheaf, as in
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules`; the underlying presheaf of
rings does not depend on the name.

## References

* [Stacks Project, Tag 0GQQ](https://stacks.math.columbia.edu/tag/0GQQ)
* [Stacks Project, Tag 0GQK](https://stacks.math.columbia.edu/tag/0GQK)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 0GQX](https://stacks.math.columbia.edu/tag/0GQX)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A map of modules whose kernel and cokernel are parasitic is invertible on sections over a
flat object.**  Evaluation at an object of the site is exact on presheaves of modules, so it
carries the kernel and the cokernel of `φ` to those of the map of modules `φ` induces at that
object; a parasitic presheaf has vanishing module of sections at every flat object, so that map
is injective and surjective, hence invertible. -/
theorem isIso_app_of_isParasitic {𝒵 : AlgebraicStacks.{u, w} B S hS}
    {M N : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj}
    (φ : M ⟶ N)
    (hker : IsParasitic B S hS 𝒵 .etale (kernel φ))
    (hcoker : IsParasitic B S hS 𝒵 .etale (cokernel φ))
    (y : 𝒵.val.val.obj) (hy : flatObject B S hS 𝒵.val y) :
    IsIso (φ.app (op y)) := by
  have hmono : Mono (φ.app (op y)) := (ModuleCat.mono_iff_injective _).2
    (PresheafOfModules.injective_app_of_subsingleton_kernel φ (op y) (hker y hy))
  have hepi : Epi (φ.app (op y)) := (ModuleCat.epi_iff_surjective _).2
    (PresheafOfModules.surjective_app_of_subsingleton_cokernel φ (op y) (hcoker y hy))
  exact isIso_of_mono_of_epi _

section DirectImage

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} [EssentiallySmall.{u} 𝒴.val.val.obj] (f : 𝒳 ⟶ 𝒴)
  (hincX : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom),
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) .etale).obj F).val)
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))

/-- **The domain of the counit of Stacks 0778 at `D(i ℱ)` is `i` of the composite of
Stacks 077A at `ℱ`.**  This is what makes the component of that counit at an object of `𝒴` the
canonical comparison from the sections of the quasi-coherent direct image to the sections of the
étale one, rather than an arbitrary map between them. -/
theorem quasicoherentToFlatBaseChange_quasicoherentDirectImageOfEtale_obj
    (D : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids)
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)) :
    (quasicoherentToFlatBaseChange B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids hinc).obj
        ((quasicoherentDirectImageOfEtale B E h S hS f hincX hinc hclosed hpres hls hlsD hwp
          hsep D).obj F) =
      (quasicoherentToFlatBaseChange B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids hinc).obj
        ((flatBaseChangeQuasicoherator B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids hinc
            hclosed hpres hls hlsD hwp hsep).obj
          (D.obj ((quasicoherentToFlatBaseChange B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX).obj F))) :=
  rfl

/-- **Stacks 0GQQ.**  Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks over `S`, let `y` be a flat object of `𝒴` and let `ℱ` be an object of
`QCoh(𝒪_𝒳)`.  Then the canonical comparison from the sections at `y` of the quasi-coherent direct
image of **Stacks 077A** to the sections at `y` of the étale direct image is invertible:

`(f_*ℱ)(y) = (f_{QCoh,*}ℱ)(y)` and `(R^i f_*ℱ)(y) = (R^i f_{QCoh,*}ℱ)(y)`.

The comparison is the component at `y` of the counit `ε : i Q(𝓖) ⟶ 𝓖` of the adjunction of
**Stacks 0778** at `𝓖 = D(i ℱ)`, whose domain is `i` of the composite of **Stacks 077A** by
`AlgebraicGeometry.Stack.quasicoherentToFlatBaseChange_quasicoherentDirectImageOfEtale_obj`.
Both halves of the source are covered at once: `D` is the étale direct image for the first and
its `i`-th right derived functor for the second.

The hypotheses `hker` and `hcoker` are **Stacks 0779** part (2) read at the presheaf level; see
"Carried versus proved" in the module documentation for why the library's part (2) does not
discharge them.  Everything else is proved, by
`AlgebraicGeometry.Stack.isIso_app_of_isParasitic`.  The two hypotheses on `f` are named `_hqc`
and `_hqs` because the argument does not consume them: they are the source's, and they stand
behind the carried data `D`. -/
@[stacks 0GQQ "the canonical comparison, namely the counit of Stacks 0778, is invertible on \
  sections over a flat object: both (f_*F)(y) = (f_{QCoh,*}F)(y) and (R^i f_*F)(y) = \
  (R^i f_{QCoh,*}F)(y), never an unspecified isomorphism. Carried: the middle étale direct \
  image of Stacks 077A on LQCoh^fbc, as data D exactly as in 0GQX; and hker, hcoker, which are \
  Stacks 0779 part (2), its library form needing Stacks 0771 part (2) to reach this reading"]
theorem isIso_app_quasicoherentDirectImageOfEtale_counit
    (_hqc : IsQuasiCompactMorphism B S hS f)
    (_hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (D : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids)
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom))
    (hker : IsParasitic B S hS 𝒴 .etale
      (kernel ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app
          (D.obj ((quasicoherentToFlatBaseChange B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX).obj F))).hom.val))
    (hcoker : IsParasitic B S hS 𝒴 .etale
      (cokernel ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app
          (D.obj ((quasicoherentToFlatBaseChange B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX).obj F))).hom.val))
    (y : 𝒴.val.val.obj) (hy : flatObject B S hS 𝒴.val y) :
    IsIso (((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app
        (D.obj ((quasicoherentToFlatBaseChange B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX).obj F))).hom.val.app
            (op y)) :=
  isIso_app_of_isParasitic B S hS _ hker hcoker y hy

end DirectImage

end AlgebraicGeometry.Stack

end
