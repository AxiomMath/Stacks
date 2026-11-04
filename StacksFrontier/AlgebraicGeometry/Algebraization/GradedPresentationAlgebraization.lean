module

public import StacksFrontier.AlgebraicGeometry.Algebraization.GradedAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal

/-!
# Algebraizing through a graded presentation on a punctured spectrum

Let `S` be an algebraization situation with `A` graded, `𝔞 = A₊` and `I` homogeneous, and let
`(ℱ_U,ₙ)` be an object of `Coh(U, I𝒪_U)` presented as `(M̃ₙ|_U)` by an inverse system `(Mₙ)` of
graded `A`-modules which extends canonically to `X = Spec(A)`. Stacks 0EL4 produces a finite graded
`A`-module `N` whose adic quotients are linked to `(Mₙ)` by degree-preserving maps, modulo
`A₊`-power torsion.

This file carries that link to another scheme. Let `W` be a locally Noetherian scheme with an
ideal sheaf `𝒥`, let `(ℱₙ)` be an object of `Coh(W, 𝒥)`, and let `Φ` be a functor from graded
`A`-modules to quasi-coherent `𝒪_W`-modules which

* inverts every map with `A₊`-power torsion kernel and cokernel,
* sends the adic quotients `(N/Iⁿ⁺¹N)` of a finite graded module to the completion of a coherent
  `𝒪_W`-module along `𝒥`, and
* sends `(Mₙ)` to `(ℱₙ)`.

Then `(ℱₙ)` is the completion of a coherent `𝒪_W`-module. This is the last step of the proof of
Stacks 0EL5, where `W = P` is a proper scheme over a field, `A = Γ_*(P, 𝓛)`, `U` is the punctured
affine cone over `P` and `Φ` is `M ↦ M̃` on `P = Proj(A)`: the ladder of degree-preserving maps
becomes, under `Φ`, a pro-isomorphism between the completion of `Φ(N)` and `(ℱₙ)`, and two objects
of `Coh(W, 𝒥)` with isomorphic pro-objects are isomorphic (Stacks 0EIQ).

## Main results

* `Stacks.Algebraization.isCompletionOfCoherent_of_gradedPresentation` — the transfer.

## Implementation notes

The source reads the pro-isomorphism of Stacks 0EL4 (a) in the category of graded modules modulo
`A₊`-power torsion modules, and applies to it the functor that `M ↦ M̃` induces on that quotient
category. The ladder of
`Stacks.Algebraization.exists_finite_graded_ladder_of_canonicallyExtends` is used here instead: it
is the explicit form of that pro-isomorphism, and a functor carries a ladder to a ladder
(`Stacks.ProObject.HasProLadder.map`), so the quotient category, whose morphisms live in a larger
universe than those of `Coh(W)`, never has to be mapped out of.

## References

* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5)
* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EIQ](https://stacks.math.columbia.edu/tag/0EIQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.LocalCohomology
open Stacks.ProObject
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u v

namespace Stacks.Algebraization

/-- **Algebraization through a graded presentation.** In an algebraization situation with `A`
graded, `𝔞 = A₊` and `I` homogeneous, let `(ℱ_U,ₙ)` be an object of `Coh(U, I𝒪_U)` presented as
`(M̃ₙ|_U)` by an inverse system `(Mₙ)` of graded `A`-modules and extending canonically to `X`. Let
`(ℱₙ)` be an object of `Coh(W, 𝒥)` on a locally Noetherian scheme `W`, and let `Φ` be a functor
from graded `A`-modules to quasi-coherent `𝒪_W`-modules which inverts the maps with `A₊`-power
torsion kernel and cokernel, sends the adic quotients of every finite graded module to the
completion of a coherent module, and sends `(Mₙ)` to `(ℱₙ)`, the last two as isomorphisms of
inverse systems of `𝒪_W`-modules. Then `(ℱₙ)` is the completion of a coherent `𝒪_W`-module. -/
public theorem isCompletionOfCoherent_of_gradedPresentation
    (S : AlgebraizationSituation.{u})
    {σ : Type v} [SetLike σ S.A] [AddSubgroupClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hIhom : S.I.IsHomogeneous 𝒜)
    (M : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, v} 𝒜)
    (FU : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hpres : Nonempty (FU.obj ≅ M ⋙ GradedModuleCat.toModuleCat 𝒜 ⋙ tilde.functor (.of S.A) ⋙
      Scheme.Modules.restrictFunctor S.U.ι))
    (hext : CanonicallyExtends S FU)
    {W : Scheme.{u}} [IsLocallyNoetherian W] (J : W.IdealSheafData)
    (F : Stacks.Coherent.CoherentAdicSystems J)
    (Φ : GradedModuleCat.{u, u, v} 𝒜 ⥤ Scheme.QuasicoherentModules W)
    (hΦ : (GradedModuleCat.isoModTorsion 𝒜
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal).IsInvertedBy Φ)
    (hΦN : ∀ N : GradedModuleCat.{u, u, v} 𝒜, Module.Finite S.A N.carrier →
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules W.ringCatSheaf,
        Nonempty ((GradedModuleCat.adicQuotients 𝒜 N S.I hIhom ⋙ Φ) ⋙ ObjectProperty.ι _ ≅
          ((completionFunctor W J).obj G).obj))
    (hΦM : Nonempty ((M ⋙ Φ) ⋙ ObjectProperty.ι _ ≅ F.obj)) :
    IsCompletionOfCoherent J F := by
  classical
  obtain ⟨N, hNg, hNm, 𝒩, hNdec, hNfin, hNgr, -, Hm, 𝓗, iH, Nsys, 𝒩s, ε, ρ, L,
      hHgr, hHtr, hε, hε', hεtr, hρgr, hρker, hρcoker, hLf, hLg⟩ :=
    @exists_finite_graded_ladder_of_canonicallyExtends S σ _ _ 𝒜 _ hirr hIhom
      (M ⋙ GradedModuleCat.toModuleCat 𝒜) (fun n => (M.obj (op n)).grade)
      (fun n => (M.obj (op n)).decomposition)
      (fun n _ _ _ _ ha hx => GradedModuleCat.smul_mem_grade 𝒜 (M.obj (op n)) ha hx)
      (fun _ _ h d x hx => (M.map (homOfLE h).op).map_grade d x hx) FU hpres hext
  let Ngr : GradedModuleCat.{u, u, v} 𝒜 := GradedModuleCat.ofGrading 𝒜 N 𝒩 hNgr
  let Hg : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, v} 𝒜 := GradedModuleCat.liftSystem 𝒜 Hm 𝓗 hHgr hHtr
  let Q := GradedModuleCat.adicQuotients 𝒜 Ngr S.I hIhom
  -- the adic quotients of `N` are the system `Nsys`, as inverse systems of modules
  let eN : Q ⋙ GradedModuleCat.toModuleCat 𝒜 ≅ Nsys :=
    NatIso.ofComponents (fun k => (ε k.unop).toModuleIso) (fun {k l} φ => by
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
      rw [Subsingleton.elim φ (homOfLE (leOfHom φ.unop)).op]
      exact (hεtr l.unop k.unop (leOfHom φ.unop) x).symm)
  -- a ladder of degree-preserving maps between the adic quotients and `(Γ(U, ℱₙ))`
  have hlad : HasProLadder Q Hg := by
    refine GradedModuleCat.hasProLadder_of_toModuleCat 𝒜 (L.ofIsoLeft eN.symm) ?_ ?_
    · rintro k d _ ⟨x, hx, rfl⟩
      exact hLf k d _ (hε (L.p k) d x hx)
    · intro n d y hy
      obtain ⟨x, hx, hxz⟩ := hε' n d _ (hLg n d y hy)
      refine ⟨x, hx, ?_⟩
      show Submodule.Quotient.mk x = (ε n).symm ((L.g n).hom y)
      rw [← hxz, LinearEquiv.symm_apply_apply]
  -- the restriction maps `(Mₙ) → (Γ(U, ℱₙ))` are inverted by `Φ`
  let ρg : M ⟶ Hg :=
    { app := fun n => ⟨(ρ.app n).hom, fun d x hx => hρgr n.unop d x hx⟩
      naturality := fun _ _ f =>
        GradedModuleCat.hom_ext (congrArg ModuleCat.Hom.hom (ρ.naturality f)) }
  have hρΦ : ∀ n, IsIso ((Functor.whiskerRight ρg Φ).app n) := fun n => hΦ _ (by
    rw [← hirr]
    exact ⟨hρker n.unop, hρcoker n.unop⟩)
  have : IsIso (Functor.whiskerRight ρg Φ) := NatIso.isIso_of_isIso_app _
  -- the pro-isomorphism on `W`
  obtain ⟨G, ⟨eG'⟩⟩ := hΦN Ngr hNfin
  obtain ⟨eM'⟩ := hΦM
  let eG : Q ⋙ Φ ≅ Stacks.Coherent.quasicoherentDiagram ((completionFunctor W J).obj G) :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight ℕᵒᵖ).preimageIso eG'
  let eM : M ⋙ Φ ≅ Stacks.Coherent.quasicoherentDiagram F :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight ℕᵒᵖ).preimageIso eM'
  obtain ⟨eQH⟩ := nonempty_colimitYonedaIso_of_hasProLadder (hlad.map Φ)
  obtain ⟨e⟩ : Nonempty (Stacks.Coherent.diagramToPro
      (Stacks.Coherent.quasicoherentDiagram ((completionFunctor W J).obj G)) ≅
        Stacks.Coherent.diagramToPro (Stacks.Coherent.quasicoherentDiagram F)) :=
    (Stacks.Coherent.nonempty_colimitYonedaIso_iff _ _).2
      ⟨(colimitYonedaIsoOfNatIso eG).symm ≪≫ eQH ≪≫
        (colimitYonedaIsoOfNatIso (asIso (Functor.whiskerRight ρg Φ))).symm ≪≫
          colimitYonedaIsoOfNatIso eM⟩
  obtain ⟨hff⟩ := Stacks.Coherent.coherentAdicToPro_fullyFaithful W J
  exact ⟨G, ⟨(ObjectProperty.ι _).mapIso (hff.preimageIso e)⟩⟩

end Stacks.Algebraization

end
