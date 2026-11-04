module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleUnique
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# `F_d` is a separated presheaf on the Zariski site

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), and fix an
integer `d`. Section 01NS attaches to `d` the functor `F_d` whose value on a test scheme `T` is
the set of strict equivalence classes of quadruples `(d, f : T → S, L, ψ)`. Step (1) of the proof
of Tag 01NV is that `F_d` is a **Zariski sheaf**. That has two halves, and this file proves the
first of them, unconditionally:

**a class in `F_d(T)` is determined by its restrictions to the members of an open covering of
`T`.**

## The argument

Two quadruples `P`, `Q` over the same `f : T ⟶ S` whose restrictions to the members of an open
covering are strictly equivalent are strictly equivalent. The comparison is *not* glued from the
local ones. Instead the degree-one component `ψ_1 : f^*𝒜_d ⟶ L` of `ψ`, which Section 01NS
requires to be surjective, is used: sheaves of `𝒪_T`-modules form an abelian category, and two
epimorphisms out of one object each of whose kernels is killed by the other have canonically
isomorphic targets. The hypothesis that makes that applicable,

`kernel.ι (P.ψ_1) ≫ Q.ψ_1 = 0`,

is a single equation between morphisms of sheaves of modules, hence local, and locally it holds
because a local comparison exists: pulling back, `Q.ψ_1` factors through `P.ψ_1`, which kills its
own kernel. Only the functoriality of the inverse image and the fact that it preserves the zero
morphism enter — the inverse image is *not* required to be exact, and no kernel is ever glued.

The isomorphism `β : L ≅ L'` so obtained is promoted to an isomorphism of the Laurent algebras by
`...RelativeProjQcohSheaf.LaurentAlgebraCongr.laurentCongrIso`, and the compatibility of that
isomorphism with `ψ` in *every* integral degree is again checked locally. What makes the check go
through in all degrees at once is `...RelativeProjQcohSheaf.laurent_app_eq_of_app_one`: on each
member of the covering the restriction of the global comparison and the given local comparison are
two homomorphisms of Laurent algebras with the same degree-one component — the two agree there
because the restricted `ψ_1` is still surjective — so they agree in every degree.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app_comp_eq_of_cover`: a morphism
  carrying one `ψ` to another is detected by the restrictions of the two maps to an open
  covering.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_of_cover`:
  **strict equivalence of quadruples is local on the test scheme.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.eq_of_pullback_eq_of_cover`: a class in
  `F_d(T)` is determined by its restrictions to an open covering of `T`, and
  `...Fd.eq_of_pullback_eq_of_openImmersion_cover`: the same for a jointly surjective family of
  open immersions, which is how the Zariski topology on `Sch` presents its coverings.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.isSeparated_functor`: **the functor `F_d` is
  a separated presheaf on the big Zariski site**, which is the separatedness half of step (1) in
  the vocabulary of the site.

## No tag is claimed

Nothing here carries a `stacks` attribute. What is proved is the separatedness half of step (1)
of the proof of Tag 01NV; the **glueing** half — assembling a quadruple over `T` out of
quadruples given on the members of a covering and strict equivalences on the overlaps — is not
proved, so the Zariski-sheaf property of `F_d` is not established and the hypothesis carrying it
in `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Representable` is not discharged. What
`...RelativeProjQcohSheaf.SmallModel.Fd.isSheaf_functor_of_exists_amalgamation` does with the
separatedness proved here is to *reduce* that hypothesis to the glueing half alone: `F_d` is a
Zariski sheaf as soon as compatible families on covering sieves have amalgamations. The
separatedness is used a second time in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiAmalgamation`, to show that the
glueing half is *equivalent* to `...ZariskiAmalgamation.QuadrupleGlues`, the glueing described
above stated for a covering of `T` by opens and for a morphism `T ⟶ S` that is itself glued from
the local ones; that reformulation is not a proof of it. The
separatedness also gives the locality of the smallness of the sets `F_d(T)`
(`...SmallModel.Fd.small_of_cover`), and through it the derivation of that smallness from Tag
01NU (`...SmallModel.Fd.small_of_baseCover`).

## Implementation notes

The locality of strict equivalence is proved for a covering by *opens* of `T`, because that is the
shape in which the locality of morphisms of sheaves of modules is available. The passage to a
jointly surjective family of open immersions, which is the shape of a Zariski covering, is made
once and only at the level of `F_d`: an open immersion is an isomorphism onto its image
(`AlgebraicGeometry.Scheme.Hom.isoOpensRange`) and `F_d` carries an isomorphism of test schemes to
a bijection by its two functor laws, so the two restrictions have the same kernel. Making the same
passage for quadruples would need the descent of a strict equivalence along an isomorphism of test
schemes, which is more than is wanted here.

`hom_ext_of_opens_cover` is `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover`
restated at the spelling `Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom g)` that the
quadruples of Section 01NS are written in; the two functors, and the two categories of sheaves of
modules, are equal by `rfl`, so it is the same theorem and not a second proof.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory modulesAbelian

variable {T' T S : Scheme.{u}}

/-! ### Two epimorphisms whose kernels kill each other -/

/-- **Two epimorphisms out of one object of an abelian category whose kernels are each killed by
the other have canonically isomorphic targets**, by an isomorphism carrying the first
epimorphism to the second.

Both maps factor through the other by `CategoryTheory.Abelian.epiDesc`, and the two factorisations
are mutually inverse because an epimorphism can be cancelled. -/
private theorem exists_iso_of_epi_pair {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    (p : X ⟶ Y) (q : X ⟶ Z) [Epi p] [Epi q]
    (hpq : kernel.ι p ≫ q = 0) (hqp : kernel.ι q ≫ p = 0) :
    ∃ e : Y ≅ Z, p ≫ e.hom = q :=
  ⟨{ hom := Abelian.epiDesc p q hpq
     inv := Abelian.epiDesc q p hqp
     hom_inv_id := by
       rw [← cancel_epi p, Category.comp_id, ← Category.assoc, Abelian.comp_epiDesc,
         Abelian.comp_epiDesc]
     inv_hom_id := by
       rw [← cancel_epi q, Category.comp_id, ← Category.assoc, Abelian.comp_epiDesc,
         Abelian.comp_epiDesc] },
    Abelian.comp_epiDesc p q hpq⟩

/-! ### Locality of morphisms of sheaves of modules, at the spelling of Section 01NS -/

/-- **Equality of morphisms of sheaves of modules is local**, at the spelling
`Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom g)` of the inverse image that the quadruples
of Section 01NS are written in. This is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover`; the two spellings of the
inverse image, and the two of the category of sheaves of modules on a scheme, are equal by
`rfl`. -/
theorem hom_ext_of_opens_cover
    {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} {φ φ' : M ⟶ N}
    {ι : Type*} (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (h : ∀ a, (pullbackFunctor (ringedSpaceHom (W a).ι)).map φ =
      (pullbackFunctor (ringedSpaceHom (W a).ι)).map φ') : φ = φ' :=
  Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover W hW h

/-- The inverse image of sheaves of modules along a morphism of schemes kills the zero morphism,
at the spelling of Section 01NS. The inverse image is a left adjoint, hence additive. -/
private theorem map_zero_pullbackFunctor (g : T' ⟶ T)
    (M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    (pullbackFunctor (ringedSpaceHom g)).map (0 : M ⟶ N) = 0 :=
  (Scheme.Modules.pullback g).map_zero M N

/-- **The hypothesis of `exists_iso_of_epi_pair`, verified locally.** If after restriction to each
member of an open covering `q` factors through `p`, then the kernel of `p` is killed by `q`.

Only the functoriality of the inverse image and the fact that it preserves the zero morphism are
used; the inverse image is *not* required to be exact, and the kernel of `p` is never compared
with a kernel on a member of the covering. -/
private theorem kernel_comp_eq_zero_of_cover {ι : Type*} (W : ι → T.Opens)
    (hW : ∀ x : T, ∃ a, x ∈ W a)
    {M N N' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (p : M ⟶ N) (q : M ⟶ N')
    (h : ∀ a, ∃ v, (pullbackFunctor (ringedSpaceHom (W a).ι)).map p ≫ v =
      (pullbackFunctor (ringedSpaceHom (W a).ι)).map q) :
    kernel.ι p ≫ q = 0 := by
  refine hom_ext_of_opens_cover W hW fun a => ?_
  obtain ⟨v, hv⟩ := h a
  rw [CategoryTheory.Functor.map_comp, ← hv, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, kernel.condition, map_zero_pullbackFunctor, zero_comp,
    map_zero_pullbackFunctor]

/-! ### Reading the pullback of `ψ` backwards -/

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **A morphism carrying the pullback of `ψ` to the pullback of `ψ'` in degree `n` produces one
carrying the inverse image of `ψ_n` to the inverse image of `ψ'_n`.** The contraction of the
iterated pullback inside `Twisting.pullbackApp` is an isomorphism and is cancelled; the comparison
of the integral tensor powers of Tag 01CU is transposed to the other side. -/
theorem map_app_comp_of_pullbackApp (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (g : T' ⟶ T) (n : ℤ)
    (w : (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece n ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')).piece n)
    (h : ψ.pullbackApp g n ≫ w = ψ'.pullbackApp g n) :
    (pullbackFunctor (ringedSpaceHom g)).map (ψ.app n) ≫
        laurentPullback g L n ≫ w ≫ inv (laurentPullback g L' n) =
      (pullbackFunctor (ringedSpaceHom g)).map (ψ'.app n) := by
  have h2 : (pullbackFunctor (ringedSpaceHom g)).map (ψ.app n) ≫ laurentPullback g L n ≫ w =
      (pullbackFunctor (ringedSpaceHom g)).map (ψ'.app n) ≫ laurentPullback g L' n :=
    (cancel_epi (compComparison g f (A.piece (n * d)))).mp
      (by simpa only [Twisting.pullbackApp, Category.assoc] using h)
  have hassoc : (pullbackFunctor (ringedSpaceHom g)).map (ψ.app n) ≫
        laurentPullback g L n ≫ w ≫ inv (laurentPullback g L' n) =
      ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app n) ≫ laurentPullback g L n ≫ w) ≫
        inv (laurentPullback g L' n) := by
    simp only [Category.assoc]
  rw [hassoc, h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The transport of a global morphism carries `ψ` to `ψ'` after inverse image if it does so
after transport.** This is `map_app_comp_of_pullbackApp` with the morphism `w` of the shape the
transport of a global morphism has, so that the two copies of the comparison of the integral
tensor powers cancel and the conclusion is about `ψ_n ≫ u` itself. -/
theorem map_app_comp_of_pullbackApp_laurentTransport (ψ : Twisting f A d L)
    (ψ' : Twisting f A d L') (g : T' ⟶ T) (n : ℤ)
    (u : (laurent L).piece n ⟶ (laurent L').piece n)
    (h : ψ.pullbackApp g n ≫ laurentTransport g L L' n n u = ψ'.pullbackApp g n) :
    (pullbackFunctor (ringedSpaceHom g)).map (ψ.app n ≫ u) =
      (pullbackFunctor (ringedSpaceHom g)).map (ψ'.app n) := by
  have hu : laurentPullback g L n ≫ laurentTransport g L L' n n u ≫
      inv (laurentPullback g L' n) = (pullbackFunctor (ringedSpaceHom g)).map u := by
    simp only [laurentTransport, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [CategoryTheory.Functor.map_comp, ← hu]
  exact ψ.map_app_comp_of_pullbackApp ψ' g n _ h

/-- **A morphism carrying one `ψ` to another is detected by an open covering of the test
scheme.** If after restriction to each member of an open covering the transport of `u` carries the
restricted `ψ` to the restricted `ψ'`, then `u` carries `ψ_n` to `ψ'_n`. -/
theorem app_comp_eq_of_cover {ι : Type*} (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (ψ : Twisting f A d L) (ψ' : Twisting f A d L') (n : ℤ)
    (u : (laurent L).piece n ⟶ (laurent L').piece n)
    (h : ∀ a, ψ.pullbackApp (W a).ι n ≫ laurentTransport (W a).ι L L' n n u =
      ψ'.pullbackApp (W a).ι n) :
    ψ.app n ≫ u = ψ'.app n :=
  hom_ext_of_opens_cover W hW fun a =>
    ψ.map_app_comp_of_pullbackApp_laurentTransport ψ' (W a).ι n u (h a)

end Twisting

/-! ### Strict equivalence of quadruples is local -/

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- The first condition on a witness of a strict equivalence, read as the identification of the
degree-one component of `γ` with `β` through the identification `L^{⊗ 1} = L` of Tag 01CU. This
is the form `...RelativeProjQcohSheaf.laurent_app_eq_of_app_one` consumes. -/
private theorem app_one_comp_oneIsoL {P Q : Quadruple f A d} {β : P.L ≅ Q.L}
    {γ : laurent P.L ≅ laurent Q.L} (h1 : γ.hom.app 1 = (pieceOneIso β).hom) :
    γ.hom.app 1 ≫ (oneIsoL Q.L).hom = (oneIsoL P.L).hom ≫ β.hom := by
  have h : γ.hom.app 1 = P.oneIso.hom ≫ β.hom ≫ Q.oneIso.inv := h1
  rw [h]
  simp

/-- **Strict equivalence of quadruples is local on the test scheme.** Two quadruples over the
same morphism `f : T ⟶ S` whose restrictions to the members of an open covering of `T` are
strictly equivalent are strictly equivalent.

Nothing is assumed beyond Situation 01NN; in particular the comparison is not glued. The
degree-one component `ψ_1` of `ψ`, surjective by `Quadruple.epi_app_one`, and its counterpart for
the second quadruple are two epimorphisms out of `f^*𝒜_d`, and each kills the other's kernel
because it does so after restriction to a member of the covering, where a comparison exists. So
their targets `L^{⊗ 1}` and `(L')^{⊗ 1}` are isomorphic over `f^*𝒜_d`, which gives the
isomorphism `β : L ≅ L'`, and `...LaurentAlgebraCongr.laurentCongrIso` promotes it to an
isomorphism `γ` of the Laurent algebras with that degree-one component.

That `γ` carries `ψ` to `ψ'` in *every* integral degree is then local as well: on each member of
the covering the restriction of `γ` and the given local comparison are homomorphisms of Laurent
algebras whose degree-one components agree — they agree because the restricted `ψ_1` is still
surjective — hence agree in every degree by
`...RelativeProjQcohSheaf.laurent_app_eq_of_app_one`. -/
theorem strictlyEquivalent_of_cover {ι : Type*} (W : ι → T.Opens)
    (hW : ∀ x : T, ∃ a, x ∈ W a) (P Q : Quadruple f A d)
    (h : ∀ a, StrictlyEquivalent (P.pullback (W a).ι) (Q.pullback (W a).ι)) :
    StrictlyEquivalent P Q := by
  have h' : ∀ a : ι, ∃ (β : (P.pullback (W a).ι).L ≅ (Q.pullback (W a).ι).L)
      (γ : laurent (P.pullback (W a).ι).L ≅ laurent (Q.pullback (W a).ι).L),
      γ.hom.app 1 = (pieceOneIso β).hom ∧
        ∀ n : ℤ, (P.pullback (W a).ι).twisting.app n ≫ γ.hom.app n =
          (Q.pullback (W a).ι).twisting.app n := h
  choose βa γa h1 hψ using h'
  let := P.epi_app_one
  let := Q.epi_app_one
  have hfwd : ∀ a : ι, ∃ v,
      (pullbackFunctor (ringedSpaceHom (W a).ι)).map (P.twisting.app 1) ≫ v =
        (pullbackFunctor (ringedSpaceHom (W a).ι)).map (Q.twisting.app 1) := fun a =>
    ⟨_, P.twisting.map_app_comp_of_pullbackApp Q.twisting (W a).ι 1 ((γa a).hom.app 1) (hψ a 1)⟩
  have hbwd : ∀ a : ι, ∃ v,
      (pullbackFunctor (ringedSpaceHom (W a).ι)).map (Q.twisting.app 1) ≫ v =
        (pullbackFunctor (ringedSpaceHom (W a).ι)).map (P.twisting.app 1) := by
    intro a
    have hh : (γa a).hom.app 1 ≫ (γa a).inv.app 1 =
        CategoryStruct.id ((laurent (P.pullback (W a).ι).L).piece 1) :=
      congrArg (fun φ : laurent (P.pullback (W a).ι).L ⟶ laurent (P.pullback (W a).ι).L =>
        φ.app 1) (γa a).hom_inv_id
    have hgoal : (Q.pullback (W a).ι).twisting.app 1 ≫ (γa a).inv.app 1 =
        (P.pullback (W a).ι).twisting.app 1 := by
      rw [← hψ a 1, Category.assoc, hh, Category.comp_id]
    exact ⟨_, Q.twisting.map_app_comp_of_pullbackApp P.twisting (W a).ι 1 ((γa a).inv.app 1)
      hgoal⟩
  obtain ⟨e, he⟩ := exists_iso_of_epi_pair (P.twisting.app 1) (Q.twisting.app 1)
    (kernel_comp_eq_zero_of_cover W hW _ _ hfwd) (kernel_comp_eq_zero_of_cover W hW _ _ hbwd)
  obtain ⟨Γ, hΓ1⟩ : ∃ Γ : laurent P.L ≅ laurent Q.L, Γ.hom.app 1 = e.hom :=
    ⟨laurentCongrIso ((oneIsoL P.L).symm ≪≫ e ≪≫ oneIsoL Q.L), by
      rw [laurentCongrIso_app_one]; simp⟩
  have hcompat1 : P.twisting.app 1 ≫ Γ.hom.app 1 = Q.twisting.app 1 := by rw [hΓ1]; exact he
  have key : ∀ (a : ι) (n : ℤ),
      laurentTransport (W a).ι P.L Q.L n n (Γ.hom.app n) = (γa a).hom.app n := by
    intro a n
    let : Epi ((P.pullback (W a).ι).twisting.app 1) := (P.pullback (W a).ι).epi_app_one
    have hδ1 : (P.pullback (W a).ι).twisting.app 1 ≫
          laurentTransport (W a).ι P.L Q.L 1 1 (Γ.hom.app 1) =
        (Q.pullback (W a).ι).twisting.app 1 :=
      Twisting.pullbackApp_comp_laurentTransport_of_app P.twisting Q.twisting (W a).ι 1
        (Γ.hom.app 1) hcompat1
    have heq1 : laurentTransport (W a).ι P.L Q.L 1 1 (Γ.hom.app 1) = (γa a).hom.app 1 :=
      (cancel_epi ((P.pullback (W a).ι).twisting.app 1)).mp (hδ1.trans (hψ a 1).symm)
    have hone : (γa a).hom.app 1 ≫ (oneIsoL (Q.pullback (W a).ι).L).hom =
        (oneIsoL (P.pullback (W a).ι).L).hom ≫ (βa a).hom := app_one_comp_oneIsoL (h1 a)
    exact laurent_app_eq_of_app_one (γ := laurentPullbackHom (W a).ι Γ.hom)
      (γ' := (γa a).hom) (e := βa a) (by rw [laurentPullbackHom_app, heq1]; exact hone) hone n
  refine (strictlyEquivalent_iff_exists_hom P Q).mpr ⟨Γ, fun n => ?_⟩
  refine Twisting.app_comp_eq_of_cover W hW P.twisting Q.twisting n (Γ.hom.app n) fun a => ?_
  rw [key a n]
  exact hψ a n

end Quadruple

/-! ### `F_d` is a separated presheaf -/

/-- **`F_d` is a separated presheaf**: a class in `F_d(T)` is determined by its restrictions to
the members of an open covering of `T`. This is the separatedness half of step (1) of the proof
of Tag 01NV, and it is unconditional.

A class consists of a morphism `T ⟶ S` and a strict equivalence class of quadruples over it. The
morphism is determined because a morphism of schemes is determined by its restrictions to an open
covering (`AlgebraicGeometry.Scheme.hom_ext_of_forall`), and the class of the quadruple is then
determined by `Quadruple.strictlyEquivalent_of_cover`. -/
theorem Fd.eq_of_pullback_eq_of_cover
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {ι : Type*} (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a) (ξ η : Fd A d T)
    (h : ∀ a, Fd.pullback (W a).ι ξ = Fd.pullback (W a).ι η) : ξ = η := by
  obtain ⟨f₁, q₁⟩ := ξ
  obtain ⟨f₂, q₂⟩ := η
  obtain rfl : f₁ = f₂ := by
    refine Scheme.hom_ext_of_forall f₁ f₂ fun x => ?_
    obtain ⟨a, ha⟩ := hW x
    exact ⟨W a, ha, congrArg (fun ζ : Fd A d (W a) => ζ.1) (h a)⟩
  obtain ⟨P, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨Q, rfl⟩ := Quotient.exists_rep q₂
  refine (Fd.mk_eq_mk_iff P Q).mpr (Quadruple.strictlyEquivalent_of_cover W hW P Q fun a => ?_)
  exact (Fd.mk_eq_mk_iff (P.pullback (W a).ι) (Q.pullback (W a).ι)).mp (h a)

/-- **`F_d` is a separated presheaf for a covering by open immersions**, which is the shape in
which the Zariski topology on `Sch` presents its coverings: a class in `F_d(T)` is determined by
its restrictions along a jointly surjective family of open immersions `g i : Z i ⟶ T`.

This is `Fd.eq_of_pullback_eq_of_cover` applied to the images of the `g i`: an open immersion is
an isomorphism onto its image (`AlgebraicGeometry.Scheme.Hom.isoOpensRange`), and `F_d` carries an
isomorphism of test schemes to a bijection by its two functor laws, so restricting along `g i`
and restricting along the inclusion of its image have the same kernel. -/
theorem Fd.eq_of_pullback_eq_of_openImmersion_cover
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ x : T, ∃ i, x ∈ (g i).opensRange) (ξ η : Fd A d T)
    (h : ∀ i, Fd.pullback (g i) ξ = Fd.pullback (g i) η) : ξ = η := by
  refine Fd.eq_of_pullback_eq_of_cover (fun i => (g i).opensRange) hg ξ η fun i => ?_
  have hinj : ∀ ζ : Fd A d ((g i).opensRange),
      Fd.pullback (g i).isoOpensRange.inv (Fd.pullback (g i).isoOpensRange.hom ζ) = ζ := by
    intro ζ
    rw [← Fd.pullback_comp, Iso.inv_hom_id, Fd.pullback_id]
  have hcomp : ∀ ζ : Fd A d T, Fd.pullback (g i).isoOpensRange.hom
      (Fd.pullback ((g i).opensRange).ι ζ) = Fd.pullback (g i) ζ := by
    intro ζ
    rw [← Fd.pullback_comp, Scheme.Hom.isoOpensRange_hom_ι]
  calc Fd.pullback ((g i).opensRange).ι ξ
      = Fd.pullback (g i).isoOpensRange.inv
          (Fd.pullback (g i).isoOpensRange.hom (Fd.pullback ((g i).opensRange).ι ξ)) :=
        (hinj _).symm
    _ = Fd.pullback (g i).isoOpensRange.inv
          (Fd.pullback (g i).isoOpensRange.hom (Fd.pullback ((g i).opensRange).ι η)) :=
        congrArg _ ((hcomp ξ).trans ((h i).trans (hcomp η).symm))
    _ = Fd.pullback ((g i).opensRange).ι η := hinj _

/-- **Step (1) of the proof of Tag 01NV, its separatedness half: the functor `F_d` is a separated
presheaf on the big Zariski site of schemes.** A compatible family of classes given on the
members of a Zariski covering of a test scheme has at most one amalgamation.

A covering sieve of the Zariski topology contains a jointly surjective family of open immersions
(`AlgebraicGeometry.Scheme.exists_cover_of_mem_grothendieckTopology`), and two amalgamations of
one family restrict to it in the same way, so they agree by
`Fd.eq_of_pullback_eq_of_openImmersion_cover`.

This is one of the two halves of the Zariski sheaf property that Tag 01NV's proof uses. The other
half — that a compatible family *has* an amalgamation, which asks for a quadruple over the test
scheme glued from quadruples on the members of the covering — is **proved**, downstream, as
`...RelativeProjQcohSheaf.quadrupleGlues_proof`, so the two together do give
`CategoryTheory.Presieve.IsSheaf`: that is `...RelativeProjQcohSheaf.Fd.isSheaf_functor` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean`, with no
hypothesis. Step (1) is therefore no longer carried anywhere except for the import-order reason
recorded in `...RelativeProjQcohSheaf.SmallModel`;
`CategoryTheory.Presieve.IsSeparated.isSheaf` is the statement that combines the two, and
`...RelativeProjQcohSheaf.SmallModel.Fd.isSheaf_functor_of_exists_amalgamation` is this result fed
into it, which reduces that carried hypothesis to the missing half alone — and
`...RelativeProjQcohSheaf.ZariskiAmalgamation.Fd.quadrupleGlues_iff_isSheaf`, which uses the
separatedness a second time, identifies that half with the glueing of quadruples along a covering
by opens, the morphism to `S` being glued rather than assumed. -/
theorem Fd.isSeparated_functor
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) :
    Presieve.IsSeparated Scheme.zariskiTopology.{u} (Fd.functor A d) := by
  intro T sieve hsieve x t₁ t₂ h₁ h₂
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hsieve
  refine Fd.eq_of_pullback_eq_of_openImmersion_cover (Z := 𝒰.X) 𝒰.f (fun y => ?_) t₁ t₂ fun i => ?_
  · obtain ⟨i, z, hz⟩ := 𝒰.exists_eq y
    exact ⟨i, z, hz⟩
  · have hmem : sieve.arrows (𝒰.f i) := by
      apply hle
      exact Presieve.ofArrows.mk i
    exact (h₁ _ hmem).trans (h₂ _ hmem).symm

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
