module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# H-projective morphisms among the quasi-projective ones

An H-projective morphism — one admitting a closed immersion into `ℙⁿ_S` over `S` — is
H-quasi-projective, and over any base it is H-projective exactly when it is H-quasi-projective
and proper. Conversely an H-quasi-projective morphism is an H-projective one restricted to an
open subscheme of its source: it factors as an open immersion followed by an H-projective
morphism, the intermediate scheme being the scheme-theoretic image of the immersion into
`ℙⁿ_S`.

An H-projective morphism is also projective in the sense of the projective bundle, because
`ℙⁿ_S` *is* the projective bundle of `𝒪_S^{n+1}`; and therefore a morphism which is
H-projective over the members of some open covering of the base is locally projective.

## Main results

* `AlgebraicGeometry.IsProjectiveMorphism.isHQuasiProjective`: an H-projective morphism is
  H-quasi-projective. This is the first clause of [Stacks, Tag 01W9].
* `AlgebraicGeometry.IsProjectiveMorphism.isProjective`: an H-projective morphism is
  projective. This is the second clause of [Stacks, Tag 01W9].
* `AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`: a morphism is
  H-projective if and only if it is H-quasi-projective and proper. This is clause (2) of
  [Stacks, Tag 0BCL].
* `AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`: an
  H-quasi-projective morphism factors as an open immersion followed by an H-projective
  morphism. This is [Stacks, Tag 01WA].
* `AlgebraicGeometry.isLocallyProjective_of_isLocallyProjectiveMorphism`: a morphism which is
  H-projective over the members of an open covering of the base is locally projective. This is
  the implication (2) ⟹ (1) of [Stacks, Tag 01WB].

## Implementation notes

**The base needs no hypothesis.** The source states Tag 0BCL for a quasi-compact and
quasi-separated base, and the statement below drops both. Neither direction uses them: the
forward one is `AlgebraicGeometry.isProper_of_isProjectiveMorphism` together with the first
clause of Tag 01W9, and the backward one cancels the separated structure morphism of `ℙⁿ_S` out
of the proper composite `X ⟶ ℙⁿ_S ⟶ S` and then uses that a proper immersion is a closed
immersion. The source's hypotheses enter its own proof only through the route it takes, which
passes through clause (1) of Tag 0BCL and hence through projectivity in the sense of the
projective bundle.

**Clause (2) of Tag 01W9 goes through the projective bundle of a free module.** Projectivity,
`AlgebraicGeometry.IsProjective`, asks for a closed immersion over the base into
`Stacks.SymGraded.schemeProjectiveBundle ℰ`, the relative homogeneous spectrum of `Sym(ℰ)` for a
quasi-coherent `ℰ` of finite type. Taking `ℰ = 𝒪_S^{n+1}` — quasi-coherent by
`Stacks.SymGraded.isQuasicoherent_freeModule` and of finite type by
`Stacks.SheafOfModules.isFiniteType_free` — the bundle is `ℙⁿ_S` itself over `S`, by the
isomorphism `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` of Tag 01OE and its
compatibility with the two structure morphisms; the closed immersion witnessing H-projectivity
transports across it.

Clause (1) of Tag 0BCL, for projectivity in the sense of clause (1) of Definition 01W8 and over a
quasi-compact quasi-separated base, is
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition`.

**Only the implication (2) ⟹ (1) of Tag 01WB is here.** The converse is
`Stacks.LocallyProjectiveHProjective.isLocallyProjectiveMorphism_of_isLocallyProjective` of
`StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym`, and the equivalence is
`Stacks.LocallyProjectiveHProjective.isLocallyProjective_iff_isLocallyProjectiveMorphism` there.
The converse needs neither a surjection `𝒪_U^{n+1} ↠ ℰ` nor a homomorphism of sheaf symmetric
algebras produced from a homomorphism of modules (which the library does not construct). The chart of `ℙ(ℰ)` over an affine open `V`
of the base is the *absolute* `Proj` of the graded ring of sections of `Sym(ℰ)` over `V`, and is
the inverse image of `V`, so the surjection used is the one of graded rings
`Γ(X, V)[T₀, …, Tₙ] ↠ Γ(V, Sym(ℰ))` coming from generators of the degree-one part, and the closed
immersion is Tag 01N0's.

**The two presentations of a covering are reconciled by the ranges of the covering maps.**
`AlgebraicGeometry.IsLocallyProjectiveMorphism` is stated with an open cover of the base by
schemes and the base changes `pullback.snd f (𝒰.f i)`, while
`AlgebraicGeometry.IsLocallyProjective` is stated with opens of the base and the restrictions
`f ∣_ U`. The opens are the ranges of the covering maps, which cover the base by
`AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`, and over each the base change and the
restriction are isomorphic as arrows by `AlgebraicGeometry.morphismRestrictOpensRange`;
`AlgebraicGeometry.IsProjectiveMorphism.of_iso` carries H-projectivity across that isomorphism.

**The factorisation of Tag 01WA is through the scheme-theoretic image, not through an abstract
closed subscheme.** The source says only that `X' ⊆ ℙⁿ_S` is "a closed subscheme" produced by
Lemma 29.7.7; here `X'` is `AlgebraicGeometry.Scheme.Hom.image` of the immersion, the subscheme
cut out by its kernel ideal sheaf, which is the one that lemma produces. The statement below
existentially quantifies `X'` anyway, so a consumer is not tied to that choice.

The two predicates are spelled with different structure morphisms of `ℙⁿ_S`:
`AlgebraicGeometry.IsProjectiveMorphism` uses `projectiveSpaceOver n S ↘ S` and
`AlgebraicGeometry.IsHQuasiProjective` the first pullback projection it is defined to be. The
two are the same morphism by `rfl`, so no transport appears below.

## References

* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SymGraded

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- **Stacks Project, Tag 01W9, first clause.** An H-projective morphism is
H-quasi-projective: the closed immersion into `ℙⁿ_S` witnessing H-projectivity is an immersion,
and it is quasi-compact because a closed immersion is affine. -/
@[stacks 01W9 "H-quasi-projective"]
theorem IsProjectiveMorphism.isHQuasiProjective (hf : IsProjectiveMorphism f) :
    IsHQuasiProjective f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have := hi
  exact ⟨n, i, inferInstance, inferInstance, hif⟩

/-- **Stacks Project, Tag 01W9, second clause.** An H-projective morphism is projective.

Projective `n`-space over `S` is the projective bundle of the free module `𝒪_S^{n+1}`, which is
quasi-coherent and of finite type; so the closed immersion `X ⟶ ℙⁿ_S` over `S` witnessing
H-projectivity becomes, after composing with the inverse of the isomorphism
`𝐏(𝒪_S^{n+1}) ≅ ℙⁿ_S` of [Stacks, Tag 01OE], a closed immersion of `X` into that projective
bundle over `S`. -/
@[stacks 01W9 "projective"]
theorem IsProjectiveMorphism.isProjective (hf : IsProjectiveMorphism f) : IsProjective f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have := hi
  have hclosed :
      IsClosedImmersion (i ≫ (projectiveBundleIsoProjectiveSpace (X := S) n).inv) :=
    inferInstance
  have hcomm : (i ≫ (projectiveBundleIsoProjectiveSpace (X := S) n).inv) ≫
      (freeProjectiveBundle (X := S) n).toBase = f := by
    rw [Category.assoc, ← projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := S) n,
      Iso.inv_hom_id_assoc]
    exact hif
  exact ⟨freeModule (coordIndex.{u} n), inferInstance, inferInstance,
    isQuasicoherentPieces_free _, i ≫ (projectiveBundleIsoProjectiveSpace (X := S) n).inv,
    hclosed, hcomm⟩

/-- **Stacks Project, Tag 0BCL, clause (2).** A morphism of schemes is H-projective if and only
if it is H-quasi-projective and proper.

Forwards, an H-projective morphism is proper and H-quasi-projective. Backwards, let
`i : X ⟶ ℙⁿ_S` be an immersion over `S` with `i ≫ (ℙⁿ_S ↘ S) = f` proper. The structure
morphism of `ℙⁿ_S` is separated, so `i` is proper, hence a closed map; an immersion with closed
image is a closed immersion.

The base carries no quasi-compactness or quasi-separatedness hypothesis; see the implementation
notes of this file. -/
@[stacks 0BCL "(2)", ega "II 5.5.3" "(i)+(ii) in H-form", ega "II 7.3.9" "special case"]
theorem isProjectiveMorphism_iff_isHQuasiProjective_and_isProper :
    IsProjectiveMorphism f ↔ IsHQuasiProjective f ∧ IsProper f := by
  refine ⟨fun hf => ⟨hf.isHQuasiProjective, isProper_of_isProjectiveMorphism f hf⟩, ?_⟩
  rintro ⟨⟨n, i, hi, -, hif⟩, hf⟩
  have := hi
  have := isProper_projectiveSpaceOver n S
  have hcomp : IsProper (i ≫ (projectiveSpaceOver n S ↘ S)) := by
    rw [show i ≫ (projectiveSpaceOver n S ↘ S) = f from hif]
    exact hf
  have := hcomp
  have := IsProper.of_comp i (projectiveSpaceOver n S ↘ S)
  exact ⟨n, i, IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range, hif⟩

/-- **Stacks Project, Tag 01WA.** An H-quasi-projective morphism factors as an open immersion
followed by an H-projective morphism.

H-quasi-projectivity gives a quasi-compact immersion `i : X ⟶ ℙⁿ_S` over `S`. Being
quasi-compact, `i` is an open immersion onto its scheme-theoretic image `X'` by
[Stacks, Tag 01RG], which is the only place the quasi-compactness is used; and `X'` is a closed
subscheme of `ℙⁿ_S`, so its structure morphism `X' ⟶ S` is H-projective. -/
@[stacks 01WA]
theorem exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective
    (hf : IsHQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ IsProjectiveMorphism p ∧ j ≫ p = f := by
  obtain ⟨n, i, hi, hqc, hif⟩ := hf
  have := hi
  refine ⟨i.image, i.toImage, i.imageι ≫ (projectiveSpaceOver n S ↘ S),
    isOpenImmersion_toImage i (.inl hqc), ⟨n, i.imageι, inferInstance, rfl⟩, ?_⟩
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact hif

/-- **An isomorphism of the base carries projective space over one to projective space over the
other.** Both are base changes of the integral model `ℙⁿ_ℤ` along the unique morphisms to the
terminal scheme, so the isomorphism is the one induced on the fibre products. -/
noncomputable def projectiveSpaceOverCongr (n : ℕ) {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    projectiveSpaceOver n Y ≅ projectiveSpaceOver n Z where
  hom := pullback.lift (pullback.fst _ _ ≫ e.hom) (pullback.snd _ _) (terminal.hom_ext _ _)
  inv := pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _) (terminal.hom_ext _ _)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- The identification of projective spaces over isomorphic bases intertwines their structure
morphisms with the isomorphism of the bases. -/
theorem projectiveSpaceOverCongr_hom_over (n : ℕ) {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (projectiveSpaceOverCongr n e).hom ≫ (projectiveSpaceOver n Z ↘ Z) =
      (projectiveSpaceOver n Y ↘ Y) ≫ e.hom :=
  pullback.lift_fst _ _ _

/-- **H-projectivity depends only on the isomorphism class of a morphism.** Given a commuting
square whose vertical sides are isomorphisms, a closed immersion into `ℙⁿ` over one base becomes
one over the other after composing with the inverse isomorphism of the sources and with the
identification of the two projective spaces. -/
theorem IsProjectiveMorphism.of_iso {Y Z Y' Z' : Scheme.{u}} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (e : Y ≅ Y') (b : Z ≅ Z') (w : e.hom ≫ g' = g ≫ b.hom) (hg : IsProjectiveMorphism g) :
    IsProjectiveMorphism g' := by
  obtain ⟨n, i, hi, hig⟩ := hg
  have := hi
  refine ⟨n, e.inv ≫ i ≫ (projectiveSpaceOverCongr n b).hom, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, projectiveSpaceOverCongr_hom_over, ← Category.assoc i,
    hig, ← w, Iso.inv_hom_id_assoc]

/-- **Stacks Project, Tag 01WB, the implication (2) ⟹ (1).** If the base is covered by opens
over each of which `f` is H-projective, then `f` is locally projective.

The opens are the ranges of the maps of the covering, which cover the base; over each of them
the base change of `f` is isomorphic, as an arrow, to the restriction of `f`, so the restriction
is H-projective, hence projective by the second clause of [Stacks, Tag 01W9]. -/
@[stacks 01WB "the implication from a local H-projective cover"]
theorem isLocallyProjective_of_isLocallyProjectiveMorphism (hf : IsLocallyProjectiveMorphism f) :
    IsLocallyProjective f := by
  obtain ⟨𝒰, h⟩ := hf
  refine ⟨𝒰.I₀, fun i => (𝒰.f i).opensRange, 𝒰.iSup_opensRange, fun i => ?_⟩
  have e := (morphismRestrictOpensRange f (𝒰.f i)).symm
  exact ((h i).of_iso (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
    (Arrow.w e.hom)).isProjective

end AlgebraicGeometry

end
