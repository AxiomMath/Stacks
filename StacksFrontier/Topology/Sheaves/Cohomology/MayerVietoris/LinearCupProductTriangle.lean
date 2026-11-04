module

public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearCupDataExists
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearCupProductFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearUnboundedTriangle

/-!
# The cup product as a map of Mayer--Vietoris triangles

Let `(X, 𝒪_X)` be a ringed space, let `A = Γ(X, 𝒪_X)`, and let `X = U ∪ V` be a union of two
open subsets.  For complexes `K` and `M` of `𝒪_X`-modules together with a choice of resolutions
`Stacks.Cohomology.LinearCupProductFamily.CupData` — a K-flat complex `T` of flat `A`-modules
representing `RΓ(X, K)`, a K-flat complex `𝒦` with flat terms resolving `K`, a K-injective
complex `ℐ` with injective terms resolving `M`, and a K-injective complex `𝒥` with injective
terms receiving `Tot(𝒦 ⊗_{𝒪_X} ℐ)` — this file produces a map of distinguished triangles in
`D(A)`

```
T ⊗^𝐋_A Γ(X, ℐ) ⟶ T ⊗^𝐋_A (Γ(U, ℐ) ⊕ Γ(V, ℐ)) ⟶ T ⊗^𝐋_A Γ(U ∩ V, ℐ) ⟶
Γ(X, 𝒥)         ⟶ Γ(U, 𝒥) ⊕ Γ(V, 𝒥)            ⟶ Γ(U ∩ V, 𝒥)        ⟶
```

whose three vertical maps are the `A`-linear cup products of
`Stacks.Cohomology.LinearCupProductFamily.CupData.cupMap`.  Both rows are the distinguished
triangles attached to short exact sequences of complexes of `A`-modules: the lower one is the
Mayer--Vietoris sequence of the sections of `𝒥`, and the upper one is that sequence for `ℐ`
tensored with `T`, which stays short exact because the terms of `T` are flat.

## Main definitions

* `Stacks.Cohomology.LinearCupProductTriangle.coverShortComplex` — the Mayer--Vietoris sequence
  `ℱ(X) ⟶ ℱ(U) ⊕ ℱ(V) ⟶ ℱ(U ∩ V)` of the `A`-linear sections of a complex of `𝒪_X`-modules.
* `Stacks.Cohomology.LinearCupProductTriangle.cupSource` and
  `Stacks.Cohomology.LinearCupProductTriangle.cupTarget` — the two Mayer--Vietoris sequences,
  with `Stacks.Cohomology.LinearCupProductTriangle.cupMiddle` the cup product on the middle term
  and `Stacks.Cohomology.LinearCupProductTriangle.cupShortComplexHom` the resulting morphism of
  short exact sequences.
* `Stacks.Cohomology.LinearCupProductTriangle.derivedCupMap` — the cup product
  `RΓ(X, K) ⊗^𝐋_A RΓ(W, M) ⟶ RΓ(W, K ⊗^𝐋_{𝒪_X} M)` in `D(A)`, read on the chosen
  representatives, and `Stacks.Cohomology.LinearCupProductTriangle.derivedCupMiddle` its value
  on the middle term.
* `Stacks.Cohomology.LinearCupProductTriangle.cupSourceTriangle`,
  `Stacks.Cohomology.LinearCupProductTriangle.cupTargetTriangle` — the two Mayer--Vietoris
  triangles, with `Stacks.Cohomology.LinearCupProductTriangle.cupBoundary` the connecting map of
  the first, and `Stacks.Cohomology.LinearCupProductTriangle.cupTriangleHom` the morphism
  between them.
* `Stacks.Cohomology.LinearCupProductTriangle.coverSectionsComplexIso` — the middle term of the
  Mayer--Vietoris sequence is the direct sum of the sections over `U` and the sections over `V`.
* `Stacks.Cohomology.LinearCupProductTriangle.sectionsIsoOfIsKInjective` — the termwise sections
  of a K-injective complex represent its derived sections; and
  `Stacks.Cohomology.LinearCupProductTriangle.tensorRepresentativeIso`,
  `Stacks.Cohomology.LinearCupProductTriangle.injSectionsIso`,
  `Stacks.Cohomology.LinearCupProductTriangle.tgtSectionsIso`, identifying the vertices of the
  two triangles with `RΓ(X, K)`, `RΓ(W, M)` and `RΓ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))`.

## Main results

* `Stacks.Cohomology.LinearCupProductTriangle.shortExact_map_tensorLeft` — a short exact
  sequence of complexes of `R`-modules stays short exact after tensoring with a complex of flat
  `R`-modules.
* `Stacks.Cohomology.LinearCupProductTriangle.shortExact_coverShortComplex` — the Mayer--Vietoris
  sequence of sections of a complex with injective terms is short exact.
* `Stacks.Cohomology.LinearCupProductTriangle.coverSectionsComplexIso_coverFirstComplex` and
  `Stacks.Cohomology.LinearCupProductTriangle.coverSectionsComplexIso_coverSecondComplex` — the
  two maps of the Mayer--Vietoris sequence are the pair of the restrictions to `U` and to `V`,
  and the difference of the restrictions to `U ∩ V`.
* `Stacks.Cohomology.LinearCupProductTriangle.cup_comm₁₂` and
  `Stacks.Cohomology.LinearCupProductTriangle.cup_comm₂₃` — the cup products commute with the
  restriction maps of the Mayer--Vietoris sequences.
* `Stacks.Cohomology.LinearCupProductTriangle.derivedCupMap_restriction` — the cup products at
  the various opens are compatible with restriction.
* `Stacks.Cohomology.LinearCupProductTriangle.linearCupProductMayerVietoris` — **Stacks 0G6X**:
  the two triangles are distinguished and the cup products form a morphism between them; and
  `Stacks.Cohomology.LinearCupProductTriangle.exists_cupData_linearCupProductMayerVietoris`,
  the same for arbitrary complexes, a choice of resolutions existing after `K` is replaced by a
  K-injective resolution.

## Implementation notes

The upper row is obtained by applying `Tot(T ⊗_A -)` to the Mayer--Vietoris sequence of the
sections of `ℐ`, rather than by applying the exact functor `RΓ(X, K) ⊗^𝐋_A -` to the
Mayer--Vietoris triangle of `M`: the connecting maps of both rows are then the connecting maps
attached to short exact sequences of complexes, so the third square — the only one with any
content — is the functoriality of "take the associated distinguished triangle".  The comparison
with the derived tensor product is `Tot(T ⊗_A -) = T ⊗^𝐋_A -`, which holds because `T` is
K-flat; this is where the first two vertices of the upper row acquire their names.  That the
vertices are the derived sections claimed for them is recorded separately, by
`tensorRepresentativeIso`, `injSectionsIso` and `tgtSectionsIso`; the remaining identification
`Tot(𝒦 ⊗_{𝒪_X} ℐ) = K ⊗^𝐋_{𝒪_X} M` is the one-sided K-flat comparison for sheaves of modules
and is not used here.

Short exactness of the tensored sequence is proved degreewise.  Only injectivity on the left
needs flatness of the terms of `T`; exactness in the middle and surjectivity on the right hold
for any complex, and are the already available
`KFlatTwoOutOfThree.tensor_exact_at` and `KFlatTwoOutOfThree.tensor_g_epi`.

The diagram chases are stated separately in an abstract category.  The complexes of
`𝒪_X`-modules carry two definitionally equal spellings of the structure sheaf of rings, one
through `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` and one through
`structureSheafRing`, and the two are not interchangeable below the default
transparency; `rw` and `simp` are therefore unavailable on goals mentioning both, while a
formal lemma applied in term mode is checked at default transparency and goes through.

## References

* [Stacks Project, Tag 0G6X](https://stacks.math.columbia.edu/tag/0G6X)
* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 014Z](https://stacks.math.columbia.edu/tag/014Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.LinearDerivedSections
open Stacks.Cohomology.LinearMayerVietoris
open Stacks.Cohomology.LinearCupProductFamily
open Stacks.SheafOfModules.Tensor (sheafTensor)
open KFlatTwoOutOfThree

universe u

namespace Stacks.Cohomology.LinearCupProductTriangle

/-! ### Tensoring a short exact sequence of complexes with a complex of flat modules -/

section Tensor

variable {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ)
  (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

/-- Tensoring a monomorphism of modules with a flat module gives a monomorphism. -/
theorem mono_whiskerLeft_of_flat (N : ModuleCat.{u} R) [Module.Flat R N]
    {Y Z : ModuleCat.{u} R} (f : Y ⟶ Z) [Mono f] : Mono (N ◁ f) := by
  rw [ModuleCat.MonoidalCategory.whiskerLeft_def, ModuleCat.mono_iff_injective]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := N) f.hom
    ((ModuleCat.mono_iff_injective _).1 ‹Mono f›)

/-- The injection of a short exact sequence of complexes stays a monomorphism in each degree
after tensoring with a complex of flat modules: the degree-`n` term of the total complex is the
direct sum of the monomorphisms `Lᵖ ⊗ S.fᵠ`. -/
theorem mono_tensorLeft_f (hse : S.ShortExact) (hflat : ∀ p : ℤ, Module.Flat R (L.X p)) (n : ℤ) :
    Mono ((L ◁ S.f).f n) := by
  have hm : ∀ b, Mono (whiskerFamily L S.f n b) := by
    rintro ⟨⟨p, q⟩, hpq⟩
    have := hflat p
    have : Mono (S.f.f q) :=
      (hse.map_of_exact (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q)).mono_f
    exact mono_whiskerLeft_of_flat (L.X p) (S.f.f q)
  exact cofanMap_mono (tensorObjCofan L.X S.X₁.X n) (tensorObjCofan L.X S.X₂.X n)
    (tensorObjCofanIsColimit L.X S.X₁.X n) (tensorObjCofanIsColimit L.X S.X₂.X n)
    ((L ◁ S.f).f n) (whiskerFamily L S.f n) inferInstance (inj_comp_whiskerLeft L S.f n)

/-- **A short exact sequence of complexes of `R`-modules stays short exact after tensoring with
a complex of flat `R`-modules.**  Exactness and surjectivity hold with no hypothesis on the
complex tensored with; injectivity on the left is where flatness of its terms enters. -/
theorem shortExact_map_tensorLeft (hse : S.ShortExact)
    (hflat : ∀ p : ℤ, Module.Flat R (L.X p)) :
    (S.map (TleftCochain L)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  have h₁ : Mono ((S.map (TleftCochain L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).f := by
    show Mono ((L ◁ S.f).f n)
    exact mono_tensorLeft_f L S hse hflat n
  have h₂ : Epi ((S.map (TleftCochain L)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).g := by
    show Epi ((L ◁ S.g).f n)
    exact tensor_g_epi L S hse n
  exact ShortComplex.ShortExact.mk (tensor_exact_at L S hse n)

end Tensor

/-! ### The Mayer--Vietoris sequence of sections of a complex -/

section Cover

variable (X : RingedSpace.{u, u}) (U V : Opens X.carrier)

/-- The sections over `W` of a complex of `𝒪_X`-modules, as a complex of `A`-modules for
`A = Γ(X, 𝒪_X)`. -/
abbrev sections (W : Opens X.carrier) (F : CochainComplex (Modules X) ℤ) :
    CochainComplex (ModuleCat.{u} (baseRing X)) ℤ :=
  ((openSections X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The sections of a complex of `𝒪_X`-modules over `U` and over `V` together, the middle term
of its Mayer--Vietoris sequence. -/
abbrev coverSectionsComplex (F : CochainComplex (Modules X) ℤ) :
    CochainComplex (ModuleCat.{u} (baseRing X)) ℤ :=
  ((coverSections X U V).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The first map `ℱ(X) ⟶ ℱ(U) ⊕ ℱ(V)` of the Mayer--Vietoris sequence of a complex. -/
abbrev coverFirstComplex (F : CochainComplex (Modules X) ℤ) :
    sections X ⊤ F ⟶ coverSectionsComplex X U V F :=
  (NatTrans.mapHomologicalComplex (coverFirst X U V) (ComplexShape.up ℤ)).app F

/-- The second map `ℱ(U) ⊕ ℱ(V) ⟶ ℱ(U ∩ V)` of the Mayer--Vietoris sequence of a complex. -/
abbrev coverSecondComplex (F : CochainComplex (Modules X) ℤ) :
    coverSectionsComplex X U V F ⟶ sections X (U ⊓ V) F :=
  (NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app F

/-- The two maps of the Mayer--Vietoris sequence of a complex compose to zero. -/
theorem coverFirstComplex_comp_coverSecondComplex (F : CochainComplex (Modules X) ℤ) :
    coverFirstComplex X U V F ≫ coverSecondComplex X U V F = 0 :=
  HomologicalComplex.hom_ext _ _ fun n =>
    NatTrans.congr_app (coverFirst_comp_coverSecond X U V) (F.X n)

/-- **The Mayer--Vietoris sequence of sections of a complex of `𝒪_X`-modules**, as a short
complex of complexes of `A`-modules. -/
abbrev coverShortComplex (F : CochainComplex (Modules X) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) :=
  ShortComplex.mk (coverFirstComplex X U V F) (coverSecondComplex X U V F)
    (coverFirstComplex_comp_coverSecondComplex X U V F)

/-- **The Mayer--Vietoris sequence of sections of a complex with injective terms is short
exact.**  Degreewise this is the short exactness at an injective sheaf of modules. -/
theorem shortExact_coverShortComplex (hUV : U ⊔ V = ⊤) (F : CochainComplex (Modules X) ℤ)
    (hF : ∀ n : ℤ, Injective (F.X n)) : (coverShortComplex X U V F).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  exact @shortExact_coverSections X U V hUV (F.X n) (hF n)

/-- The projection of the middle term of the Mayer--Vietoris sequence of a complex to the
sections over `U`. -/
abbrev coverFstComplex (F : CochainComplex (Modules X) ℤ) :
    coverSectionsComplex X U V F ⟶ sections X U F :=
  (NatTrans.mapHomologicalComplex (coverFst X U V) (ComplexShape.up ℤ)).app F

/-- The projection of the middle term of the Mayer--Vietoris sequence of a complex to the
sections over `V`. -/
abbrev coverSndComplex (F : CochainComplex (Modules X) ℤ) :
    coverSectionsComplex X U V F ⟶ sections X V F :=
  (NatTrans.mapHomologicalComplex (coverSnd X U V) (ComplexShape.up ℤ)).app F

/-- The inclusion of the sections over `U` into the middle term of the Mayer--Vietoris sequence
of a complex. -/
abbrev coverInlComplex (F : CochainComplex (Modules X) ℤ) :
    sections X U F ⟶ coverSectionsComplex X U V F :=
  (NatTrans.mapHomologicalComplex (coverInl X U V) (ComplexShape.up ℤ)).app F

/-- The inclusion of the sections over `V` into the middle term of the Mayer--Vietoris sequence
of a complex. -/
abbrev coverInrComplex (F : CochainComplex (Modules X) ℤ) :
    sections X V F ⟶ coverSectionsComplex X U V F :=
  (NatTrans.mapHomologicalComplex (coverInr X U V) (ComplexShape.up ℤ)).app F

/-- The inclusion of the summand of sections over `U` followed by the projection to it is the
identity. -/
theorem coverInlComplex_comp_coverFstComplex (F : CochainComplex (Modules X) ℤ) :
    coverInlComplex X U V F ≫ coverFstComplex X U V F = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_fst

/-- The inclusion of the summand of sections over `V` followed by the projection to the summand
of sections over `U` vanishes. -/
theorem coverInrComplex_comp_coverFstComplex (F : CochainComplex (Modules X) ℤ) :
    coverInrComplex X U V F ≫ coverFstComplex X U V F = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_fst

/-- The inclusion of the summand of sections over `U` followed by the projection to the summand
of sections over `V` vanishes. -/
theorem coverInlComplex_comp_coverSndComplex (F : CochainComplex (Modules X) ℤ) :
    coverInlComplex X U V F ≫ coverSndComplex X U V F = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_snd

/-- The inclusion of the summand of sections over `V` followed by the projection to it is the
identity. -/
theorem coverInrComplex_comp_coverSndComplex (F : CochainComplex (Modules X) ℤ) :
    coverInrComplex X U V F ≫ coverSndComplex X U V F = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_snd

/-- The two projections and the two inclusions exhibit the middle term of the Mayer--Vietoris
sequence of a complex as a direct sum. -/
theorem coverComplex_total (F : CochainComplex (Modules X) ℤ) :
    coverFstComplex X U V F ≫ coverInlComplex X U V F +
        coverSndComplex X U V F ≫ coverInrComplex X U V F = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.total

/-- **The middle term of the Mayer--Vietoris sequence of a complex is the direct sum of the
sections over `U` and the sections over `V`.** -/
def coverSectionsComplexIso (F : CochainComplex (Modules X) ℤ) :
    coverSectionsComplex X U V F ≅ sections X U F ⊞ sections X V F where
  hom := biprod.lift (coverFstComplex X U V F) (coverSndComplex X U V F)
  inv := biprod.desc (coverInlComplex X U V F) (coverInrComplex X U V F)
  hom_inv_id := by rw [biprod.lift_desc, coverComplex_total]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_desc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, coverInlComplex_comp_coverFstComplex,
          biprod.inl_fst]
      · rw [Category.assoc, biprod.lift_snd, coverInlComplex_comp_coverSndComplex,
          biprod.inl_snd]
    · rw [← Category.assoc, biprod.inr_desc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, coverInrComplex_comp_coverFstComplex,
          biprod.inr_fst]
      · rw [Category.assoc, biprod.lift_snd, coverInrComplex_comp_coverSndComplex,
          biprod.inr_snd]

variable {X}

/-- Restriction of sections of a complex of `𝒪_X`-modules to a smaller open. -/
abbrev restrictionComplex {Z W : Opens X.carrier} (h : Z ≤ W)
    (F : CochainComplex (Modules X) ℤ) : sections X W F ⟶ sections X Z F :=
  (NatTrans.mapHomologicalComplex (openRestriction h) (ComplexShape.up ℤ)).app F

variable (X)

/-- The direct sum decomposition of the middle term, as a pair of projections. -/
theorem coverSectionsComplexIso_hom (F : CochainComplex (Modules X) ℤ) :
    (coverSectionsComplexIso X U V F).hom =
      biprod.lift (coverFstComplex X U V F) (coverSndComplex X U V F) := rfl

/-- The direct sum decomposition of the middle term, as a pair of inclusions. -/
theorem coverSectionsComplexIso_inv (F : CochainComplex (Modules X) ℤ) :
    (coverSectionsComplexIso X U V F).inv =
      biprod.desc (coverInlComplex X U V F) (coverInrComplex X U V F) := rfl

/-- A map into the middle term of the Mayer--Vietoris sequence of a complex is determined by its
two components. -/
theorem coverSectionsComplex_hom_ext {F : CochainComplex (Modules X) ℤ}
    {C : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ}
    (a b : C ⟶ coverSectionsComplex X U V F)
    (h₁ : a ≫ coverFstComplex X U V F = b ≫ coverFstComplex X U V F)
    (h₂ : a ≫ coverSndComplex X U V F = b ≫ coverSndComplex X U V F) : a = b := by
  refine HomologicalComplex.hom_ext _ _ fun n => biprod.hom_ext _ _ ?_ ?_
  · exact congrArg (fun φ => HomologicalComplex.Hom.f φ n) h₁
  · exact congrArg (fun φ => HomologicalComplex.Hom.f φ n) h₂

/-- Composition of natural transformations is compatible with their action on complexes. -/
private theorem app_comp_app_mapHomologicalComplex {W₁ W₂ : Type*} [Category* W₁] [Category* W₂]
    [Preadditive W₁] [Preadditive W₂] {F G H : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms] {α : F ⟶ G} {β : G ⟶ H} {γ : F ⟶ H}
    (h : α ≫ β = γ) (K : CochainComplex W₁ ℤ) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex γ (ComplexShape.up ℤ)).app K := by
  rw [← h, NatTrans.mapHomologicalComplex_comp]
  rfl

/-- The first map of the Mayer--Vietoris sequence of a complex followed by the projection to the
sections over `U` is the restriction to `U`. -/
theorem coverFirstComplex_comp_coverFstComplex (F : CochainComplex (Modules X) ℤ) :
    coverFirstComplex X U V F ≫ coverFstComplex X U V F =
      restrictionComplex (le_top : U ≤ ⊤) F := by
  exact app_comp_app_mapHomologicalComplex (coverFirst_comp_coverFst X U V) F

/-- The first map of the Mayer--Vietoris sequence of a complex followed by the projection to the
sections over `V` is the restriction to `V`. -/
theorem coverFirstComplex_comp_coverSndComplex (F : CochainComplex (Modules X) ℤ) :
    coverFirstComplex X U V F ≫ coverSndComplex X U V F =
      restrictionComplex (le_top : V ≤ ⊤) F := by
  exact app_comp_app_mapHomologicalComplex (coverFirst_comp_coverSnd X U V) F

/-- On the summand of sections over `U`, the second map of the Mayer--Vietoris sequence of a
complex is the restriction to `U ∩ V`. -/
theorem coverInlComplex_comp_coverSecondComplex (F : CochainComplex (Modules X) ℤ) :
    coverInlComplex X U V F ≫ coverSecondComplex X U V F =
      restrictionComplex (inf_le_left : U ⊓ V ≤ U) F := by
  exact app_comp_app_mapHomologicalComplex (coverInl_comp_coverSecond X U V) F

/-- On the summand of sections over `V`, the second map of the Mayer--Vietoris sequence of a
complex is minus the restriction to `U ∩ V`. -/
theorem coverInrComplex_comp_coverSecondComplex (F : CochainComplex (Modules X) ℤ) :
    coverInrComplex X U V F ≫ coverSecondComplex X U V F =
      -restrictionComplex (inf_le_right : U ⊓ V ≤ V) F := by
  exact (app_comp_app_mapHomologicalComplex (coverInr_comp_coverSecond X U V) F).trans
    (HomologicalComplex.hom_ext _ _ fun _ => rfl)

/-- The first map of the Mayer--Vietoris sequence of a complex, written through the two
inclusions of the direct sum. -/
theorem coverFirstComplex_eq (F : CochainComplex (Modules X) ℤ) :
    coverFirstComplex X U V F =
      restrictionComplex (le_top : U ≤ ⊤) F ≫ coverInlComplex X U V F +
        restrictionComplex (le_top : V ≤ ⊤) F ≫ coverInrComplex X U V F := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact biprod.lift_eq

/-- The second map of the Mayer--Vietoris sequence of a complex, written through the two
projections of the direct sum. -/
theorem coverSecondComplex_eq (F : CochainComplex (Modules X) ℤ) :
    coverSecondComplex X U V F =
      coverFstComplex X U V F ≫ restrictionComplex (inf_le_left : U ⊓ V ≤ U) F -
        coverSndComplex X U V F ≫ restrictionComplex (inf_le_right : U ⊓ V ≤ V) F := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine biprod.desc_eq.trans ?_
  rw [Preadditive.comp_neg, ← sub_eq_add_neg]
  rfl

/-- **The first map of the Mayer--Vietoris sequence of a complex is the pair of the restrictions
to `U` and to `V`.** -/
theorem coverSectionsComplexIso_coverFirstComplex (F : CochainComplex (Modules X) ℤ) :
    coverFirstComplex X U V F ≫ (coverSectionsComplexIso X U V F).hom =
      biprod.lift (restrictionComplex (le_top : U ≤ ⊤) F)
        (restrictionComplex (le_top : V ≤ ⊤) F) := by
  rw [coverSectionsComplexIso_hom]
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst,
      coverFirstComplex_comp_coverFstComplex]
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd,
      coverFirstComplex_comp_coverSndComplex]

/-- **The second map of the Mayer--Vietoris sequence of a complex is the difference of the
restrictions to `U ∩ V`.** -/
theorem coverSectionsComplexIso_coverSecondComplex (F : CochainComplex (Modules X) ℤ) :
    (coverSectionsComplexIso X U V F).inv ≫ coverSecondComplex X U V F =
      biprod.desc (restrictionComplex (inf_le_left : U ⊓ V ≤ U) F)
        (-restrictionComplex (inf_le_right : U ⊓ V ≤ V) F) := by
  rw [coverSectionsComplexIso_inv]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, biprod.inl_desc, biprod.inl_desc,
      coverInlComplex_comp_coverSecondComplex]
  · rw [← Category.assoc, biprod.inr_desc, biprod.inr_desc,
      coverInrComplex_comp_coverSecondComplex]

end Cover

/-! ### Formal diagram chases -/

section Formal

variable {C : Type*} [Category* C] [Preadditive C]

/-- A map built from two splittings, read on the first component. -/
theorem add_comp_fst {P A A' B B' S : C} (p : P ⟶ A) (cU : A ⟶ A') (i : A' ⟶ S)
    (p' : P ⟶ B) (cV : B ⟶ B') (j : B' ⟶ S) (π : S ⟶ A') (hi : i ≫ π = 𝟙 A')
    (hj : j ≫ π = 0) : (p ≫ cU ≫ i + p' ≫ cV ≫ j) ≫ π = p ≫ cU := by
  simp only [Preadditive.add_comp, Category.assoc, hi, hj, comp_zero, Category.comp_id, add_zero]

/-- A map built from two splittings, read on the second component. -/
theorem add_comp_snd {P A A' B B' S : C} (p : P ⟶ A) (cU : A ⟶ A') (i : A' ⟶ S)
    (p' : P ⟶ B) (cV : B ⟶ B') (j : B' ⟶ S) (π : S ⟶ B') (hi : i ≫ π = 0)
    (hj : j ≫ π = 𝟙 B') : (p ≫ cU ≫ i + p' ≫ cV ≫ j) ≫ π = p' ≫ cV := by
  simp only [Preadditive.add_comp, Category.assoc, hi, hj, comp_zero, Category.comp_id, zero_add]

omit [Preadditive C] in
/-- The chase closing a commuting square one component of a direct sum at a time. -/
theorem squareChase {P Q S A B T : C} (a : P ⟶ Q) (m : Q ⟶ S) (π : S ⟶ A) (p : Q ⟶ B)
    (cU : B ⟶ A) (b : P ⟶ B) (c : P ⟶ T) (f : T ⟶ S) (r : T ⟶ A) (h₁ : m ≫ π = p ≫ cU)
    (h₂ : f ≫ π = r) (h₃ : a ≫ p = b) (h₄ : b ≫ cU = c ≫ r) :
    (a ≫ m) ≫ π = (c ≫ f) ≫ π := by
  rw [Category.assoc, h₁, ← Category.assoc, h₃, h₄, Category.assoc, h₂]

/-- The chase closing the commuting square whose target is a difference of two restrictions. -/
theorem diffChase {P A B Z W A' B' S : C} (g : P ⟶ Z) (cI : Z ⟶ W) (p : P ⟶ A)
    (q₁ : A ⟶ Z) (p' : P ⟶ B) (q₂ : B ⟶ Z) (cU : A ⟶ A') (i : A' ⟶ S) (cV : B ⟶ B')
    (j : B' ⟶ S) (g' : S ⟶ W) (s₁ : A' ⟶ W) (s₂ : B' ⟶ W) (hg : g = p ≫ q₁ - p' ≫ q₂)
    (h₁ : q₁ ≫ cI = cU ≫ s₁) (h₂ : q₂ ≫ cI = cV ≫ s₂) (hi : i ≫ g' = s₁)
    (hj : j ≫ g' = -s₂) : g ≫ cI = (p ≫ cU ≫ i + p' ≫ cV ≫ j) ≫ g' := by
  rw [hg, Preadditive.sub_comp, Category.assoc, Category.assoc, h₁, h₂, Preadditive.add_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, hi, hj]
  simp [Preadditive.comp_neg, sub_eq_add_neg]

omit [Preadditive C] in
/-- Transporting a commuting square across two isomorphisms. -/
theorem isoRearrange {A A' B B' : C} (e : A ≅ A') (e' : B ≅ B') (f : A' ⟶ B')
    (f' : A ⟶ B) (h : f' ≫ e'.hom = e.hom ≫ f) : f ≫ e'.inv = e.inv ≫ f' := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [Preadditive C] in
/-- Cancelling an inverse pair at the head of a composite. -/
theorem inv_hom_comp_cancel {A B Z : C} (e : A ≅ B) (x : B ⟶ Z) :
    x = e.inv ≫ e.hom ≫ x := by
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

omit [Preadditive C] in
/-- The chase pasting two commuting squares along a composite. -/
theorem compChase {P Q R S T W : C} (x : P ⟶ Q) (y : Q ⟶ R) (z : R ⟶ S) (a : P ⟶ T)
    (u : T ⟶ R) (b : T ⟶ W) (v : W ⟶ S) (h₁ : x ≫ y = a ≫ u) (h₂ : u ≫ z = b ≫ v) :
    x ≫ y ≫ z = a ≫ b ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

variable {D : Type*} [Category* D] [Preadditive D]

/-- An additive functor carries a difference of two composites to the difference of the
composites of the images. -/
theorem map_sub_comp (F : C ⥤ D) [F.Additive] {P A B Z : C} (g : P ⟶ Z) (p : P ⟶ A)
    (q₁ : A ⟶ Z) (p' : P ⟶ B) (q₂ : B ⟶ Z) (h : g = p ≫ q₁ - p' ≫ q₂) :
    F.map g = F.map p ≫ F.map q₁ - F.map p' ≫ F.map q₂ := by
  rw [h, F.map_sub, F.map_comp, F.map_comp]

end Formal

/-! ### The cup product as a morphism of Mayer--Vietoris sequences -/

section Cup

variable {X : RingedSpace.{u, u}} (U V : Opens X.carrier)
  {K M : CochainComplex (Modules X) ℤ} (d : CupData X K M)

/-- **The Mayer--Vietoris sequence of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)`**, as the short exact sequence
of complexes of `A`-modules obtained by tensoring the Mayer--Vietoris sequence of the sections
of `ℐ` with the complex `T`. -/
abbrev cupSource : ShortComplex (CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) :=
  (coverShortComplex X U V d.inj).map (TleftCochain d.T)

/-- **The Mayer--Vietoris sequence of `RΓ(-, K ⊗^𝐋_{𝒪_X} M)`**, as the short exact sequence of
complexes of `A`-modules of the sections of `𝒥`. -/
abbrev cupTarget : ShortComplex (CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) :=
  coverShortComplex X U V d.tgt

/-- The tensored Mayer--Vietoris sequence is short exact: the terms of `T` are flat. -/
theorem shortExact_cupSource (hUV : U ⊔ V = ⊤) : (cupSource U V d).ShortExact :=
  shortExact_map_tensorLeft d.T _
    (shortExact_coverShortComplex X U V hUV d.inj d.inj_injective) d.T_flat

/-- The Mayer--Vietoris sequence of the sections of `𝒥` is short exact: its terms are
injective. -/
theorem shortExact_cupTarget (hUV : U ⊔ V = ⊤) : (cupTarget U V d).ShortExact :=
  shortExact_coverShortComplex X U V hUV d.tgt d.tgt_injective

/-- **The cup product on the middle term of the Mayer--Vietoris sequence**, the cup products
over `U` and over `V` read on the two summands. -/
def cupMiddle : (TleftCochain d.T).obj (coverSectionsComplex X U V d.inj) ⟶
    coverSectionsComplex X U V d.tgt :=
  (TleftCochain d.T).map (coverFstComplex X U V d.inj) ≫ d.cupMap U ≫
      coverInlComplex X U V d.tgt +
    (TleftCochain d.T).map (coverSndComplex X U V d.inj) ≫ d.cupMap V ≫
      coverInrComplex X U V d.tgt

/-- On the summand of sections over `U`, the cup product on the middle term is the cup product
over `U`. -/
theorem cupMiddle_comp_coverFstComplex :
    cupMiddle U V d ≫ coverFstComplex X U V d.tgt =
      (TleftCochain d.T).map (coverFstComplex X U V d.inj) ≫ d.cupMap U :=
  add_comp_fst _ _ _ _ _ _ _ (coverInlComplex_comp_coverFstComplex X U V d.tgt)
    (coverInrComplex_comp_coverFstComplex X U V d.tgt)

/-- On the summand of sections over `V`, the cup product on the middle term is the cup product
over `V`. -/
theorem cupMiddle_comp_coverSndComplex :
    cupMiddle U V d ≫ coverSndComplex X U V d.tgt =
      (TleftCochain d.T).map (coverSndComplex X U V d.inj) ≫ d.cupMap V :=
  add_comp_snd _ _ _ _ _ _ _ (coverInlComplex_comp_coverSndComplex X U V d.tgt)
    (coverInrComplex_comp_coverSndComplex X U V d.tgt)

/-- **The first square of the cup product diagram commutes**: the cup product is compatible
with the restriction maps from `X` to `U` and to `V`. -/
theorem cup_comm₁₂ :
    (cupSource U V d).f ≫ cupMiddle U V d = d.cupMap ⊤ ≫ (cupTarget U V d).f :=
  coverSectionsComplex_hom_ext X U V _ _
    (squareChase _ _ _ _ _ _ _ _ _ (cupMiddle_comp_coverFstComplex U V d)
      (coverFirstComplex_comp_coverFstComplex X U V d.tgt)
      (((TleftCochain d.T).map_comp _ _).symm.trans (congrArg (TleftCochain d.T).map
        (coverFirstComplex_comp_coverFstComplex X U V d.inj)))
      (d.cupMap_restriction (le_top : U ≤ ⊤)).symm)
    (squareChase _ _ _ _ _ _ _ _ _ (cupMiddle_comp_coverSndComplex U V d)
      (coverFirstComplex_comp_coverSndComplex X U V d.tgt)
      (((TleftCochain d.T).map_comp _ _).symm.trans (congrArg (TleftCochain d.T).map
        (coverFirstComplex_comp_coverSndComplex X U V d.inj)))
      (d.cupMap_restriction (le_top : V ≤ ⊤)).symm)

/-- **The second square of the cup product diagram commutes**: the cup product is compatible
with the restriction maps from `U` and from `V` to `U ∩ V`. -/
theorem cup_comm₂₃ :
    (cupSource U V d).g ≫ d.cupMap (U ⊓ V) = cupMiddle U V d ≫ (cupTarget U V d).g :=
  diffChase _ _ _ _ _ _ _ _ _ _ _ _ _
    (map_sub_comp (TleftCochain d.T) _ _ _ _ _ (coverSecondComplex_eq X U V d.inj))
    (d.cupMap_restriction (inf_le_left : U ⊓ V ≤ U)).symm
    (d.cupMap_restriction (inf_le_right : U ⊓ V ≤ V)).symm
    (coverInlComplex_comp_coverSecondComplex X U V d.tgt)
    (coverInrComplex_comp_coverSecondComplex X U V d.tgt)

/-- **The cup product is a morphism of Mayer--Vietoris sequences of complexes of `A`-modules**,
from the sequence of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)` to the sequence of
`RΓ(-, K ⊗^𝐋_{𝒪_X} M)`. -/
def cupShortComplexHom : cupSource U V d ⟶ cupTarget U V d where
  τ₁ := d.cupMap ⊤
  τ₂ := cupMiddle U V d
  τ₃ := d.cupMap (U ⊓ V)
  comm₁₂ := (cup_comm₁₂ U V d).symm
  comm₂₃ := (cup_comm₂₃ U V d).symm

end Cup

/-! ### The map of Mayer--Vietoris triangles -/

section Triangle

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U V : Opens X.carrier)
  {K M : CochainComplex (Modules X) ℤ} (d : CupData X K M)

/-- **`RΓ(X, K) ⊗^𝐋_A -` read on the chosen representative `T` of `RΓ(X, K)`**, the exact
functor `D(A) ⥤ D(A)` applied to the Mayer--Vietoris triangle of `M`. -/
abbrev tensorRepresentative :
    DerivedCategory (ModuleCat.{u} (baseRing X)) ⥤ DerivedCategory (ModuleCat.{u} (baseRing X)) :=
  (CochainComplex.DerivedTensor.OneSided.tensorBifunctor (baseRing X)).obj
    (DerivedCategory.Q.obj d.T)

/-- The comparison identifying `T ⊗^𝐋_A Γ(W, ℐ)` with the total complex `Tot(T ⊗_A Γ(W, ℐ))`:
the complex `T` is K-flat. -/
abbrev cupComparison (W : Opens X.carrier) :
    (tensorRepresentative d).obj (DerivedCategory.Q.obj (sections X W d.inj)) ≅
      DerivedCategory.Q.obj ((TleftCochain d.T).obj (sections X W d.inj)) :=
  CochainComplex.DerivedTensor.OneSided.comparisonLeft d.T (sections X W d.inj) d.T_kFlat

/-- The comparison identifying `T ⊗^𝐋_A (Γ(U, ℐ) ⊕ Γ(V, ℐ))` with the total complex. -/
abbrev cupComparisonMiddle :
    (tensorRepresentative d).obj (DerivedCategory.Q.obj (coverSectionsComplex X U V d.inj)) ≅
      DerivedCategory.Q.obj ((TleftCochain d.T).obj (coverSectionsComplex X U V d.inj)) :=
  CochainComplex.DerivedTensor.OneSided.comparisonLeft d.T
    (coverSectionsComplex X U V d.inj) d.T_kFlat

/-- **The `A`-linear cup product**
`RΓ(X, K) ⊗^𝐋_A RΓ(W, M) ⟶ RΓ(W, K ⊗^𝐋_{𝒪_X} M)`, read on the chosen representatives. -/
def derivedCupMap (W : Opens X.carrier) :
    (tensorRepresentative d).obj (DerivedCategory.Q.obj (sections X W d.inj)) ⟶
      DerivedCategory.Q.obj (sections X W d.tgt) :=
  (cupComparison d W).hom ≫ DerivedCategory.Q.map (d.cupMap W)

/-- **The cup products at the various opens are compatible with restriction.**  One choice of
resolutions gives the map `RΓ(X, K) ⊗^𝐋_A RΓ(W, M) ⟶ RΓ(W, K ⊗^𝐋_{𝒪_X} M)` for every open `W`
at once, compatibly with the restriction maps of an inclusion `Z ⊆ W`. -/
theorem derivedCupMap_restriction {Z W : Opens X.carrier} (h : Z ≤ W) :
    (tensorRepresentative d).map
          (DerivedCategory.Q.map (restrictionComplex h d.inj)) ≫ derivedCupMap d Z =
      derivedCupMap d W ≫ DerivedCategory.Q.map (restrictionComplex h d.tgt) :=
  (compChase _ _ _ _ _ _ _
    (CochainComplex.DerivedTensor.OneSided.comparisonLeft_naturality_right d.T
      (restrictionComplex h d.inj) d.T_kFlat)
    (((DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map (d.cupMap_restriction h).symm)).trans
        (DerivedCategory.Q.map_comp _ _))).trans (Category.assoc _ _ _).symm

/-- The cup product on the middle term of the Mayer--Vietoris triangle. -/
def derivedCupMiddle :
    (tensorRepresentative d).obj (DerivedCategory.Q.obj (coverSectionsComplex X U V d.inj)) ⟶
      DerivedCategory.Q.obj (coverSectionsComplex X U V d.tgt) :=
  (cupComparisonMiddle U V d).hom ≫ DerivedCategory.Q.map (cupMiddle U V d)

/-- **The Mayer--Vietoris triangle of `RΓ(-, K ⊗^𝐋_{𝒪_X} M)`**, the distinguished triangle in
`D(A)` attached to the short exact sequence of the sections of `𝒥`. -/
abbrev cupTargetTriangle (hUV : U ⊔ V = ⊤) :
    Triangle (DerivedCategory (ModuleCat.{u} (baseRing X))) :=
  DerivedCategory.triangleOfSES (shortExact_cupTarget U V d hUV)

/-- The connecting map of the Mayer--Vietoris triangle of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)`, read
through the comparison with the total complexes. -/
def cupBoundary (hUV : U ⊔ V = ⊤) :
    (tensorRepresentative d).obj (DerivedCategory.Q.obj (sections X (U ⊓ V) d.inj)) ⟶
      ((tensorRepresentative d).obj (DerivedCategory.Q.obj (sections X ⊤ d.inj)))⟦(1 : ℤ)⟧ :=
  (cupComparison d (U ⊓ V)).hom ≫
    DerivedCategory.triangleOfSESδ (shortExact_cupSource U V d hUV) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)).map
        (cupComparison d ⊤).inv

/-- **The Mayer--Vietoris triangle of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)`**: the exact functor
`RΓ(X, K) ⊗^𝐋_A -` applied to the Mayer--Vietoris triangle of `M`, read on the chosen
representatives. -/
abbrev cupSourceTriangle (hUV : U ⊔ V = ⊤) :
    Triangle (DerivedCategory (ModuleCat.{u} (baseRing X))) :=
  Triangle.mk
    ((tensorRepresentative d).map (DerivedCategory.Q.map (coverFirstComplex X U V d.inj)))
    ((tensorRepresentative d).map (DerivedCategory.Q.map (coverSecondComplex X U V d.inj)))
    (cupBoundary U V d hUV)

/-- The comparison with the total complexes, as an isomorphism of triangles. -/
def cupTriangleIso (hUV : U ⊔ V = ⊤) :
    DerivedCategory.triangleOfSES (shortExact_cupSource U V d hUV) ≅
      cupSourceTriangle U V d hUV :=
  Triangle.isoMk _ _ (cupComparison d ⊤).symm (cupComparisonMiddle U V d).symm
    (cupComparison d (U ⊓ V)).symm
    (isoRearrange _ _ _ _
      (CochainComplex.DerivedTensor.OneSided.comparisonLeft_naturality_right d.T
        (coverFirstComplex X U V d.inj) d.T_kFlat))
    (isoRearrange _ _ _ _
      (CochainComplex.DerivedTensor.OneSided.comparisonLeft_naturality_right d.T
        (coverSecondComplex X U V d.inj) d.T_kFlat))
    (inv_hom_comp_cancel (cupComparison d (U ⊓ V)) _)

/-- **The cup product is a morphism of distinguished triangles.** -/
def cupTriangleHom (hUV : U ⊔ V = ⊤) :
    cupSourceTriangle U V d hUV ⟶ cupTargetTriangle U V d hUV :=
  (cupTriangleIso U V d hUV).inv ≫
    DerivedCategory.triangleOfSES.map (shortExact_cupSource U V d hUV)
      (shortExact_cupTarget U V d hUV) (cupShortComplexHom U V d)

/-- The first component of the morphism of triangles is the cup product over `X`. -/
theorem cupTriangleHom_hom₁ (hUV : U ⊔ V = ⊤) :
    (cupTriangleHom U V d hUV).hom₁ = derivedCupMap d ⊤ := rfl

/-- The middle component of the morphism of triangles is the cup product on the middle term. -/
theorem cupTriangleHom_hom₂ (hUV : U ⊔ V = ⊤) :
    (cupTriangleHom U V d hUV).hom₂ = derivedCupMiddle U V d := rfl

/-- The third component of the morphism of triangles is the cup product over `U ∩ V`. -/
theorem cupTriangleHom_hom₃ (hUV : U ⊔ V = ⊤) :
    (cupTriangleHom U V d hUV).hom₃ = derivedCupMap d (U ⊓ V) := rfl

/-- The Mayer--Vietoris triangle of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)` is distinguished. -/
theorem cupSourceTriangle_distinguished (hUV : U ⊔ V = ⊤) :
    cupSourceTriangle U V d hUV ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) :=
  isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (shortExact_cupSource U V d hUV)) _
    (cupTriangleIso U V d hUV).symm

/-- The Mayer--Vietoris triangle of `RΓ(-, K ⊗^𝐋_{𝒪_X} M)` is distinguished. -/
theorem cupTargetTriangle_distinguished (hUV : U ⊔ V = ⊤) :
    cupTargetTriangle U V d hUV ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) :=
  DerivedCategory.triangleOfSES_distinguished (shortExact_cupTarget U V d hUV)

/-- **Stacks 0G6X.**  Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)`, and let
`X = U ∪ V` be a union of two open subsets.  For a choice of resolutions of two complexes `K`
and `M` of `𝒪_X`-modules there is a map of distinguished triangles in `D(A)` from the
Mayer--Vietoris triangle of `RΓ(X, K) ⊗^𝐋_A RΓ(-, M)` to the Mayer--Vietoris triangle of
`RΓ(-, K ⊗^𝐋_{𝒪_X} M)` whose three vertical maps are the cup products over `X`, over `U` and
`V`, and over `U ∩ V`. -/
@[stacks 0G6X "the map of triangles, with the vertices read on the chosen representatives"]
theorem linearCupProductMayerVietoris (hUV : U ⊔ V = ⊤) :
    cupSourceTriangle U V d hUV ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) ∧
      cupTargetTriangle U V d hUV ∈
          distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) ∧
        (tensorRepresentative d).map
              (DerivedCategory.Q.map (coverFirstComplex X U V d.inj)) ≫
            derivedCupMiddle U V d =
          derivedCupMap d ⊤ ≫ DerivedCategory.Q.map (coverFirstComplex X U V d.tgt) ∧
        (tensorRepresentative d).map
              (DerivedCategory.Q.map (coverSecondComplex X U V d.inj)) ≫
            derivedCupMap d (U ⊓ V) =
          derivedCupMiddle U V d ≫ DerivedCategory.Q.map (coverSecondComplex X U V d.tgt) ∧
        cupBoundary U V d hUV ≫
            (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)).map
              (derivedCupMap d ⊤) =
          derivedCupMap d (U ⊓ V) ≫
            DerivedCategory.triangleOfSESδ (shortExact_cupTarget U V d hUV) :=
  ⟨cupSourceTriangle_distinguished U V d hUV, cupTargetTriangle_distinguished U V d hUV,
    (cupTriangleHom U V d hUV).comm₁, (cupTriangleHom U V d hUV).comm₂,
    (cupTriangleHom U V d hUV).comm₃⟩

/-- **Stacks 0G6X for arbitrary complexes.**  Every complex `K` of `𝒪_X`-modules admits a
quasi-isomorphism into a complex carrying a choice of resolutions, so that the map of
Mayer--Vietoris triangles above exists for every object of `D(𝒪_X)`. -/
@[stacks 0G6X "for arbitrary complexes, after replacing K by a K-injective resolution"]
theorem exists_cupData_linearCupProductMayerVietoris (hUV : U ⊔ V = ⊤)
    (K M : CochainComplex (Modules X) ℤ) :
    ∃ (K' : CochainComplex (Modules X) ℤ) (e : K ⟶ K') (d : CupData X K' M), QuasiIso e ∧
      cupSourceTriangle U V d hUV ∈
          distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) ∧
        cupTargetTriangle U V d hUV ∈
            distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) ∧
          (tensorRepresentative d).map
                (DerivedCategory.Q.map (coverFirstComplex X U V d.inj)) ≫
              derivedCupMiddle U V d =
            derivedCupMap d ⊤ ≫ DerivedCategory.Q.map (coverFirstComplex X U V d.tgt) ∧
          (tensorRepresentative d).map
                (DerivedCategory.Q.map (coverSecondComplex X U V d.inj)) ≫
              derivedCupMap d (U ⊓ V) =
            derivedCupMiddle U V d ≫ DerivedCategory.Q.map (coverSecondComplex X U V d.tgt) ∧
          cupBoundary U V d hUV ≫
              (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)).map
                (derivedCupMap d ⊤) =
            derivedCupMap d (U ⊓ V) ≫
              DerivedCategory.triangleOfSESδ (shortExact_cupTarget U V d hUV) := by
  obtain ⟨K', e, he, ⟨d⟩⟩ := exists_cupData X K M
  exact ⟨K', e, d, he, linearCupProductMayerVietoris U V d hUV⟩

/-! ### The vertices of the two triangles -/

/-- **The termwise sections of a K-injective complex compute the derived sections.**  The
comparison map of the right derived functor `RΓ(W, -)` is invertible at a K-injective
complex. -/
theorem isIso_derivedLinearSectionsUnit_app (W : Opens X.carrier)
    (I : CochainComplex (Modules X) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedLinearSectionsUnit X W).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (homotopyLinearSections X W)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)).2
      DerivedCategory.Qh (derivedLinearSections X W) (derivedLinearSectionsUnit X W) I hI

/-- **The sections over `W` of a K-injective complex represent its derived sections over
`W`.** -/
def sectionsIsoOfIsKInjective (W : Opens X.carrier) (I : CochainComplex (Modules X) ℤ)
    (hI : I.IsKInjective) :
    DerivedCategory.Q.obj (sections X W I) ≅
      (derivedLinearSections X W).obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} (baseRing X))).app (sections X W I)).symm ≪≫
    @asIso _ _ _ _ _ (isIso_derivedLinearSectionsUnit_app W I hI) ≪≫
    (derivedLinearSections X W).mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app I)

/-- **`ℐ` represents `M` in `D(𝒪_X)`.** -/
theorem isIso_Q_map_injRes : IsIso (DerivedCategory.Q.map d.injRes) := 
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 d.injRes_quasiIso

/-- **`𝒥` represents `Tot(𝒦 ⊗_{𝒪_X} ℐ)` in `D(𝒪_X)`.** -/
theorem isIso_Q_map_toTgt : IsIso (DerivedCategory.Q.map d.toTgt) := 
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 d.toTgt_quasiIso

/-- **`𝒦` represents `K` in `D(𝒪_X)`.** -/
theorem isIso_Q_map_cplxRes : IsIso (DerivedCategory.Q.map d.cplxRes) := 
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 d.cplxRes_quasiIso

/-- **`ℰ` represents `𝒦` in `D(𝒪_X)`.** -/
theorem isIso_Q_map_cplxToKinj : IsIso (DerivedCategory.Q.map d.cplxToKinj) := 
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 d.cplxToKinj_quasiIso

/-- **`T` represents the derived global sections `RΓ(X, K)`.**  This is the defining property
of the complex `T` of the chosen resolutions. -/
theorem isIso_Q_map_toSections :
    IsIso (DerivedCategory.Q.map (d.toSections ≫
      ((openSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map d.cplxToKinj)) := 
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 d.toSections_quasiIso

/-- **`T` represents `RΓ(X, K)`**, as an isomorphism of `D(A)`: the chosen map
`T ⟶ Γ(X, 𝒦)` becomes an isomorphism onto the derived global sections of `K` after the
K-injective resolution of `𝒦`. -/
def tensorRepresentativeIso :
    DerivedCategory.Q.obj d.T ≅
      (derivedLinearSections X ⊤).obj (DerivedCategory.Q.obj K) :=
  @asIso _ _ _ _ _ (isIso_Q_map_toSections d) ≪≫
    sectionsIsoOfIsKInjective ⊤ d.kinj d.kinj_kInjective ≪≫
    (derivedLinearSections X ⊤).mapIso
      (@asIso _ _ _ _ _ (isIso_Q_map_cplxToKinj d)).symm ≪≫
    (derivedLinearSections X ⊤).mapIso (@asIso _ _ _ _ _ (isIso_Q_map_cplxRes d))

/-- **The sections of `ℐ` over `W` represent `RΓ(W, M)`.** -/
def injSectionsIso (W : Opens X.carrier) :
    DerivedCategory.Q.obj (sections X W d.inj) ≅
      (derivedLinearSections X W).obj (DerivedCategory.Q.obj M) :=
  sectionsIsoOfIsKInjective W d.inj d.inj_kInjective ≪≫
    (derivedLinearSections X W).mapIso (@asIso _ _ _ _ _ (isIso_Q_map_injRes d)).symm

/-- **The sections of `𝒥` over `W` represent `RΓ(W, Tot(𝒦 ⊗_{𝒪_X} ℐ))`**, the derived
sections of the derived tensor product of `K` and `M`. -/
def tgtSectionsIso (W : Opens X.carrier) :
    DerivedCategory.Q.obj (sections X W d.tgt) ≅
      (derivedLinearSections X W).obj (DerivedCategory.Q.obj
        (HomologicalComplex.mapBifunctor d.cplx d.inj (sheafTensor X.sheaf)
          (ComplexShape.up ℤ))) :=
  sectionsIsoOfIsKInjective W d.tgt d.tgt_kInjective ≪≫
    (derivedLinearSections X W).mapIso (@asIso _ _ _ _ _ (isIso_Q_map_toTgt d)).symm

end Triangle

end Stacks.Cohomology.LinearCupProductTriangle

end
