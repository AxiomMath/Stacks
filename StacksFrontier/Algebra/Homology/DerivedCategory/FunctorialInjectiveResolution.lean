module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ResolutionFunctor
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# Functorial injective embeddings give a resolution functor

Let `C` be an abelian category with *functorial injective embeddings*: a functor
`J : C ⥤ ℐ` into the full subcategory `ℐ` of injective objects together with a natural
transformation `η : 𝟭 C ⟶ J` whose components are monomorphisms
([Stacks, Tag 0139]). Then the construction of an injective resolution of a bounded below
complex can be carried out functorially, *on the nose* and not just up to homotopy:
there is a functor `F : Comp⁺(C) ⥤ Comp⁺(ℐ)` and a natural transformation
`α : 𝟭 ⟶ F ⋙ ι` all of whose components `α_K : K ⟶ F K` are quasi-isomorphisms — one
takes `F K = Tot(I^{•,•})` for the double complex `I^{p, 0} = J(Kᵖ)`,
`I^{p, q + 1} = J(Coker(I^{p, q - 1} → I^{p, q}))` ([Stacks, Tag 0133]). Passing to
homotopy categories, such data yields a resolution functor for `C` in the sense of
[Stacks, Tag 013W]; this second half needs no hypothesis on `C` beyond abelianness, and
is what makes resolution functors available for "big" abelian categories such as
`Mod(𝒪_X)`, where the choice-based construction of [Stacks, Tag 013X] does not apply
([Stacks, Tag 0142]).

## Main results

* `CochainComplex.Plus.exists_functorial_injective_resolution_and_exists_resolutionFunctor`:
  the two assertions of [Stacks, Tag 0141] — the functorial injective resolution of bounded
  below complexes, and that such data yields a resolution functor.

## Implementation notes

The source phrases both parts through the category `InjRes(C)` of quasi-isomorphisms
`K ⟶ I` from a bounded below complex to a bounded below complex of injectives, and the
functor `s : InjRes(C) → Comp⁺(C)` remembering the source: `inj` is a functor
`Comp⁺(C) ⥤ InjRes(C)` with `s ∘ inj = id`. Such an `inj` is precisely a pair `(F, α)`
with `F : Comp⁺(C) ⥤ Comp⁺(ℐ)` a functor, `α : 𝟭 ⟶ F ⋙ ι` a natural transformation
(the equality `s ∘ inj = id` is the identity functor appearing as the source of `α`, on
the nose) and every `α_K` a quasi-isomorphism; the second component of `inj` is
`t ∘ inj = F`. The intermediate category `InjRes(C)` is therefore not introduced: it has
nothing to say beyond this equivalence of data, and a `Comma`-style construction would
have to be unfolded at every use. Likewise the hypothesis [Stacks, Tag 0139] is spelled
as the data `(J, η)` rather than as a functor `C ⥤ Arrow C` over `𝟭 C`, and injectivity
of `J A` comes from the codomain `ℐ = InjectiveObject C` rather than from a side
condition, as in [Stacks, Tag 013W].

The functorial injective embedding `(J, η)` is quantified over *inside* the first conjunct,
not in the ambient signature, because the second assertion holds for an arbitrary abelian
category: `(J, η)` is what produces a pair `(F, α)`, and plays no part in turning one into
a resolution functor. Sharing it would make the second assertion inapplicable to an
`(F, α)` built by hand over a category not known to have functorial injective embeddings,
which is the situation [Stacks, Tag 0142] is about; as stated, the second conjunct needs no
hypothesis on `C` beyond `Abelian C`, and neither conjunct implies the other.

The second conjunct pins down the resolution functor it produces: `R` is the image of
`(F, α)` under `Comp⁺ ⥤ K⁺`, which is the content of the source's "write
`inj(K) = (i_K : K → j(K))`; this provides a resolution functor". Since
`HomotopyCategory.Plus.quotient C` is bijective on objects, that pins `R` completely, and
[Stacks, Tag 05TL] — which reads off `j = t ∘ inj` from `inj` — is stated against exactly
this description. The `eqToHom` transports along that pinning of the resolving complex;
the two ways of forming the image of `F K` in `K⁺(C)` agree by `rfl`, so no compatibility
lemma is involved.

Faithfulness to the source. (1) No hypothesis is idle: `(J, η, hη)` is used by the first
conjunct, which is an existence statement false for a general abelian category, and
`Abelian C` is what makes `ℐ`, `Comp⁺(C)`, its quasi-isomorphisms and `K⁺(C)` available;
the second conjunct is the source's part (2), which is likewise asserted for an arbitrary
functor `inj`. (2) The base is the source's: one fixed abelian category `C = 𝒜`, with
`ℐ = InjectiveObject C`, `ℤ`-graded cochain complexes bounded below, and `α` a morphism of
*complexes* in part (1) — not a homotopy class, which is where the added strength over
[Stacks, Tag 013X] lies. (3) The canonical maps are pinned: `α` is the source's family
`i_{K}` and is quantified over as data rather than merely asserted to exist degreewise,
and in part (2) both fields of the resolution functor are pinned to the images of `F` and
`α`. (4) The instantiation is not degenerate: `C = ModuleCat R` has functorial injective
embeddings, namely `M ↦ (M → J(M))` of [Stacks, Tag 01DD], so the hypothesis is
satisfiable, and part (1) then produces a resolution functor for it through part (2).

## References

* [Stacks, Tag 0141]
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

namespace StacksDraft.FunctorialInjectiveResolutions

section CartanEilenberg

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The data of a functorial degreewise injective embedding of the bounded below complexes of an
abelian category `C`: an endofunctor `Ψ` of `Comp⁺(C)` with injective terms, an embedding
`η : 𝟭 ⟶ Ψ` which is a monomorphism in each degree, and the requirement that `Ψ M` vanish in
every degree where `M` does. -/
public structure Setup (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The endofunctor of `Comp⁺(C)`. -/
  fn : CochainComplex.Plus C ⥤ CochainComplex.Plus C
  /-- The embedding of the identity functor into it. -/
  unit : 𝟭 (CochainComplex.Plus C) ⟶ fn
  /-- The embedding is a monomorphism in each degree. -/
  mono_unit (M : CochainComplex.Plus C) (n : ℤ) : Mono ((unit.app M).hom.f n)
  /-- The target of the embedding has injective terms. -/
  injective_fn (M : CochainComplex.Plus C) (n : ℤ) : Injective ((fn.obj M).obj.X n)
  /-- The target of the embedding vanishes wherever its source does. -/
  isZero_fn (M : CochainComplex.Plus C) (n : ℤ) :
    IsZero (M.obj.X n) → IsZero ((fn.obj M).obj.X n)

namespace Setup

/-- The embedding in a fixed degree. -/
public noncomputable def u (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    M.obj.X p ⟶ (S.fn.obj M).obj.X p := (S.unit.app M).hom.f p

private instance monoU (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    Mono (C := C) (S.u M p) := S.mono_unit M p

private instance injectiveFn (S : Setup C) (M : CochainComplex.Plus C) (n : ℤ) :
    Injective (C := C) ((S.fn.obj M).obj.X n) := S.injective_fn M n

/-- The embedding commutes with the differentials. -/
public lemma u_comm (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    S.u M p ≫ (S.fn.obj M).obj.d p p' = M.obj.d p p' ≫ S.u M p' :=
  (S.unit.app M).hom.comm p p'

/-- The naturality square of the embedding, in a fixed degree. -/
public lemma u_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    S.u M p ≫ (S.fn.map f).hom.f p = f.hom.f p ≫ S.u N p := by
  have h2 : (S.unit.app M).hom.f p ≫ (S.fn.map f).hom.f p =
      f.hom.f p ≫ (S.unit.app N).hom.f p := by
    have h3 := congrArg (fun (w : M ⟶ S.fn.obj N) => w.hom.f p) (NatTrans.naturality S.unit f)
    simpa using h3.symm
  exact h2

/-- The projection to a cokernel composed with a map of cokernels. -/
@[simp, reassoc (attr := simp)]
private lemma π_cokernelMap {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y')
    (w : f ≫ β = α ≫ g) :
    cokernel.π f ≫ cokernel.map f g α β w = β ≫ cokernel.π g :=
  cokernel.π_desc _ _ _

/-- The differential of the degreewise cokernel of the embedding. -/
public noncomputable def cokd (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    cokernel (S.u M p) ⟶ cokernel (S.u M p') :=
  cokernel.map _ _ (M.obj.d p p') ((S.fn.obj M).obj.d p p') (S.u_comm M p p')

@[simp, reassoc (attr := simp)]
private lemma π_cokd (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    cokernel.π (S.u M p) ≫ S.cokd M p p' =
      (S.fn.obj M).obj.d p p' ≫ cokernel.π (S.u M p') :=
  cokernel.π_desc _ _ _

/-- The degreewise cokernel of the embedding, as a cochain complex. -/
public noncomputable def cokComplex (S : Setup C) (M : CochainComplex.Plus C) :
    CochainComplex C ℤ where
  X p := cokernel (S.u M p)
  d := S.cokd M
  shape p p' h := by
    have h0 : (S.fn.obj M).obj.d p p' = 0 := (S.fn.obj M).obj.shape p p' h
    refine (cancel_epi (cokernel.π (S.u M p))).1 ?_
    rw [comp_zero, π_cokd, h0, zero_comp]
  d_comp_d' p p' p'' _ _ := by
    refine (cancel_epi (cokernel.π (S.u M p))).1 ?_
    rw [comp_zero, π_cokd_assoc, π_cokd, ← Category.assoc,
      HomologicalComplex.d_comp_d, zero_comp]

@[simp]
private lemma cokComplex_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.cokComplex M).X p = cokernel (S.u M p) := rfl

@[simp]
private lemma cokComplex_d (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    (S.cokComplex M).d p p' = S.cokd M p p' := rfl

/-- The morphism of degreewise cokernels induced by a morphism of complexes, in one degree. -/
public noncomputable def cokMapf (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N)
    (p : ℤ) : cokernel (S.u M p) ⟶ cokernel (S.u N p) :=
  cokernel.map _ _ (f.hom.f p) ((S.fn.map f).hom.f p) (S.u_naturality f p)

@[simp, reassoc (attr := simp)]
private lemma π_cokMapf (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    cokernel.π (S.u M p) ≫ S.cokMapf f p =
      (S.fn.map f).hom.f p ≫ cokernel.π (S.u N p) :=
  cokernel.π_desc _ _ _

/-- The morphism of degreewise cokernels induced by a morphism of complexes. -/
public noncomputable def cokMap (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) :
    S.cokComplex M ⟶ S.cokComplex N where
  f := S.cokMapf f
  comm' p p' _ := by
    dsimp only [cokComplex_X, cokComplex_d]
    refine (cancel_epi (cokernel.π (S.u M p))).1 ?_
    rw [π_cokMapf_assoc, π_cokd, π_cokd_assoc, π_cokMapf, ← Category.assoc, ← Category.assoc,
      HomologicalComplex.Hom.comm]

@[simp]
private lemma cokMap_f (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    (S.cokMap f).f p = S.cokMapf f p := rfl

/-- The degreewise cokernel of the embedding, as a functor to all cochain complexes. -/
public noncomputable def cokFunctor (S : Setup C) :
    CochainComplex.Plus C ⥤ CochainComplex C ℤ where
  obj M := S.cokComplex M
  map f := S.cokMap f
  map_id M := by
    ext p
    dsimp only [cokMap_f, cokComplex_X, HomologicalComplex.id_f]
    refine (cancel_epi (cokernel.π (S.u M p))).1 ?_
    rw [Category.comp_id, π_cokMapf]
    simp
  map_comp {M N P} f g := by
    ext p
    dsimp only [cokMap_f, cokComplex_X, HomologicalComplex.comp_f]
    refine (cancel_epi (cokernel.π (S.u M p))).1 ?_
    rw [π_cokMapf, π_cokMapf_assoc, π_cokMapf]
    simp

/-- The degreewise cokernel of the embedding vanishes wherever the source does. -/
private lemma isZero_cokComplex_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ)
    (h : IsZero (M.obj.X p)) : IsZero ((S.cokComplex M).X p) := by
  rw [cokComplex_X]
  exact IsZero.of_epi (cokernel.π (S.u M p)) (S.isZero_fn M p h)

/-- The degreewise cokernel of the embedding is bounded below. -/
public lemma plus_cokComplex (S : Setup C) (M : CochainComplex.Plus C) :
    CochainComplex.plus C (S.cokComplex M) := by
  obtain ⟨n, hn⟩ := M.property
  have := hn
  refine ⟨n, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact S.isZero_cokComplex_X M i (CochainComplex.isZero_of_isStrictlyGE M.obj n i hi)

/-- The degreewise cokernel of the embedding, as an endofunctor of `Comp⁺(C)`. -/
public noncomputable def Q (S : Setup C) : CochainComplex.Plus C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ S.cokFunctor S.plus_cokComplex

@[simp]
private lemma Q_obj_obj (S : Setup C) (M : CochainComplex.Plus C) :
    (S.Q.obj M).obj = S.cokComplex M := rfl

/-- The projection of the embedding onto its degreewise cokernel, in a fixed degree. -/
public noncomputable def cokπ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.fn.obj M).obj.X p ⟶ (S.Q.obj M).obj.X p := cokernel.π (S.u M p)

/-- The morphism of degreewise cokernels induced by a morphism of complexes, in a fixed
degree. -/
private noncomputable def Qf (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    (S.Q.obj M).obj.X p ⟶ (S.Q.obj N).obj.X p := (S.Q.map f).hom.f p

private instance epiCokπ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    Epi (C := C) (S.cokπ M p) := by
  have h : Epi (cokernel.π (S.u M p)) := inferInstance
  exact h

/-- The embedding followed by the projection onto its cokernel vanishes. -/
private lemma u_comp_cokπ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    S.u M p ≫ S.cokπ M p = 0 := cokernel.condition _

/-- The projection onto the degreewise cokernel exhibits it as a cokernel. -/
private noncomputable def isColimitCokπ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (S.cokπ M p) (S.u_comp_cokπ M p)) :=
  cokernelIsCokernel (S.u M p)

/-- The projection onto the degreewise cokernel commutes with the differentials. -/
private lemma cokπ_comm (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    S.cokπ M p ≫ (S.Q.obj M).obj.d p p' = (S.fn.obj M).obj.d p p' ≫ S.cokπ M p' :=
  π_cokd S M p p'

/-- The projection onto the degreewise cokernel is natural. -/
private lemma cokπ_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    S.cokπ M p ≫ S.Qf f p = (S.fn.map f).hom.f p ≫ S.cokπ N p :=
  π_cokMapf S f p

/-- The differential of the resolution in a fixed degree: the projection onto the cokernel of
the embedding, followed by the embedding of that cokernel. -/
public noncomputable def dRes (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.fn.obj M).obj.X p ⟶ (S.fn.obj (S.Q.obj M)).obj.X p :=
  S.cokπ M p ≫ S.u (S.Q.obj M) p

/-- Two consecutive differentials of the resolution compose to zero. -/
public lemma dRes_comp_dRes (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    S.dRes M p ≫ S.dRes (S.Q.obj M) p = 0 := by
  simp only [dRes]
  rw [Category.assoc, ← Category.assoc (S.u (S.Q.obj M) p), u_comp_cokπ, zero_comp, comp_zero]

/-- The naturality of the embedding, applied to the cokernel step. -/
private lemma u_naturality_Q (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    S.u (S.Q.obj M) p ≫ (S.fn.map (S.Q.map f)).hom.f p = S.Qf f p ≫ S.u (S.Q.obj N) p :=
  S.u_naturality (S.Q.map f) p

/-- The naturality of the differential of the resolution. -/
private lemma dRes_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    (S.fn.map f).hom.f p ≫ S.dRes N p = S.dRes M p ≫ (S.fn.map (S.Q.map f)).hom.f p := by
  simp only [dRes]
  rw [Category.assoc, u_naturality_Q, ← Category.assoc, ← cokπ_naturality, Category.assoc]

/-- The `q`-th iterate of the cokernel endofunctor. -/
public noncomputable def iter (S : Setup C) : ℕ → (CochainComplex.Plus C ⥤ CochainComplex.Plus C)
  | 0 => 𝟭 _
  | (q + 1) => S.iter q ⋙ S.Q

/-- The `q`-th term of the resolution, as an endofunctor of `Comp⁺(C)`. -/
public noncomputable def emb (S : Setup C) (q : ℕ) :
    CochainComplex.Plus C ⥤ CochainComplex.Plus C := S.iter q ⋙ S.fn

/-- The differential of the resolution at the `q`-th step, in a fixed degree. -/
public noncomputable def dCol (S : Setup C) (q : ℕ) (M : CochainComplex.Plus C) (p : ℤ) :
    ((S.emb q).obj M).obj.X p ⟶ ((S.emb (q + 1)).obj M).obj.X p :=
  S.dRes ((S.iter q).obj M) p

/-- The differential of the resolution commutes with the differentials of the complex. -/
private lemma dRes_comm (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    (S.fn.obj M).obj.d p p' ≫ S.dRes M p' =
      S.dRes M p ≫ (S.fn.obj (S.Q.obj M)).obj.d p p' := by
  simp only [dRes]
  rw [← Category.assoc, ← cokπ_comm, Category.assoc, ← u_comm, ← Category.assoc]

/-- The naturality of the `q`-th differential of the resolution. -/
private lemma dCol_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (q : ℕ)
    (p : ℤ) :
    ((S.emb q).map f).hom.f p ≫ S.dCol q N p =
      S.dCol q M p ≫ ((S.emb (q + 1)).map f).hom.f p :=
  S.dRes_naturality ((S.iter q).map f) p

/-- The `p`-th column of the double complex: the resolution of `Mᵖ`, indexed by `ℕ`. -/
public noncomputable def col (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    CochainComplex C ℕ :=
  CochainComplex.of (fun q => ((S.emb q).obj M).obj.X p) (fun q => S.dCol q M p)
    (fun q => S.dRes_comp_dRes ((S.iter q).obj M) p)

@[simp]
private lemma col_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) (q : ℕ) :
    (S.col M p).X q = ((S.emb q).obj M).obj.X p := rfl

@[simp]
private lemma col_d (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) (q : ℕ) :
    (S.col M p).d q (q + 1) = S.dCol q M p := by
  simp [col]

/-- The morphism of columns induced by a morphism of complexes. -/
public noncomputable def colMap (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    S.col M p ⟶ S.col N p :=
  CochainComplex.ofHom (fun q => ((S.emb q).map f).hom.f p) (fun q => by
    rw [col_d, col_d]
    exact S.dCol_naturality f q p)

@[simp]
private lemma colMap_f (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) (q : ℕ) :
    (S.colMap f p).f q = ((S.emb q).map f).hom.f p := rfl

/-- The differential of the double complex in the direction of the complex. -/
public noncomputable def colD (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    S.col M p ⟶ S.col M p' :=
  CochainComplex.ofHom (fun q => ((S.emb q).obj M).obj.d p p') (fun q => by
    rw [col_d, col_d]
    exact S.dRes_comm ((S.iter q).obj M) p p')

@[simp]
private lemma colD_f (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) (q : ℕ) :
    (S.colD M p p').f q = ((S.emb q).obj M).obj.d p p' := rfl

/-- The double complex `I^{p, q} = (Ψ (Q^q M))ᵖ` of the construction, with the resolution
degree indexed by `ℕ`. -/
public noncomputable def dbl (S : Setup C) (M : CochainComplex.Plus C) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ) where
  X p := S.col M p
  d := S.colD M
  shape p p' h := by
    ext q
    have h0 : ((S.emb q).obj M).obj.d p p' = 0 := ((S.emb q).obj M).obj.shape p p' h
    simp only [colD_f]
    exact h0
  d_comp_d' p p' p'' _ _ := by
    ext q
    have h0 : ((S.emb q).obj M).obj.d p p' ≫ ((S.emb q).obj M).obj.d p' p'' = 0 :=
      HomologicalComplex.d_comp_d _ _ _ _
    simp only [HomologicalComplex.comp_f, colD_f]
    exact h0

@[simp]
private lemma dbl_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.dbl M).X p = S.col M p := rfl

@[simp]
private lemma dbl_d (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    (S.dbl M).d p p' = S.colD M p p' := rfl

/-- The morphism of double complexes induced by a morphism of complexes. -/
public noncomputable def dblMap (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) :
    S.dbl M ⟶ S.dbl N where
  f := S.colMap f
  comm' p p' _ := by
    ext q
    exact ((S.emb q).map f).hom.comm p p'

@[simp]
private lemma dblMap_f (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    (S.dblMap f).f p = S.colMap f p := rfl

/-- The double complex of the construction, as a functor of the complex. -/
public noncomputable def dblFunctor (S : Setup C) :
    CochainComplex.Plus C ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ) where
  obj M := S.dbl M
  map f := S.dblMap f
  map_id M := by
    ext p q
    simp
  map_comp f g := by
    ext p q
    simp

/-- The double complex of the construction, its resolution degree extended by zero to `ℤ`. -/
public noncomputable def I (S : Setup C) :
    CochainComplex.Plus C ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  S.dblFunctor ⋙
    (ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)

@[simp]
private lemma I_obj_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.I.obj M).X p = (S.col M p).extend ComplexShape.embeddingUpNat := rfl

/-- Every iterate of the cokernel endofunctor vanishes where the complex does. -/
private lemma isZero_iter_X (S : Setup C) (M : CochainComplex.Plus C) (q : ℕ) (p : ℤ)
    (h : IsZero (M.obj.X p)) : IsZero (((S.iter q).obj M).obj.X p) := by
  induction q with
  | zero => exact h
  | succ q ih => exact S.isZero_cokComplex_X ((S.iter q).obj M) p ih

/-- Every term of the resolution vanishes where the complex does. -/
private lemma isZero_emb_X (S : Setup C) (M : CochainComplex.Plus C) (q : ℕ) (p : ℤ)
    (h : IsZero (M.obj.X p)) : IsZero (((S.emb q).obj M).obj.X p) :=
  S.isZero_fn _ p (S.isZero_iter_X M q p h)

/-- The columns of the double complex vanish where the complex does. -/
private lemma isZero_col (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ)
    (h : IsZero (M.obj.X p)) : IsZero (S.col M p) := by
  rw [IsZero.iff_id_eq_zero]
  ext q
  exact (S.isZero_emb_X M q p h).eq_of_src _ _

private lemma isZero_I_X (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ)
    (h : IsZero (M.obj.X p)) : IsZero ((S.I.obj M).X p) := by
  rw [I_obj_X]
  exact Functor.map_isZero (ComplexShape.embeddingUpNat.extendFunctor C) (S.isZero_col M p h)

private lemma isZero_I_X_X (S : Setup C) (M : CochainComplex.Plus C) (p q : ℤ) (hq : q < 0) :
    IsZero (((S.I.obj M).X p).X q) := by
  rw [I_obj_X]
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q hq

private lemma injective_I_X_X (S : Setup C) (M : CochainComplex.Plus C) (p q : ℤ) :
    Injective (((S.I.obj M).X p).X q) := by
  rw [I_obj_X]
  by_cases hq : 0 ≤ q
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have hinj : Injective ((S.col M p).X k) := S.injective_fn ((S.iter k).obj M) p
    exact Injective.of_iso
      (HomologicalComplex.extendXIso (S.col M p) ComplexShape.embeddingUpNat
        (i := k) (i' := (k : ℤ)) rfl).symm hinj
  · exact IsZero.injective (CochainComplex.isZero_of_isStrictlyGE _ 0 q (by lia))

private lemma hasTotal_I (S : Setup C) (M : CochainComplex.Plus C) :
    (S.I.obj M).HasTotal (ComplexShape.up ℤ) := by
  obtain ⟨a, ha⟩ := M.property
  have := ha
  exact StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ a
    (fun p q hq => S.isZero_I_X_X M p q hq)
    (fun p hp => S.isZero_I_X M p (CochainComplex.isZero_of_isStrictlyGE M.obj a p hp))

private instance hasTotalI (S : Setup C) (M : CochainComplex.Plus C) :
    (S.I.obj M).HasTotal (ComplexShape.up ℤ) := S.hasTotal_I M

/-- The total complex of the double complex of the construction, as a functor. -/
private noncomputable def Ftot (S : Setup C) : CochainComplex.Plus C ⥤ CochainComplex C ℤ where
  obj M := (S.I.obj M).total (ComplexShape.up ℤ)
  map f := HomologicalComplex₂.total.map (S.I.map f) (ComplexShape.up ℤ)
  map_id M := by
    simp only [CategoryTheory.Functor.map_id]
    exact HomologicalComplex₂.total.map_id _ _
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp]
    exact HomologicalComplex₂.total.map_comp _ _ _

@[simp]
private lemma Ftot_obj (S : Setup C) (M : CochainComplex.Plus C) :
    S.Ftot.obj M = (S.I.obj M).total (ComplexShape.up ℤ) := rfl

private lemma injective_Ftot_X (S : Setup C) (M : CochainComplex.Plus C) (n : ℤ) :
    Injective ((S.Ftot.obj M).X n) := by
  obtain ⟨a, ha⟩ := M.property
  have := ha
  exact StacksDraft.TotalComplexQuasiIso.injective_total_X_of_bounded _ a
    (fun p q hq => S.isZero_I_X_X M p q hq)
    (fun p hp => S.isZero_I_X M p (CochainComplex.isZero_of_isStrictlyGE M.obj a p hp))
    (fun p q => S.injective_I_X_X M p q) n

private lemma isStrictlyGE_Ftot (S : Setup C) (M : CochainComplex.Plus C) (a : ℤ)
    [M.obj.IsStrictlyGE a] : (S.Ftot.obj M).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact StacksDraft.TotalComplexQuasiIso.isZero_total_X _ a
    (fun p q hq => S.isZero_I_X_X M p q hq)
    (fun p hp => S.isZero_I_X M p (CochainComplex.isZero_of_isStrictlyGE M.obj a p hp)) n hn

/-- The total complex of the construction, as a complex of injective objects. -/
private noncomputable def Finj (S : Setup C) :
    CochainComplex.Plus C ⥤ CochainComplex (InjectiveObject C) ℤ :=
  HomologicalComplex.liftFunctorObjectProperty (isInjective C) S.Ftot S.injective_Ftot_X

/-- The functorial injective resolution produced by the construction. -/
private noncomputable def F (S : Setup C) :
    CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C) :=
  ObjectProperty.lift _ S.Finj (fun M => by
    obtain ⟨a, ha⟩ := M.property
    have := ha
    refine ⟨a, ?_⟩
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
    exact S.isStrictlyGE_Ftot M a)

@[simp]
private lemma F_comp_ι_obj_obj (S : Setup C) (M : CochainComplex.Plus C) :
    ((S.F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj M).obj = S.Ftot.obj M := rfl

@[simp]
private lemma F_comp_ι_map_hom (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) :
    ((S.F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).map f).hom = S.Ftot.map f := rfl

/-- The embedding followed by the differential of the resolution vanishes. -/
private lemma u_comp_dRes (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    S.u M p ≫ S.dRes M p = 0 := by
  simp only [dRes]
  rw [← Category.assoc, u_comp_cokπ, zero_comp]

/-- `0 ⟶ Mᵖ ⟶ (Ψ M)ᵖ ⟶ (Ψ Q M)ᵖ` is exact: since the second embedding is a monomorphism,
the kernel of `π ≫ ε` is the kernel of `π`, which is the image of the first embedding. -/
private lemma exact_u_dRes (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (ShortComplex.mk (S.u M p) (S.dRes M p) (S.u_comp_dRes M p)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (S.u M p) (S.cokπ M p) (S.u_comp_cokπ M p))
    (S₂ := ShortComplex.mk (S.u M p) (S.dRes M p) (S.u_comp_dRes M p))
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := S.u (S.Q.obj M) p
      comm₁₂ := by simp
      comm₂₃ := by simp [dRes] }).1
    (ShortComplex.exact_of_g_is_cokernel _ (S.isColimitCokπ M p))

/-- Two consecutive differentials of the resolution are exact: the projection onto the cokernel
is an epimorphism, so the image of `π ≫ ε` is the image of `ε`. -/
private lemma exact_dRes_dRes (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (ShortComplex.mk (S.dRes M p) (S.dRes (S.Q.obj M) p) (S.dRes_comp_dRes M p)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (S.dRes M p) (S.dRes (S.Q.obj M) p) (S.dRes_comp_dRes M p))
    (S₂ := ShortComplex.mk (S.u (S.Q.obj M) p) (S.dRes (S.Q.obj M) p)
      (S.u_comp_dRes (S.Q.obj M) p))
    { τ₁ := S.cokπ M p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [dRes]
      comm₂₃ := by simp }).2 (S.exact_u_dRes (S.Q.obj M) p)

/-- The augmentation of the `p`-th column of the double complex: the embedding `Mᵖ ⟶ (Ψ M)ᵖ`,
regarded as a morphism from the complex concentrated in degree `0`. -/
private noncomputable def aug (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj (M.obj.X p) ⟶ S.col M p :=
  HomologicalComplex.mkHomFromSingle (S.u M p) (fun i hi => by
    obtain rfl : 1 = i := hi
    rw [col_d]
    exact S.u_comp_dRes M p)

/-- The embedding, viewed as a morphism into the bottom term of the `p`-th column. -/
private noncomputable def u0 (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    M.obj.X p ⟶ (S.col M p).X 0 := S.u M p

private instance monoU0 (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    Mono (C := C) (S.u0 M p) := S.mono_unit M p

private lemma u0_comm (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    S.u0 M p ≫ (S.colD M p p').f 0 = M.obj.d p p' ≫ S.u0 M p' := S.u_comm M p p'

private lemma u0_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    S.u0 M p ≫ (S.colMap f p).f 0 = f.hom.f p ≫ S.u0 N p := S.u_naturality f p

private lemma aug_f_zero (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.aug M p).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (M.obj.X p)).hom ≫ S.u0 M p :=
  HomologicalComplex.mkHomFromSingle_f _ _

private lemma emb_obj (S : Setup C) (q : ℕ) (M : CochainComplex.Plus C) :
    (S.emb q).obj M = S.fn.obj ((S.iter q).obj M) := rfl

private lemma iter_zero_obj (S : Setup C) (M : CochainComplex.Plus C) : (S.iter 0).obj M = M := rfl

private lemma col_d_one (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.col M p).d 0 1 = S.dRes M p := col_d S M p 0

private instance monoAugFZero (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    Mono (C := C) ((S.aug M p).f 0) := by
  rw [aug_f_zero]
  infer_instance

/-- The augmentation of a column is exact at the bottom. -/
private lemma exact_aug_col (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ)
    (hz : (S.aug M p).f 0 ≫ (S.col M p).d 0 1 = 0) :
    (ShortComplex.mk ((S.aug M p).f 0) ((S.col M p).d 0 1) hz).Exact := by
  refine ShortComplex.exact_of_iso ?_ (S.exact_u_dRes M p)
  refine ShortComplex.isoMk
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (M.obj.X p)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact Eq.trans
      (congrArg
        (fun t => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (M.obj.X p)).inv ≫ t)
        (aug_f_zero S M p))
      (Eq.trans (Iso.inv_hom_id_assoc _ _) (Category.comp_id _).symm)
  · exact Eq.trans (Eq.trans (Category.id_comp _) (col_d_one S M p)) (Category.comp_id _).symm

/-- The columns of the double complex are exact in positive degrees. -/
private lemma exactAt_col_succ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) (k : ℕ) :
    (S.col M p).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2) (by simp) (by simp)]
  refine ShortComplex.exact_of_iso ?_ (S.exact_dRes_dRes ((S.iter k).obj M) p)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact Eq.trans (Eq.trans (Category.id_comp _) (col_d S M p k)) (Category.comp_id _).symm
  · exact Eq.trans (Eq.trans (Category.id_comp _) (col_d S M p (k + 1)))
      (Category.comp_id _).symm

/-- The augmentation of a column is a quasi-isomorphism: the column is an injective resolution
of `Mᵖ`. -/
private instance quasiIsoAug (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    QuasiIso (S.aug M p) := by
  rw [quasiIso_iff]
  intro n
  obtain _ | k := n
  · have h0 : ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj (M.obj.X p)).d 0 0 = 0 :=
      HomologicalComplex.shape _ 0 0 (by simp)
    have h1 : ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj (M.obj.X p)).d 0 1 = 0 :=
      HomologicalComplex.single_obj_d _ _ _ _ _
    have h2 : (S.col M p).d 0 0 = 0 := HomologicalComplex.shape _ 0 0 (by simp)
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ h0 h1 h2]
    exact ⟨S.exact_aug_col M p _, S.monoAugFZero M p⟩
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj (M.obj.X p) k)]
    exact S.exactAt_col_succ M p k

@[simp]
private lemma I_obj_d (S : Setup C) (M : CochainComplex.Plus C) (p p' : ℤ) :
    (S.I.obj M).d p p' =
      HomologicalComplex.extendMap (S.colD M p p') ComplexShape.embeddingUpNat := rfl

@[simp]
private lemma I_map_f (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) (p : ℤ) :
    (S.I.map f).f p =
      HomologicalComplex.extendMap (S.colMap f p) ComplexShape.embeddingUpNat := rfl

@[simp]
private lemma srz_X (M : CochainComplex.Plus C) (p : ℤ) :
    (StacksDraft.TotalComplexQuasiIso.singleRowZero M.obj).X p =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (M.obj.X p) := rfl

@[simp]
private lemma srz_d (M : CochainComplex.Plus C) (p p' : ℤ) :
    (StacksDraft.TotalComplexQuasiIso.singleRowZero M.obj).d p p' =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (M.obj.d p p') := rfl

@[simp]
private lemma srz_map_f (M N : CochainComplex.Plus C) (f : M ⟶ N) (p : ℤ) :
    ((((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f.hom).f p) =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (f.hom.f p) := rfl

/-- The identification of the bottom term of a column with the corresponding term of its
extension by zero. -/
private noncomputable def eXinv (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.col M p).X 0 ⟶ ((S.col M p).extend ComplexShape.embeddingUpNat).X 0 :=
  (HomologicalComplex.extendXIso (S.col M p) ComplexShape.embeddingUpNat
    (i := 0) (i' := (0 : ℤ)) ComplexShape.embeddingUpNat_f_zero).inv

/-- The augmentation of the `p`-th column, extended by zero to a `ℤ`-indexed complex. -/
private noncomputable def augZ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (M.obj.X p) ⟶
      (S.col M p).extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (M.obj.X p) 0 0
      ComplexShape.embeddingUpNat_f_zero).inv ≫
    HomologicalComplex.extendMap (S.aug M p) ComplexShape.embeddingUpNat

private instance quasiIsoAugZ (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    QuasiIso (S.augZ M p) := by
  have h1 : QuasiIso (HomologicalComplex.extendMap (S.aug M p) ComplexShape.embeddingUpNat) := by
    rw [HomologicalComplex.quasiIso_extendMap_iff]
    infer_instance
  dsimp only [augZ]
  infer_instance

private lemma augZ_f_zero (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.augZ M p).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (M.obj.X p)).hom ≫
        S.u0 M p ≫ S.eXinv M p := by
  dsimp only [augZ, eXinv]
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ))
      ComplexShape.embeddingUpNat_f_zero,
    HomologicalComplex.extendSingleIso_inv_f, aug_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The extension by zero of a morphism of columns, in degree `0`. -/
private lemma eXinv_comp_extendMap_f (S : Setup C) {M N : CochainComplex.Plus C}
    {p p' : ℤ} (φ : S.col M p ⟶ S.col N p') :
    S.eXinv M p ≫ (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f 0 =
      φ.f 0 ≫ S.eXinv N p' := by
  dsimp only [eXinv]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ))
      ComplexShape.embeddingUpNat_f_zero, Iso.inv_hom_id_assoc]

/-- The augmentation of the double complex of the construction: the morphism from the complex
`M`, placed in resolution degree `0`, to the double complex `I`. -/
private noncomputable def uAug (S : Setup C) (M : CochainComplex.Plus C) :
    StacksDraft.TotalComplexQuasiIso.singleRowZero M.obj ⟶ S.I.obj M where
  f := S.augZ M
  comm' p p' _ := by
    dsimp only [I_obj_X, srz_X, I_obj_d, srz_d]
    refine HomologicalComplex.from_single_hom_ext (c := ComplexShape.up ℤ) ?_
    simp only [HomologicalComplex.comp_f, augZ_f_zero, HomologicalComplex.single_map_f_self,
      Category.assoc, Iso.inv_hom_id_assoc, eXinv_comp_extendMap_f]
    rw [← Category.assoc (S.u0 M p), u0_comm, Category.assoc]

@[simp]
private lemma uAug_f (S : Setup C) (M : CochainComplex.Plus C) (p : ℤ) :
    (S.uAug M).f p = S.augZ M p := rfl

private lemma uAug_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) :
    S.uAug M ≫ S.I.map f =
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f.hom ≫ S.uAug N := by
  ext p : 1
  simp only [HomologicalComplex.comp_f]
  dsimp only [I_obj_X, srz_X, uAug_f, I_map_f, srz_map_f]
  refine HomologicalComplex.from_single_hom_ext (c := ComplexShape.up ℤ) ?_
  simp only [HomologicalComplex.comp_f, augZ_f_zero, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc, eXinv_comp_extendMap_f]
  rw [← Category.assoc (S.u0 M p), u0_naturality, Category.assoc]

private lemma hasTotal_srz (M : CochainComplex.Plus C) :
    (StacksDraft.TotalComplexQuasiIso.singleRowZero M.obj).HasTotal (ComplexShape.up ℤ) := by
  obtain ⟨a, ha⟩ := M.property
  have := ha
  exact StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ a
    (fun p q hq => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X M.obj p q hq)
    (fun p hp => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X M.obj a p hp)

attribute [instance] hasTotal_srz

/-- The comparison map `M ⟶ Tot(I)` of the construction. -/
private noncomputable def alphaHom (S : Setup C) (M : CochainComplex.Plus C) :
    M.obj ⟶ (S.I.obj M).total (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit M.obj ≫
    HomologicalComplex₂.total.map (S.uAug M) (ComplexShape.up ℤ)

private lemma quasiIso_alphaHom (S : Setup C) (M : CochainComplex.Plus C) :
    QuasiIso (S.alphaHom M) := by
  obtain ⟨a, ha⟩ := M.property
  have := ha
  have h1 : IsIso (StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit M.obj) :=
    StacksDraft.TotalComplexQuasiIso.isIso_totalSingleRowZeroUnit M.obj
  have h2 : QuasiIso (HomologicalComplex₂.total.map (S.uAug M) (ComplexShape.up ℤ)) :=
    StacksDraft.TotalComplexQuasiIso.quasiIso_total_map (S.uAug M) a
      (fun p q hq => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X M.obj p q hq)
      (fun p hp => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X M.obj a p hp)
      (fun p q hq => S.isZero_I_X_X M p q hq)
      (fun p hp => S.isZero_I_X M p (CochainComplex.isZero_of_isStrictlyGE M.obj a p hp))
      (fun p => S.quasiIsoAugZ M p)
  dsimp only [alphaHom]
  infer_instance

private lemma alphaHom_naturality (S : Setup C) {M N : CochainComplex.Plus C} (f : M ⟶ N) :
    f.hom ≫ S.alphaHom N =
      S.alphaHom M ≫ HomologicalComplex₂.total.map (S.I.map f) (ComplexShape.up ℤ) := by
  simp only [alphaHom]
  rw [Category.assoc, ← HomologicalComplex₂.total.map_comp, S.uAug_naturality f,
    HomologicalComplex₂.total.map_comp,
    ← Category.assoc (StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit M.obj),
    StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit_naturality, Category.assoc]

/-- The natural transformation `𝟭 ⟶ F ⋙ ι` of the construction. -/
private noncomputable def alpha (S : Setup C) :
    𝟭 (CochainComplex.Plus C) ⟶ S.F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus where
  app M := ObjectProperty.homMk (S.alphaHom M)
  naturality {M N} f := by
    apply ObjectProperty.hom_ext
    exact S.alphaHom_naturality f

/-- **The Cartan-Eilenberg step with the lower bound.**  The resolution the construction produces
resolves a complex vanishing in every degree below `a` by a complex vanishing in every degree
below `a`:  `F K` is the total complex of a double complex whose column `p` vanishes when `K^p`
does, which is `isStrictlyGE_Ftot`. -/
private theorem exists_functorial_resolution_isStrictlyGE (S : Setup C) :
    ∃ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
      (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
      (∀ K, CochainComplex.Plus.quasiIso C (α.app K)) ∧
        ∀ (K : CochainComplex.Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
          ((F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj K).obj.IsStrictlyGE a :=
  ⟨S.F, S.alpha, fun K => S.quasiIso_alphaHom K, fun K a h =>
    have := h
    S.isStrictlyGE_Ftot K a⟩

end Setup

end CartanEilenberg

section Auxiliary

variable {C : Type*} [Category C] [Abelian C]

/-- The bounded below cochain complex underlying an object of `K⁺(C)`. The objects of
`K⁺(C)` are the bounded below complexes themselves, so this is a two-sided inverse of
`HomotopyCategory.Plus.quotient C` on objects. -/
private def unquotient (K : HomotopyCategory.Plus C) : CochainComplex.Plus C :=
  ⟨K.obj.as, by rw [← HomotopyCategory.plus_quotient_obj_iff]; exact K.property⟩

private lemma quotient_obj_unquotient (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.quotient C).obj (unquotient K) = K := rfl

private lemma unquotient_quotient_obj (K : CochainComplex.Plus C) :
    unquotient ((HomotopyCategory.Plus.quotient C).obj K) = K := rfl

/-- The image in `K⁺(C)` of a quasi-isomorphism of bounded below complexes is a
quasi-isomorphism of `K⁺(C)`. -/
private lemma quasiIso_quotient_map {K L : CochainComplex.Plus C} (f : K ⟶ L)
    (hf : CochainComplex.Plus.quasiIso C f) :
    HomotopyCategory.Plus.quasiIso C ((HomotopyCategory.Plus.quotient C).map f) :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff f.hom).2 hf

/-- The resolution functor attached to a functorial injective resolution `(F, α)` of the
bounded below complexes of `C`: it sends an object `K` of `K⁺(C)`, i.e. a bounded below
complex, to the image of `F K` in `K⁺(ℐ)` together with the homotopy class of `α_K`. -/
private noncomputable def resolutionFunctor
    (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
    (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus)
    (hα : ∀ K, CochainComplex.Plus.quasiIso C (α.app K)) :
    (∀ K : HomotopyCategory.Plus C,
      (HomotopyCategory.Plus.localizerMorphism C).RightResolution K) := fun K ↦
  { X₁ := (HomotopyCategory.Plus.quotient (InjectiveObject C)).obj (F.obj (unquotient K))
    w := (HomotopyCategory.Plus.quotient C).map (α.app (unquotient K))
    hw := quasiIso_quotient_map _ (hα (unquotient K)) }

section Reduction

variable (G : C ⥤ C)

/-- The functor `A ↦ Ker (G A ⟶ G 0)`, the *reduction* of an endofunctor `G` of an abelian
category. It agrees with `G` up to the direct summand `G 0`, and unlike `G` it sends zero
morphisms to zero morphisms (`redFunctor_preservesZeroMorphisms`). -/
private noncomputable def redFunctor : C ⥤ C where
  obj A := kernel (G.map (0 : A ⟶ 0))
  map {A B} f := kernel.map _ _ (G.map f) (𝟙 _) (by simp [← G.map_comp])
  map_id A := by
    rw [← cancel_mono (kernel.ι (G.map (0 : A ⟶ 0)))]
    simp [kernel.map]
  map_comp {A B D} f g := by
    rw [← cancel_mono (kernel.ι (G.map (0 : D ⟶ 0)))]
    simp [kernel.map, G.map_comp]

/-- The canonical monomorphism `Ker (G A ⟶ G 0) ⟶ G A`. -/
private noncomputable def redι (A : C) : (redFunctor G).obj A ⟶ G.obj A :=
  kernel.ι (G.map (0 : A ⟶ 0))

private lemma mono_redι (A : C) : Mono (redι G A) :=
  inferInstanceAs (Mono (kernel.ι (G.map (0 : A ⟶ 0))))

private lemma redι_comp (A : C) : redι G A ≫ G.map (0 : A ⟶ 0) = 0 := kernel.condition _

private lemma redFunctor_map_ι {A B : C} (f : A ⟶ B) :
    (redFunctor G).map f ≫ redι G B = redι G A ≫ G.map f := kernel.lift_ι _ _ _

private lemma map_zero_comp_map_zero (A : C) :
    G.map (0 : (0 : C) ⟶ A) ≫ G.map (0 : A ⟶ 0) = 𝟙 (G.obj 0) := by
  rw [← G.map_comp, (isZero_zero C).eq_of_src ((0 : (0 : C) ⟶ A) ≫ 0) (𝟙 _), G.map_id]

/-- `Ker (G A ⟶ G 0)` is a retract of `G A`: the morphisms `0 → A → 0` split `G 0` off
`G A`, and `Ker (G A ⟶ G 0)` is the complementary summand. -/
private noncomputable def redRetract (A : C) :
    Retract (kernel (G.map (0 : A ⟶ 0))) (G.obj A) where
  i := kernel.ι _
  r := kernel.lift _ (𝟙 (G.obj A) - G.map (0 : A ⟶ 0) ≫ G.map (0 : (0 : C) ⟶ A)) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, map_zero_comp_map_zero,
      Category.comp_id, sub_self])
  retract := by
    rw [← cancel_mono (kernel.ι (G.map (0 : A ⟶ 0)))]
    simp

private lemma injective_redFunctor_obj (A : C) [Injective (G.obj A)] :
    Injective ((redFunctor G).obj A) :=
  (redRetract G A).injective

private lemma redFunctor_preservesZeroMorphisms : (redFunctor G).PreservesZeroMorphisms where
  map_zero A B := by
    have := mono_redι G B
    refine (cancel_mono (redι G B)).1 ?_
    rw [redFunctor_map_ι, zero_comp,
      show (0 : A ⟶ B) = (0 : A ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ B) by simp, G.map_comp,
      ← Category.assoc, redι_comp, zero_comp]

variable (η : 𝟭 C ⟶ G)

/-- The component at `A` of the natural transformation `𝟭 C ⟶ redFunctor G` induced by
`η : 𝟭 C ⟶ G`: the composite `A ⟶ G A ⟶ G 0` is zero by naturality of `η`. -/
private noncomputable def redNatApp (A : C) : A ⟶ (redFunctor G).obj A :=
  kernel.lift _ (η.app A) (by simpa using (η.naturality (0 : A ⟶ (0 : C))).symm)

private lemma redNatApp_ι (A : C) : redNatApp G η A ≫ redι G A = η.app A := kernel.lift_ι _ _ _

/-- The natural transformation `𝟭 C ⟶ redFunctor G` induced by `η : 𝟭 C ⟶ G`. -/
private noncomputable def redNat : 𝟭 C ⟶ redFunctor G where
  app A := redNatApp G η A
  naturality {A B} f := by
    have := mono_redι G B
    refine (cancel_mono (redι G B)).1 ?_
    have h1 : redNatApp G η B ≫ redι G B = η.app B := redNatApp_ι G η B
    have h2 : (redFunctor G).map f ≫ redι G B = redι G A ≫ G.map f := redFunctor_map_ι G f
    have h3 : redNatApp G η A ≫ redι G A = η.app A := redNatApp_ι G η A
    rw [Category.assoc, h1, Category.assoc, h2, ← Category.assoc, h3]
    simpa using η.naturality f

private lemma mono_redNatApp (A : C) [Mono (η.app A)] : Mono (redNatApp G η A) :=
  mono_of_mono_fac (redNatApp_ι G η A)

end Reduction

/-- A functorial injective embedding may be assumed to kill zero morphisms, i.e. to satisfy
`J 0 = 0`: replacing `J A` by `Ker (J A ⟶ J 0)` leaves the values injective, because
`0 → A → 0` splits `J 0` off `J A` as a direct summand, and leaves `η` monomorphic, because
it factors through the kernel. This is the first paragraph of the proof of
[Stacks, Tag 0141]. -/
private lemma exists_injectiveEmbedding_preservesZeroMorphisms (J : C ⥤ InjectiveObject C)
    (η : 𝟭 C ⟶ J ⋙ InjectiveObject.ι C) (hη : ∀ A, Mono (η.app A)) :
    ∃ (J' : C ⥤ InjectiveObject C) (η' : 𝟭 C ⟶ J' ⋙ InjectiveObject.ι C),
      (∀ A, Mono (η'.app A)) ∧ (J' ⋙ InjectiveObject.ι C).PreservesZeroMorphisms := by
  have h : ∀ A, isInjective C ((redFunctor (J ⋙ InjectiveObject.ι C)).obj A) := fun A ↦ by
    have : Injective ((J ⋙ InjectiveObject.ι C).obj A) := (J.obj A).2
    exact injective_redFunctor_obj _ A
  refine ⟨(isInjective C).lift _ h, ?_⟩
  rw [show ((isInjective C).lift (redFunctor (J ⋙ InjectiveObject.ι C)) h) ⋙
      InjectiveObject.ι C = redFunctor (J ⋙ InjectiveObject.ι C) from rfl]
  refine ⟨redNat _ η, fun A ↦ ?_, redFunctor_preservesZeroMorphisms _⟩
  have := hη A
  exact mono_redNatApp _ η A

/-- **The Cartan-Eilenberg step with the lower bound**, from a functorial degreewise injective
embedding. -/
private theorem exists_functorial_injective_resolution_of_degreewise_embedding_isStrictlyGE
    (Φ : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
    (ε : 𝟭 (CochainComplex.Plus C) ⟶ Φ ⋙ (InjectiveObject.ι C).mapCochainComplexPlus)
    (hε : ∀ (K : CochainComplex.Plus C) (n : ℤ), Mono ((ε.app K).hom.f n))
    (hΦ : ∀ (K : CochainComplex.Plus C) (n : ℤ), IsZero (K.obj.X n) →
      IsZero (((Φ ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj K).obj.X n)) :
    ∃ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
      (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
      (∀ K, CochainComplex.Plus.quasiIso C (α.app K)) ∧
        ∀ (K : CochainComplex.Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
          ((F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj K).obj.IsStrictlyGE a :=
  Setup.exists_functorial_resolution_isStrictlyGE
    { fn := Φ ⋙ (InjectiveObject.ι C).mapCochainComplexPlus
      unit := ε
      mono_unit := hε
      injective_fn := fun M n => ((Φ.obj M).obj.X n).property
      isZero_fn := hΦ }

/-- **The functorial injective resolution with the lower bound**, from functorial injective
embeddings. -/
private theorem exists_functorial_injective_resolution_isStrictlyGE'
    (J : C ⥤ InjectiveObject C) (η : 𝟭 C ⟶ J ⋙ InjectiveObject.ι C) (hη : ∀ A, Mono (η.app A)) :
    ∃ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
      (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
      (∀ K, CochainComplex.Plus.quasiIso C (α.app K)) ∧
        ∀ (K : CochainComplex.Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
          ((F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj K).obj.IsStrictlyGE a := by
  obtain ⟨J', η', hη', hJ'⟩ := exists_injectiveEmbedding_preservesZeroMorphisms J η hη
  have hzm : J'.PreservesZeroMorphisms :=
    ⟨fun X Y ↦ (InjectiveObject.ι C).map_injective (by simpa using hJ'.map_zero X Y)⟩
  refine exists_functorial_injective_resolution_of_degreewise_embedding_isStrictlyGE
    J'.mapCochainComplexPlus
    { app := fun K ↦ ⟨{ f := fun n ↦ η'.app (K.obj.X n)
                        comm' := fun i j _ ↦ (η'.naturality _).symm }⟩
      naturality := fun K L f ↦ by
        ext n
        exact η'.naturality (f.hom.f n) } (fun K n ↦ hη' _) (fun K n hK ↦ ?_)
  show IsZero ((J' ⋙ InjectiveObject.ι C).obj (K.obj.X n))
  rw [IsZero.iff_id_eq_zero, ← (J' ⋙ InjectiveObject.ι C).map_id,
    (IsZero.iff_id_eq_zero _).1 hK, Functor.map_zero]

end Auxiliary

section Main

variable (C : Type*) [Category C] [Abelian C]

/-- Let `C` be an abelian category, `F : Comp⁺(C) ⥤ Comp⁺(ℐ)` a functor on bounded below
cochain complexes and `α : 𝟭 ⟶ F ⋙ ι` a natural transformation whose components are
quasi-isomorphisms. Then `C` has a resolution functor ([Stacks, Tag 013W]), namely the one
sending an object `K` of `K⁺(C)` to the image of `F K` in `K⁺(ℐ)`, with comparison map the
homotopy class of `α_K`. -/
private theorem exists_resolutionFunctor
    (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
    (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus)
    (hα : ∀ K, CochainComplex.Plus.quasiIso C (α.app K)) :
    ∃ R : (∀ K : HomotopyCategory.Plus C,
        (HomotopyCategory.Plus.localizerMorphism C).RightResolution K),
      ∀ K : CochainComplex.Plus C,
        ∃ h : (R ((HomotopyCategory.Plus.quotient C).obj K)).X₁ =
            (HomotopyCategory.Plus.quotient (InjectiveObject C)).obj (F.obj K),
          (R ((HomotopyCategory.Plus.quotient C).obj K)).w =
            (HomotopyCategory.Plus.quotient C).map (α.app K) ≫
              eqToHom (congrArg (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj h.symm) :=
  ⟨resolutionFunctor F α hα, fun _ ↦ ⟨rfl, (Category.comp_id _).symm⟩⟩

end Main

end StacksDraft.FunctorialInjectiveResolutions

namespace CochainComplex.Plus

variable (C : Type*) [Category C] [Abelian C]

/-- Let `C` be an abelian category.

(1) If `C` has functorial injective embeddings, i.e. is equipped with a functor
`J : C ⥤ ℐ` to the full subcategory of injective objects and a natural transformation
`η : 𝟭 C ⟶ J` with monomorphic components ([Stacks, Tag 0139]), then there is a functor
`F : Comp⁺(C) ⥤ Comp⁺(ℐ)` on bounded below cochain complexes and a natural transformation
`α : 𝟭 ⟶ F ⋙ ι` whose components are quasi-isomorphisms, i.e. a functorial injective
resolution of bounded below complexes.

(2) Any such pair `(F, α)` — over an arbitrary abelian `C` — induces a resolution functor
for `C` ([Stacks, Tag 013W]), namely the one whose value at `K` is the image of `F K` in
`K⁺(ℐ)` and whose comparison map is the homotopy class of `α_K`. -/
@[stacks 0141]
public theorem exists_functorial_injective_resolution_and_exists_resolutionFunctor :
    (∀ (J : C ⥤ InjectiveObject C) (η : 𝟭 C ⟶ J ⋙ InjectiveObject.ι C),
        (∀ A, Mono (η.app A)) →
        ∃ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
          (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
          ∀ K, CochainComplex.Plus.quasiIso C (α.app K)) ∧
      ∀ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
        (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
        (∀ K, CochainComplex.Plus.quasiIso C (α.app K)) →
        ∃ R : HomotopyCategory.Plus.ResolutionFunctor C,
          ∀ K : CochainComplex.Plus C,
            ∃ h : (R ((HomotopyCategory.Plus.quotient C).obj K)).X₁ =
                (HomotopyCategory.Plus.quotient (InjectiveObject C)).obj (F.obj K),
              (R ((HomotopyCategory.Plus.quotient C).obj K)).w =
                (HomotopyCategory.Plus.quotient C).map (α.app K) ≫
                  eqToHom (congrArg (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj h.symm) :=
  ⟨fun J η hη ↦
    (StacksDraft.FunctorialInjectiveResolutions.exists_functorial_injective_resolution_isStrictlyGE'
      J η hη).imp fun _ h ↦ h.imp fun _ h ↦ h.1,
    StacksDraft.FunctorialInjectiveResolutions.exists_resolutionFunctor C⟩

/-- **The functorial injective resolution of [Stacks, Tag 0141] respects the lower bound.**  The
resolution `F` of part (1) of
`CochainComplex.Plus.exists_functorial_injective_resolution_and_exists_resolutionFunctor` can be
chosen so that, in addition, it carries a complex vanishing in every degree below `a` to a complex
vanishing in every degree below `a`.

The construction of the tag already has this property — `F K` is the total complex of a double
complex whose column `p` vanishes when `K^p` does — and the statement records it, because a
right-derived-functor comparison read along the *rows* of `T(F K)` needs the resolution to be
concentrated in nonnegative degrees when `K` is. -/
public theorem exists_functorial_injective_resolution_isStrictlyGE
    (J : C ⥤ InjectiveObject C) (η : 𝟭 C ⟶ J ⋙ InjectiveObject.ι C)
    (hη : ∀ A, Mono (η.app A)) :
    ∃ (F : CochainComplex.Plus C ⥤ CochainComplex.Plus (InjectiveObject C))
      (α : 𝟭 (CochainComplex.Plus C) ⟶ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus),
      (∀ K, CochainComplex.Plus.quasiIso C (α.app K)) ∧
        ∀ (K : CochainComplex.Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
          ((F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus).obj K).obj.IsStrictlyGE a :=
  StacksDraft.FunctorialInjectiveResolutions.exists_functorial_injective_resolution_isStrictlyGE'
    J η hη

end CochainComplex.Plus

end
