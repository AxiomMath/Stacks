module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Constant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.FullyFaithful

/-!
# Gluing of small étale sheaves along an étale covering, with inverse images

Let `S` be a scheme of a big étale site `B` and `f k : X k ⟶ S` a family of étale morphisms
covering `S`, i.e. such that the corresponding objects of the small étale site of `S` cover its
final object. This file proves étale descent for sheaves with values in an arbitrary category `A`
on the small étale sites, phrased with the inverse images
`AlgebraicGeometry.smallEtaleSheafPullback` along the members and along the projections from the
overlaps, which are given by arbitrary pullback squares `O k l` (and `T k l m` for the triple
overlaps); the two inverse images of a sheaf to an overlap are identified by the composition
comparisons `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`.

* Morphisms are determined by, and glue from, compatible families of morphisms between the inverse
  images (Stacks 04TQ). No assumption is made on `A`.
* Sheaves glue from sheaves on the members with transition isomorphisms on the overlaps satisfying
  the cocycle condition on the triple overlaps (Stacks 04TR); this needs limits in `A`.
* In particular constant sheaves glue along isomorphisms of constant sheaves on the overlaps
  satisfying the cocycle condition, the inverse image of a constant sheaf being identified with the
  constant sheaf through `AlgebraicGeometry.smallEtaleConstantPullbackIso`.

The proof is `AlgebraicGeometry.SmallEtaleGluing.isEquivalence_toDescentData` and
`AlgebraicGeometry.SmallEtaleGluing.fullyFaithful_toDescentData`: descent for the pseudofunctor
`AlgebraicGeometry.SmallEtaleGluing.pseudofunctor` of small étale inverse images, obtained from
descent for sheaves on slice sites (Stacks 04TS) through the slice equivalences.

## Implementation notes

The members are given as a family of étale morphisms `f k : X k ⟶ S` of `B` with target `S`, and
the covering condition through the objects `AlgebraicGeometry.SmallEtale.ofEtaleHom B (f k)` of
the small étale site. For a family `V k` of objects of the small étale site the members are the
structure morphisms `(V k).obj.hom`; these have target `(V k).obj.right`-indexed copies of `S`
which are only definitionally `S`, and statements mixing the two spellings make the kernel unfold
the comparison isomorphisms, so the statements are phrased with the named family `f`
(for `V`, take `f k := (V k).obj.hom` with codomain `S`, e.g. through
`AlgebraicGeometry.SmallEtaleGluing.memberHom`).

## Main results

* `AlgebraicGeometry.smallEtaleSheafPullback_jointly_faithful`
* `AlgebraicGeometry.smallEtaleSheafPullback_exists_map_eq_of_isPullback`
* `AlgebraicGeometry.smallEtaleSheaf_exists_glue_of_isPullback`
* `AlgebraicGeometry.smallEtaleSheaf_exists_glue_constant_of_isPullback`

## References

* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (S : B.Scheme) {ι : Type*}

namespace SmallEtaleGluing

/-- The structure morphism of an object of the small étale site of `S`, with codomain `S`. -/
public abbrev memberHom (V : ι → SmallEtale B S.obj S.property) (k : ι) :
    (V k).obj.left ⟶ S :=
  (V k).obj.hom

/-- The structure morphism of an object of the small étale site is étale. -/
public instance etale_memberHom (V : ι → SmallEtale B S.obj S.property) (k : ι) :
    Etale (B.inclusion.map (memberHom B S V k)) :=
  (V k).property

/-- A covering of the final object of the small étale site of `S`, read through the structure
morphisms of its members. -/
public theorem sieve_ofEtaleHom_memberHom (V : ι → SmallEtale B S.obj S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (memberHom B S V k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) :=
  hV

/-- The canonical functor to descent data along a family of étale morphisms is the one along the
structure morphisms of the corresponding objects of the small étale site. -/
public theorem toDescentData_etale_eq {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S)
    [∀ k, Etale (B.inclusion.map (f k))] :
    (pseudofunctor B A).toDescentData (fun k => (SmallEtale.ofEtaleHom B (f k)).obj.hom) =
      (pseudofunctor B A).toDescentData f :=
  rfl

/-- **Étale descent along a family of étale morphisms covering `S`**, in the pseudofunctor of
small étale inverse images. -/
public theorem isEquivalence_toDescentData_of_etale [HasLimitsOfSize.{u + 1, u + 1} A]
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    ((pseudofunctor B A).toDescentData f).IsEquivalence :=
  isEquivalence_toDescentData B A S (fun k => SmallEtale.ofEtaleHom B (f k)) hf

/-- **Full faithfulness of étale descent along a family of étale morphisms covering `S`**, in
the pseudofunctor of small étale inverse images, for any coefficient category. -/
public theorem full_faithful_toDescentData_of_etale
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    ((pseudofunctor B A).toDescentData f).Full ∧
      ((pseudofunctor B A).toDescentData f).Faithful :=
  have h := fullyFaithful_toDescentData B A S (fun k => SmallEtale.ofEtaleHom B (f k)) hf
  ⟨h.full, h.faithful⟩

end SmallEtaleGluing

open SmallEtaleGluing

/-- **Morphisms of sheaves are determined étale locally (Stacks 04TQ, faithfulness).** Two
morphisms of sheaves on the small étale site of `S` which agree after inverse image along the
members of a family of étale morphisms covering `S` are equal. -/
public theorem smallEtaleSheafPullback_jointly_faithful
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) A} (ψ ψ' : F ⟶ G)
    (h : ∀ k, (smallEtaleSheafPullback B A (f k)).map ψ =
      (smallEtaleSheafPullback B A (f k)).map ψ') :
    ψ = ψ' := by
  have := (full_faithful_toDescentData_of_etale B A S f hf).2
  apply ((pseudofunctor B A).toDescentData f).map_injective
  ext k
  exact h k

/-- **Morphisms of sheaves glue étale locally (Stacks 04TQ).** Let `f k : X k ⟶ S` be a family of
étale morphisms covering `S`, with overlaps given by pullback squares `O k l` with projections
`p k l`, `q k l` and structure maps `r k l` to `S`. A family of morphisms `φ k` between the
inverse images of two sheaves along the `f k` which agree on the overlaps — after identifying the
two inverse images to an overlap through the comparisons
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` — is the family of inverse images of a
morphism of sheaves. No assumption is made on the coefficient category. -/
public theorem smallEtaleSheafPullback_exists_map_eq_of_isPullback
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) A}
    (O : ι → ι → B.Scheme) (p : ∀ k l, O k l ⟶ X k) (q : ∀ k l, O k l ⟶ X l)
    (r : ∀ k l, O k l ⟶ S) (hO : ∀ k l, IsPullback (p k l) (q k l) (f k) (f l))
    (hr₁ : ∀ k l, p k l ≫ f k = r k l) (hr₂ : ∀ k l, q k l ≫ f l = r k l)
    (φ : ∀ k, (smallEtaleSheafPullback B A (f k)).obj F ⟶
      (smallEtaleSheafPullback B A (f k)).obj G)
    (hφ : ∀ k l,
      (smallEtaleSheafPullbackCompIso' B A (p k l) (f k) (r k l) (hr₁ k l)).inv.app F ≫
          (smallEtaleSheafPullback B A (p k l)).map (φ k) ≫
        (smallEtaleSheafPullbackCompIso' B A (p k l) (f k) (r k l) (hr₁ k l)).hom.app G =
      (smallEtaleSheafPullbackCompIso' B A (q k l) (f l) (r k l) (hr₂ k l)).inv.app F ≫
          (smallEtaleSheafPullback B A (q k l)).map (φ l) ≫
        (smallEtaleSheafPullbackCompIso' B A (q k l) (f l) (r k l) (hr₂ k l)).hom.app G) :
    ∃ ψ : F ⟶ G, ∀ k, (smallEtaleSheafPullback B A (f k)).map ψ = φ k :=
  have := (full_faithful_toDescentData_of_etale B A S f hf).1
  Pseudofunctor.exists_map_eq_of_full_toDescentData_of_isPullback (pseudofunctor B A)
    f F G O p q r hO hr₁ hr₂ φ
    (fun k l => toDescentData_comm_of_comp B A f (p k l) (q k l) (r k l) (hr₁ k l) (hr₂ k l)
      (φ k) (φ l) (hφ k l))

/-- **Sheaves glue étale locally (Stacks 04TR).** Let `f k : X k ⟶ S` be a family of étale
morphisms covering `S`, with overlaps given by pullback squares `O k l` (projections `p k l`,
`q k l`, structure maps `r k l`) and triple overlaps given by pullback squares `T k l m` of
`q k l` and `p l m` (projections `a₁₂`, `a₂₃`, a map `a₁₃` to `O k m`, and maps `t₁`, `t₂`, `t₃`
to the members). Sheaves `G k` on the members, with isomorphisms `θ k l` between their inverse
images to the overlaps satisfying the cocycle condition on the triple overlaps — the inverse
images being identified through the comparisons
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`, see
`AlgebraicGeometry.SmallEtaleGluing.pullbackTransition` — glue: there is a sheaf `F` on the small
étale site of `S` with isomorphisms `ε k` from its inverse images to the `G k` inducing the
`θ k l`. -/
public theorem smallEtaleSheaf_exists_glue_of_isPullback [HasLimitsOfSize.{u + 1, u + 1} A]
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (O : ι → ι → B.Scheme) (p : ∀ k l, O k l ⟶ X k) (q : ∀ k l, O k l ⟶ X l)
    (r : ∀ k l, O k l ⟶ S) (hO : ∀ k l, IsPullback (p k l) (q k l) (f k) (f l))
    (hr₁ : ∀ k l, p k l ≫ f k = r k l) (hr₂ : ∀ k l, q k l ≫ f l = r k l)
    (T : ι → ι → ι → B.Scheme) (a₁₂ : ∀ k l m, T k l m ⟶ O k l)
    (a₂₃ : ∀ k l m, T k l m ⟶ O l m) (a₁₃ : ∀ k l m, T k l m ⟶ O k m)
    (hT : ∀ k l m, IsPullback (a₁₂ k l m) (a₂₃ k l m) (q k l) (p l m))
    (t₁ : ∀ k l m, T k l m ⟶ X k) (t₂ : ∀ k l m, T k l m ⟶ X l) (t₃ : ∀ k l m, T k l m ⟶ X m)
    (h₁₂₁ : ∀ k l m, a₁₂ k l m ≫ p k l = t₁ k l m) (h₁₂₂ : ∀ k l m, a₁₂ k l m ≫ q k l = t₂ k l m)
    (h₂₃₁ : ∀ k l m, a₂₃ k l m ≫ p l m = t₂ k l m) (h₂₃₂ : ∀ k l m, a₂₃ k l m ≫ q l m = t₃ k l m)
    (h₁₃₁ : ∀ k l m, a₁₃ k l m ≫ p k m = t₁ k l m) (h₁₃₂ : ∀ k l m, a₁₃ k l m ≫ q k m = t₃ k l m)
    (G : ∀ k, Sheaf (SmallEtale.topology B (X k).obj (X k).property) A)
    (θ : ∀ k l, (smallEtaleSheafPullback B A (p k l)).obj (G k) ≅
      (smallEtaleSheafPullback B A (q k l)).obj (G l))
    (hθ : ∀ k l m,
      pullbackTransition B A (a₁₂ k l m) (θ k l) (t₁ k l m) (t₂ k l m) (h₁₂₁ k l m)
          (h₁₂₂ k l m) ≪≫
        pullbackTransition B A (a₂₃ k l m) (θ l m) (t₂ k l m) (t₃ k l m) (h₂₃₁ k l m)
          (h₂₃₂ k l m) =
      pullbackTransition B A (a₁₃ k l m) (θ k m) (t₁ k l m) (t₃ k l m) (h₁₃₁ k l m)
        (h₁₃₂ k l m)) :
    ∃ (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
      (ε : ∀ k, (smallEtaleSheafPullback B A (f k)).obj F ≅ G k),
      ∀ k l, (smallEtaleSheafPullback B A (p k l)).mapIso (ε k).symm ≪≫
          (smallEtaleSheafPullbackCompIso' B A (p k l) (f k) (r k l) (hr₁ k l)).app F ≪≫
          (smallEtaleSheafPullbackCompIso' B A (q k l) (f l) (r k l) (hr₂ k l)).symm.app F ≪≫
          (smallEtaleSheafPullback B A (q k l)).mapIso (ε l) = θ k l := by
  have := isEquivalence_toDescentData_of_etale B A S f hf
  obtain ⟨M, ε, hε⟩ := Pseudofunctor.exists_iso_of_isEquivalence_toDescentData_of_isPullback
    (pseudofunctor B A) f O p q r hO hr₁ hr₂ T a₁₂ a₂₃ a₁₃ hT t₁ t₂ t₃ h₁₂₁ h₁₂₂ h₂₃₁ h₂₃₂
    h₁₃₁ h₁₃₂ G θ
    (fun k l m => pullHom_comp_of_cocycle B A (a₁₂ k l m) (a₂₃ k l m) (a₁₃ k l m) (t₁ k l m)
      (t₂ k l m) (t₃ k l m) (h₁₂₁ k l m) (h₁₂₂ k l m) (h₂₃₁ k l m) (h₂₃₂ k l m) (h₁₃₁ k l m)
      (h₁₃₂ k l m) (θ k l) (θ l m) (θ k m) (hθ k l m))
  exact ⟨M, ε, fun k l => iso_eq_of_comm B A f (p k l) (q k l) (r k l) (hr₁ k l) (hr₂ k l) M
    (ε k) (ε l) (θ k l) (hε k l)⟩

/-- **Constant sheaves glue étale locally (Stacks 04TR).** In the situation of
`AlgebraicGeometry.smallEtaleSheaf_exists_glue_of_isPullback`, isomorphisms `τ k l` between the
constant sheaves on `E k` and on `E l` over the overlaps, satisfying the cocycle condition on the
triple overlaps after transport along the maps `a` to the overlaps
(`τ^T(a) = (cP a).symm ≪≫ a⁻¹ τ ≪≫ cP a`, with `cP` the comparison
`AlgebraicGeometry.smallEtaleConstantPullbackIso`), glue: there is a sheaf `F` on the small étale
site of `S` with isomorphisms `ε k` from its inverse images to the constant sheaves on `E k`
inducing the `τ k l`. -/
public theorem smallEtaleSheaf_exists_glue_constant_of_isPullback
    [HasLimitsOfSize.{u + 1, u + 1} A]
    [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (O : ι → ι → B.Scheme) (p : ∀ k l, O k l ⟶ X k) (q : ∀ k l, O k l ⟶ X l)
    (r : ∀ k l, O k l ⟶ S) (hO : ∀ k l, IsPullback (p k l) (q k l) (f k) (f l))
    (hr₁ : ∀ k l, p k l ≫ f k = r k l) (hr₂ : ∀ k l, q k l ≫ f l = r k l)
    (T : ι → ι → ι → B.Scheme) (a₁₂ : ∀ k l m, T k l m ⟶ O k l)
    (a₂₃ : ∀ k l m, T k l m ⟶ O l m) (a₁₃ : ∀ k l m, T k l m ⟶ O k m)
    (hT : ∀ k l m, IsPullback (a₁₂ k l m) (a₂₃ k l m) (q k l) (p l m))
    (t₁ : ∀ k l m, T k l m ⟶ X k) (t₂ : ∀ k l m, T k l m ⟶ X l) (t₃ : ∀ k l m, T k l m ⟶ X m)
    (h₁₂₁ : ∀ k l m, a₁₂ k l m ≫ p k l = t₁ k l m) (h₁₂₂ : ∀ k l m, a₁₂ k l m ≫ q k l = t₂ k l m)
    (h₂₃₁ : ∀ k l m, a₂₃ k l m ≫ p l m = t₂ k l m) (h₂₃₂ : ∀ k l m, a₂₃ k l m ≫ q l m = t₃ k l m)
    (h₁₃₁ : ∀ k l m, a₁₃ k l m ≫ p k m = t₁ k l m) (h₁₃₂ : ∀ k l m, a₁₃ k l m ≫ q k m = t₃ k l m)
    (E : ι → A)
    (τ : ∀ k l, (constantSheaf (SmallEtale.topology B (O k l).obj (O k l).property) A).obj (E k) ≅
      (constantSheaf (SmallEtale.topology B (O k l).obj (O k l).property) A).obj (E l))
    (hτ : ∀ k l m,
      ((smallEtaleConstantPullbackIso B A (a₁₂ k l m) (E k)).symm ≪≫
          (smallEtaleSheafPullback B A (a₁₂ k l m)).mapIso (τ k l) ≪≫
          smallEtaleConstantPullbackIso B A (a₁₂ k l m) (E l)) ≪≫
        ((smallEtaleConstantPullbackIso B A (a₂₃ k l m) (E l)).symm ≪≫
          (smallEtaleSheafPullback B A (a₂₃ k l m)).mapIso (τ l m) ≪≫
          smallEtaleConstantPullbackIso B A (a₂₃ k l m) (E m)) =
      (smallEtaleConstantPullbackIso B A (a₁₃ k l m) (E k)).symm ≪≫
        (smallEtaleSheafPullback B A (a₁₃ k l m)).mapIso (τ k m) ≪≫
        smallEtaleConstantPullbackIso B A (a₁₃ k l m) (E m)) :
    ∃ (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
      (ε : ∀ k, (smallEtaleSheafPullback B A (f k)).obj F ≅
        (constantSheaf (SmallEtale.topology B (X k).obj (X k).property) A).obj (E k)),
      ∀ k l, (smallEtaleConstantPullbackIso B A (p k l) (E k)).symm ≪≫
          (smallEtaleSheafPullback B A (p k l)).mapIso (ε k).symm ≪≫
          (smallEtaleSheafPullbackCompIso' B A (p k l) (f k) (r k l) (hr₁ k l)).app F ≪≫
          (smallEtaleSheafPullbackCompIso' B A (q k l) (f l) (r k l) (hr₂ k l)).symm.app F ≪≫
          (smallEtaleSheafPullback B A (q k l)).mapIso (ε l) ≪≫
          smallEtaleConstantPullbackIso B A (q k l) (E l) = τ k l := by
  obtain ⟨F, ε, hε⟩ := smallEtaleSheaf_exists_glue_of_isPullback B A S f hf O p q r hO hr₁ hr₂
    T a₁₂ a₂₃ a₁₃ hT t₁ t₂ t₃ h₁₂₁ h₁₂₂ h₂₃₁ h₂₃₂ h₁₃₁ h₁₃₂
    (fun k => (constantSheaf (SmallEtale.topology B (X k).obj (X k).property) A).obj (E k))
    (fun k l => smallEtaleConstantPullbackIso B A (p k l) (E k) ≪≫ τ k l ≪≫
      (smallEtaleConstantPullbackIso B A (q k l) (E l)).symm)
    (fun k l m => by
      rw [pullbackTransition_constant, pullbackTransition_constant, pullbackTransition_constant]
      have h := hτ k l m
      simp only [constantTransport]
      rw [← h]
      ext
      simp)
  refine ⟨F, ε, fun k l => ?_⟩
  have h2 := congrArg (fun x => (smallEtaleConstantPullbackIso B A (p k l) (E k)).symm ≪≫ x ≪≫
    smallEtaleConstantPullbackIso B A (q k l) (E l)) (hε k l)
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
    using h2

end AlgebraicGeometry

end
