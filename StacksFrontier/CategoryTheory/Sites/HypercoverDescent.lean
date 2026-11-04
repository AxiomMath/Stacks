module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence

/-!
# Levels and face maps of a hypercovering are coverings

Let `C` be a site with fibre products given by a pretopology `J`, let `X : C` and let `K` be a
hypercovering of `X`, that is, a simplicial object of `SR(C, X) = FormalCoproduct (Over X)`
whose degree-zero term covers `X` and whose canonical morphism to each successive coskeleton is
covering. This file proves Tag 0DEQ: every level `K_n` covers `X`, and every face map
`δ i : K_{n + 1} ⟶ K_n` is covering.

The route is the source's. Part (2) is Tag 01GN applied to the `n + 2` face inclusions
`Δ[n] ⟶ Δ[n + 1]`, using the identification `Hom(Δ[m], K)₀ = K_m` of Tag 017L; part (1)
follows from part (2) by composing `K_n ⟶ K_{n - 1} ⟶ … ⟶ K_0 ⟶ {X → X}` and applying
Tag 01G4 (1).

## Main definitions

* `homPresheaf K A`: the presheaf `Y ↦ Mor(Y × A, K)` on the ambient category, of which
  `Hom(A, K)₀` is a representing object.
* `representableByHom` and `representableByIso`: the canonical comparison morphism, and
  isomorphism, between two representing objects of one presheaf.
* `transportHomPresheaf`: transport of a representing datum for `homPresheaf K B` along an
  isomorphism `A ≅ B` of simplicial sets.

## Main results

* `representableByHom_comp_induced`: the restriction morphism induced by a morphism of
  simplicial sets is independent of the chosen representing data, up to the comparison
  isomorphisms. This is what lets the covering morphism produced by Tag 01GN — which is
  phrased for the *chosen* `Hom` objects — be transported to the face map of `K`, which is the
  same morphism for the Yoneda representing data `K_n` and `K_{n + 1}`.
* `stdSimplexDelta_comp_yonedaEquiv_symm_id`: restricting the universal element of `K_{n + 1}`
  along the `i`-th face inclusion gives the universal element of `K_n` twisted by `δ i`. This
  is the computation that makes the face map appear.
* `isCoveringOver_delta` is Tag 0DEQ (2) and `isCoveringOver_terminalFrom` is Tag 0DEQ (1).

## Implementation notes

The source states part (1) as "`K_n` is a covering of `X`"; since each object of `SR(C, X)` is
a family of morphisms with target `X`, this is the statement that the unique morphism from
`K_n` to the terminal object `{X → X}` of `SR(C, X)` is covering, which is the form used here
(and the form the source itself notes after Definition 25.3.3).

Part (2) is indexed so that the degree is `n + 1`: the source's range `0 ≤ i ≤ n` for
`d^n_i : K_n → K_{n - 1}` with `n ≥ 1` becomes `i : Fin (n + 2)` for
`K.δ i : K_{n + 1} ⟶ K_n`, which is Mathlib's indexing of the face maps.

The hypothesis `Precoverage.IsStableUnderComposition J.toPrecoverage` is the indexed-family
composition axiom of a site (Tag 00VH (2)). Mathlib's `Pretopology` only asks that composites
of *presieves* be covering, which does not give the axiom when an indexed family repeats an
arrow, so the axiom has to be carried separately; it is used through Tag 01G4 (1), which the
source's proof of both parts invokes. The `i`-th face of `Δ[n + 1]` is Mathlib's
`SSet.stdSimplex.face {i}ᶜ`, isomorphic to `Δ[n]` by
`SSet.stdSimplex.faceSingletonComplIso`.

## References

* [Stacks Project, Tag 0DEQ](https://stacks.math.columbia.edu/tag/0DEQ)
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Comparing representing objects of the `Hom` presheaves -/

section Representable

variable {D : Type u'} [Category.{v'} D]

/-- The presheaf `X ↦ Mor(X × A, K)` on `D`, equally `X ↦ Mor(A, K ⋙ Mor(X, -))`, of which
`Hom(A, K)₀` is a representing object. -/
abbrev homPresheaf (K : SimplicialObject D) (A : SSet.{v'}) : Dᵒᵖ ⥤ Type v' :=
  coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K ⋙
    coyoneda.obj (op A)

variable {F : Dᵒᵖ ⥤ Type v'} {M M' : D}

/-- The comparison morphism between two representing objects of the same presheaf. -/
noncomputable def representableByHom (h : F.RepresentableBy M) (h' : F.RepresentableBy M') :
    M ⟶ M' :=
  h'.homEquiv.symm (h.homEquiv (𝟙 M))

/-- The defining property of the comparison morphism: it mediates between the two
representing data. -/
theorem homEquiv_comp_representableByHom (h : F.RepresentableBy M) (h' : F.RepresentableBy M')
    {Y : D} (u : Y ⟶ M) : h'.homEquiv (u ≫ representableByHom h h') = h.homEquiv u := by
  rw [h'.homEquiv_comp, representableByHom, Equiv.apply_symm_apply,
    ← h.homEquiv_comp u (𝟙 M), Category.comp_id]

/-- The comparison morphism at the identity. -/
theorem homEquiv_representableByHom (h : F.RepresentableBy M) (h' : F.RepresentableBy M') :
    h'.homEquiv (representableByHom h h') = h.homEquiv (𝟙 M) := by
  have h₀ := homEquiv_comp_representableByHom h h' (𝟙 M)
  rwa [Category.id_comp] at h₀

/-- Any two representing objects of a presheaf are canonically isomorphic. -/
noncomputable def representableByIso (h : F.RepresentableBy M) (h' : F.RepresentableBy M') :
    M ≅ M' where
  hom := representableByHom h h'
  inv := representableByHom h' h
  hom_inv_id := h.homEquiv.injective (by
    rw [homEquiv_comp_representableByHom h' h, representableByHom, Equiv.apply_symm_apply])
  inv_hom_id := h'.homEquiv.injective (by
    rw [homEquiv_comp_representableByHom h h', representableByHom, Equiv.apply_symm_apply])

/-- The comparison morphism between two representing objects of the same presheaf is an
isomorphism. -/
instance isIso_representableByHom (h : F.RepresentableBy M) (h' : F.RepresentableBy M') :
    IsIso (representableByHom h h') :=
  (representableByIso h h').isIso_hom

/-- A representing datum for one `Hom` presheaf transports along an isomorphism of simplicial
sets to one for the other, with the same representing object. -/
noncomputable def transportHomPresheaf {A B : SSet.{v'}} (e : A ≅ B) (K : SimplicialObject D)
    {H : D} (hB : (homPresheaf K B).RepresentableBy H) :
    (homPresheaf K A).RepresentableBy H :=
  hB.ofIso (NatIso.ofComponents
    (fun Y ↦ (coyoneda.mapIso e.op).app ((coyoneda ⋙
      (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K).obj Y))
    (fun {_ _} f ↦ (coyoneda.mapIso e.op).hom.naturality
      ((coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K).map f)))

/-- The transported representing datum precomposes with the isomorphism. -/
theorem transportHomPresheaf_homEquiv {A B : SSet.{v'}} (e : A ≅ B) (K : SimplicialObject D)
    {H : D} (hB : (homPresheaf K B).RepresentableBy H) {Y : D} (g : Y ⟶ H) :
    (transportHomPresheaf e K hB).homEquiv g = e.hom ≫ hB.homEquiv g := by
  simp [transportHomPresheaf, Functor.RepresentableBy.ofIso]

/-- **The comparison square for restriction of `Hom` objects.** For a morphism `i : A ⟶ B` of
simplicial sets and two pairs of representing data for the presheaves represented by
`Hom(A, K)₀` and `Hom(B, K)₀`, the two induced restriction morphisms agree up to the canonical
comparison isomorphisms. -/
theorem representableByHom_comp_induced {A B : SSet.{v'}} {K : SimplicialObject D} (i : A ⟶ B)
    {MA MA' MB MB' : D} (hA : (homPresheaf K A).RepresentableBy MA)
    (hA' : (homPresheaf K A).RepresentableBy MA')
    (hB : (homPresheaf K B).RepresentableBy MB)
    (hB' : (homPresheaf K B).RepresentableBy MB') :
    representableByHom hB hB' ≫ hA'.homEquiv.symm (i ≫ hB'.homEquiv (𝟙 MB')) =
      hA.homEquiv.symm (i ≫ hB.homEquiv (𝟙 MB)) ≫ representableByHom hA hA' := by
  apply hA'.homEquiv.injective
  rw [homEquiv_comp_representableByHom hA hA', Equiv.apply_symm_apply, hA'.homEquiv_comp,
    Equiv.apply_symm_apply]
  have hstep : (homPresheaf K B).map (representableByHom hB hB').op
      (hB'.homEquiv (𝟙 MB')) = hB.homEquiv (𝟙 MB) := by
    rw [← hB'.homEquiv_comp, Category.comp_id, homEquiv_representableByHom hB hB']
  show i ≫ (homPresheaf K B).map (representableByHom hB hB').op
    (hB'.homEquiv (𝟙 MB')) = _
  rw [hstep]

end Representable

/-! ### Tag 0DEQ: the levels and face maps of a hypercovering -/

section Degeneracy

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C)
  [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
  (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-- The universal element of the Yoneda representation of `K_{n + 1}`, restricted along the
`i`-th face inclusion `Δ[n] ⟶ Δ[n + 1]`, is the universal element of `K_n` twisted by the face
map `δ i` of `K`. -/
theorem stdSimplexDelta_comp_yonedaEquiv_symm_id {D : Type u'} [Category.{v'} D]
    (L : SimplicialObject D) (n : ℕ) (i : Fin (n + 2)) :
    SSet.stdSimplex.δ i ≫
        (SSet.yonedaEquiv (X := L ⋙ coyoneda.obj (op (L.obj (op ⦋n + 1⦌))))
          (n := ⦋n + 1⦌)).symm (𝟙 (L.obj (op ⦋n + 1⦌))) =
      (SSet.yonedaEquiv (X := L ⋙ coyoneda.obj (op (L.obj (op ⦋n + 1⦌))))
        (n := ⦋n⦌)).symm (L.δ i) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  exact Category.id_comp _

/-- **Stacks Project, Tag 0DEQ, part (2).** Every face map of a hypercovering of `X` is a
covering morphism in `SR(C, X)`. -/
@[stacks 0DEQ "part (2)"]
theorem isCoveringOver_delta (hK : IsHypercovering J K) (n : ℕ) (i : Fin (n + 2)) :
    IsCoveringOver J (K.δ i) := by
  classical
  -- The `i`-th face of `Δ[n + 1]`, a copy of `Δ[n]`.
  set U : (Δ[n + 1] : SSet.{max w v}).Subcomplex := SSet.stdSimplex.face {i}ᶜ with hU
  set e : (Δ[n] : SSet.{max w v}) ≅ (U : SSet.{max w v}) :=
    SSet.stdSimplex.faceSingletonComplIso i with he
  have _ : SSet.Nonempty (U : SSet.{max w v}) := SSet.nonempty_of_hom e.hom
  -- Four representing data: the Yoneda ones on `K`, and the chosen `Hom` objects.
  let hA : (homPresheaf K (U : SSet.{max w v})).RepresentableBy (K.obj (op ⦋n⦌)) :=
    transportHomPresheaf e.symm K (representableByStdSimplex K n)
  let hA' : (homPresheaf K (U : SSet.{max w v})).RepresentableBy
      ((homFromSSet (U : SSet.{max w v}) K).obj (op ⦋0⦌)) :=
    representableByAppZero _ K _ (homFromSSetIsHom (U : SSet.{max w v}) K)
  let hB : (homPresheaf K (Δ[n + 1] : SSet.{max w v})).RepresentableBy
      (K.obj (op ⦋n + 1⦌)) := representableByStdSimplex K (n + 1)
  let hB' : (homPresheaf K (Δ[n + 1] : SSet.{max w v})).RepresentableBy
      ((homFromSSet (Δ[n + 1] : SSet.{max w v}) K).obj (op ⦋0⦌)) :=
    representableByAppZero _ K _ (homFromSSetIsHom (Δ[n + 1] : SSet.{max w v}) K)
  -- Tag 01GN: restriction along the face inclusion is a covering.
  have hcov : IsCoveringOver J ((homFromSSetRestriction U.ι K).app (op ⦋0⦌)) :=
    isCoveringOver_homFromSSetRestriction_app_zero J X K hK (Δ[n + 1] : SSet.{max w v}) U
  rw [homFromSSetRestriction_eq_homFromSSetMap, homFromSSetMap_app_zero] at hcov
  -- That restriction morphism is the face map, up to the comparison isomorphisms.
  have hface : hA.homEquiv.symm (U.ι ≫ hB.homEquiv (𝟙 (K.obj (op ⦋n + 1⦌)))) = K.δ i := by
    apply hA.homEquiv.injective
    rw [Equiv.apply_symm_apply]
    show U.ι ≫ (SSet.yonedaEquiv
        (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋n + 1⦌)))) (n := ⦋n + 1⦌)).symm
          (𝟙 (K.obj (op ⦋n + 1⦌))) =
      (transportHomPresheaf e.symm K (representableByStdSimplex K n)).homEquiv (K.δ i)
    rw [transportHomPresheaf_homEquiv]
    show _ = e.inv ≫ (SSet.yonedaEquiv
      (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋n + 1⦌)))) (n := ⦋n⦌)).symm (K.δ i)
    rw [← stdSimplexDelta_comp_yonedaEquiv_symm_id K n i,
      show (SSet.stdSimplex.δ i : (Δ[n] : SSet.{max w v}) ⟶ Δ[n + 1]) = e.hom ≫ U.ι from
        (SSet.stdSimplex.faceSingletonComplIso_hom_ι i).symm]
    simp
  have hsq := representableByHom_comp_induced U.ι hA hA' hB hB'
  rw [hface] at hsq
  -- Strip the comparison isomorphisms.
  have hfac : K.δ i = representableByHom hB hB' ≫
      hA'.homEquiv.symm (U.ι ≫ hB'.homEquiv (𝟙 _)) ≫ inv (representableByHom hA hA') := by
    rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hfac]
  exact IsCoveringOver.comp J (IsCoveringOver.of_isIso J _) (hcov.comp_isIso J _)

/-- **Stacks Project, Tag 0DEQ, part (1).** Every level of a hypercovering of `X` is a
covering of `X`. -/
@[stacks 0DEQ "part (1)"]
theorem isCoveringOver_terminalFrom (hK : IsHypercovering J K) (n : ℕ) :
    IsCoveringOver J (terminal.from (K.obj (op ⦋n⦌))) := by
  induction n with
  | zero => exact hK.1
  | succ n ih =>
    have hfac : terminal.from (K.obj (op ⦋n + 1⦌)) =
        K.δ (0 : Fin (n + 2)) ≫ terminal.from (K.obj (op ⦋n⦌)) := terminal.hom_ext _ _
    rw [hfac]
    exact IsCoveringOver.comp J (isCoveringOver_delta J K hK n 0) ih

end Degeneracy

end Stacks.CategoryTheory.Hypercovering

end
