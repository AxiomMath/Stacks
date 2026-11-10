module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Brown representability for a triangulated category with a set of generators

Let `𝒟` be a triangulated category with direct sums and let `E : ι → 𝒟` be a family of objects
of `𝒟` such that

1. every nonzero object `X` of `𝒟` receives a nonzero morphism `E i ⟶ X` from some member of
   the family, and
2. for every family `X : ℕ → 𝒟`, every morphism `α : E i ⟶ ∐ X` into its direct sum factors as
   `α = γ ≫ Sigma.map β` for some `j : ℕ → ι`, morphisms `β n : E (j n) ⟶ X n` and
   `γ : E i ⟶ ∐ fun n ↦ E (j n)`.

Then every contravariant cohomological functor `H : 𝒟ᵒᵖ ⥤ AddCommGrpCat` which transforms
direct sums into products is representable: there is an object `X` of `𝒟` and an isomorphism
`Hom_𝒟(-, X) ≅ H` of abelian group valued functors. This is a weak form of Brown
representability; the representing object is built as the homotopy colimit of a sequence
`X₁ → X₂ → ⋯` starting from a direct sum of members of the family. Each step takes the cone
of a map from another such direct sum, killing the evaluation kernel on the generators.

## Main results

* `exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma`: the weak Brown
  representability theorem stated above.

## Implementation notes

A contravariant cohomological functor on `𝒟` is a homological functor on `𝒟ᵒᵖ`, which is
Mathlib's convention for this notion: `preadditiveYoneda.obj X : 𝒟ᵒᵖ ⥤ AddCommGrpCat` is
`Functor.IsHomological`. Since a direct sum in `𝒟` is a product in `𝒟ᵒᵖ`, "`H` transforms direct
sums into products" is `Limits.PreservesLimitsOfShape (Discrete J) H`, asked for every index type
`J` of the size of the direct sums that `𝒟` is assumed to have; the countable case used in
hypothesis (2) follows from it along `Discrete ℕ ≌ Discrete (ULift ℕ)`, as does the existence of
the countable direct sums themselves along `Limits.hasCoproducts_shrink`.

For telescope injectivity, cover each tower term by a coproduct of generators. Finite partial
sums give a left inverse on these covers, and exactness of coproducts of distinguished triangles,
together with condition (2), allows descent through their kernels. Only evaluation-kernel maps
are killed. The construction retains a map from any initial element which is surjective on the
generators. Repeating it on a cone or a binary direct sum then gives injectivity or surjectivity
of evaluation on every object, since the shifted generators detect isomorphisms.

The source's *set* `ℰ` of objects is a family `E : ι → 𝒟` indexed by a type `ι : Type w`, and not
an `ObjectProperty 𝒟`; the conditions only refer to `ℰ` through its members, so nothing is lost,
and this is where the source's smallness requirement on `ℰ` lives. It is essential rather than
cosmetic: conditions (1) and (2) hold for the family of *all* objects of `𝒟` (take `E := X` and
`f := 𝟙 X` in (1), and `Eₙ := Xₙ`, `βₙ := 𝟙 Xₙ`, `γ := α` in (2)), so if `ℰ` were allowed to be
indexed by `Ob 𝒟` the hypotheses would carry no information — and the direct sums used to
construct the representing object would then be indexed by types as large as `Ob 𝒟`, which
categories such as the derived category of a ring do not possess. Asking instead for coproducts
of families indexed by `Type (max w v)`, with `v` the universe of the morphisms of `𝒟`, is the
size condition under which the construction runs, and it is satisfied in the intended examples:
for `𝒟 = D(Mod R)` one may take `ι := ℤ` and `E n := R⟦n⟧`, an index type in `Type 0`, so that
`max w v = v` and only the direct sums that `D(Mod R)` has are asked for.

On faithfulness. (1) `E`, `hE` and `hE'` are conditions (1) and (2) and
are what make the representing object exist, the coproducts are the source's "with direct sums"
and are needed already to state (2), and the two hypotheses on `H` are its being cohomological
and transforming direct sums into products; `IsTriangulated 𝒟` is the source's word
"triangulated". The proof below in fact needs only the pretriangulated axioms; the
statement retains the source's triangulated hypothesis.
(2) The category, the family and the functor are the source's `𝒟`, `ℰ` and `H`, with `H` valued
in abelian groups as in the source, and the countable sums in (2) are indexed by `ℕ` as there.
(3) The conclusion is the source's "`H` is representable"; it is pinned as an isomorphism of
`AddCommGrpCat`-valued functors `preadditiveYoneda.obj X ≅ H`, i.e. as representability in the
additive sense, which for a functor with values in abelian groups is the meaning of the word and
is stronger than representability of the underlying set valued functor.
(4) The instantiation is not degenerate: with `𝒟 = D(Mod R)`, `ι = ℤ` and `E n = R⟦n⟧` both
hypotheses on `E` hold — (1) because a nonzero object `X` has `Hⁱ X ≠ 0` for some `i`, and
`Hom(R⟦-i⟧, X) = Hⁱ X` as `R` is free, so some `E (-i) ⟶ X` is nonzero; and (2) because `R⟦n⟧` is
compact, so `α : R⟦n⟧ ⟶ ∐ X` is a finite sum `∑_{m ∈ S} βₘ ≫ Sigma.ι X m` with `βₘ : R⟦n⟧ ⟶ Xₘ`,
and taking `j` constant equal to `n`, `β` those `βₘ` extended by zero outside `S` and
`γ = ∑_{m ∈ S} Sigma.ι _ m` the diagonal of `S` gives `α = γ ≫ Sigma.map β`. The conclusion, on
the other hand, fails for cohomological functors that do not transform direct sums into products,
so neither the hypotheses nor the conclusion are vacuous. The shifts in that family are what make
(1) hold, and a family without them does not do so: `ι = PUnit` with `E _ = R` fails (1), because
`Hom_{D(Mod R)}(R, X) = H⁰ X` vanishes on a nonzero complex concentrated in a nonzero degree,
while condition (1) as stated contains no shifts of its own. This matches the source, whose proof
replaces `ℰ` by `⋃_{i ∈ ℤ} ℰ[i]` only *after* assuming (1).

## References

* [Stacks project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG), a weak version of
  Theorem A of H. Krause, *A Brown representability theorem via coherent functors*.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.Pretriangulated

section Evaluation

variable {D : Type u} [Category.{v} D] (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})

private lemma map_op_sub_apply [Preadditive D] [H.Additive] {X Y : D} (f g : X ⟶ Y)
    (x : H.obj (op Y)) : H.map (f - g).op x = H.map f.op x - H.map g.op x := by
  simp

/-- Composition in the source of a contravariant functor acts on elements by successive
application. -/
private lemma map_op_comp_apply {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (x : H.obj (op Z)) :
    H.map (f ≫ g).op x = H.map f.op (H.map g.op x) := by
  simp

/-- Two morphisms inducing the same map on an element differ by a morphism killing it. -/
private lemma map_op_sub_eq_zero [Preadditive D] [H.Additive] {X Y : D} {f g : X ⟶ Y}
    {x : H.obj (op Y)} (h : H.map f.op x = H.map g.op x) : H.map (f - g).op x = 0 := by
  rw [map_op_sub_apply, h, sub_self]

/-- For a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` and a homological functor
`H : Dᵒᵖ ⥤ Ab`, an element of `H(Y)` killed by `H(X ⟶ Y)` comes from `H(Z)`. -/
private lemma exists_map_op_eq_of_distTriang [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [H.IsHomological]
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang D) (y : H.obj (op Y)) (hy : H.map f.op y = 0) :
    ∃ z : H.obj (op Z), H.map g.op z = y :=
  (ShortComplex.ab_exact_iff _).1 (H.map_distinguished_op_exact _ hT) y hy

end Evaluation

/- Condition (2) implies Krause's condition (G2): countable sums of maps which are
surjective on morphisms from the generators retain that property. -/
section Factorization

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasCountableCoproducts D] {ι : Type w} (E : ι → D)
  (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
    (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
      α = γ ≫ Limits.Sigma.map β)

include hE'

omit [Preadditive D] in
private lemma surjective_sigma_of_factorsThroughSigma
    (X Y : ℕ → D) (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n i, Function.Surjective (fun g : E i ⟶ X n ↦ g ≫ f n)) (i : ι) :
    Function.Surjective (fun g : E i ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f) := by
  intro α
  obtain ⟨j, β, γ, rfl⟩ := hE' Y i α
  choose δ hδ using fun n ↦ hf n (j n) (β n)
  dsimp only at hδ
  refine ⟨γ ≫ Limits.Sigma.map δ, ?_⟩
  simp [Limits.Sigma.map_comp_map, hδ]

end Factorization

section EquivalenceFactorization

variable {D : Type u} [Category.{v} D] [HasCoproducts.{0} D] {ι : Type w} (E : ι → D)

private lemma equivalence_factorsThroughSigma
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
      (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (e : D ≌ D) (X : ℕ → D) (i : ι) (α : e.functor.obj (E i) ⟶ ∐ X) :
    ∃ (j : ℕ → ι) (β : ∀ n, e.functor.obj (E (j n)) ⟶ X n)
      (γ : e.functor.obj (E i) ⟶ ∐ fun n ↦ e.functor.obj (E (j n))),
      α = γ ≫ Limits.Sigma.map β := by
  let Y : ℕ → D := fun n ↦ e.inverse.obj (X n)
  let c : e.functor.obj (∐ Y) ≅ ∐ X :=
    PreservesCoproduct.iso e.functor Y ≪≫ Sigma.mapIso (fun n ↦ e.counitIso.app (X n))
  let α' : E i ⟶ ∐ Y := e.functor.preimage (α ≫ c.inv)
  obtain ⟨j, β, γ, hγ⟩ := hE' Y i α'
  let β' (n : ℕ) := e.functor.map (β n) ≫ e.counitIso.hom.app (X n)
  let c' := PreservesCoproduct.iso e.functor (fun n ↦ E (j n))
  have hc : e.functor.map (Limits.Sigma.map β) ≫ c.hom =
      c'.hom ≫ Limits.Sigma.map β' := by
    apply (cancel_epi c'.inv).1
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    have eh (Z : ℕ → D) : (PreservesCoproduct.iso e.functor Z).hom =
        inv (sigmaComparison e.functor Z) :=
      (IsIso.Iso.inv_inv (PreservesCoproduct.iso e.functor Z)).symm
    simp only [c, c', Iso.trans_hom, PreservesCoproduct.inv_hom,
      ι_comp_sigmaComparison_assoc, eh]
    rw [← Category.assoc, ← e.functor.map_comp, Limits.Sigma.ι_map, e.functor.map_comp]
    simp [Category.assoc, β']
  refine ⟨j, β', e.functor.map γ ≫ c'.hom, ?_⟩
  calc
    α = e.functor.map α' ≫ c.hom := by simp [α']
    _ = (e.functor.map γ ≫ c'.hom) ≫ Limits.Sigma.map β' := by
      rw [hγ, e.functor.map_comp, Category.assoc, hc, Category.assoc]

end EquivalenceFactorization

section ShiftDetection

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] {ι : Type w} (E : ι → D)
  (hshift : ∀ i, ∃ j, Nonempty (E j ≅ (E i)⟦(-1 : ℤ)⟧))

include hshift

private lemma comp_shift_eq_zero {X Y : D} (f : X ⟶ Y)
    (hf : ∀ i (g : E i ⟶ X), g ≫ f = 0 → g = 0)
    (i : ι) (g : E i ⟶ X⟦(1 : ℤ)⟧) (hg : g ≫ f⟦1⟧' = 0) : g = 0 := by
  obtain ⟨j, ⟨e⟩⟩ := hshift i
  let u := shiftFunctorCompIsoId D (1 : ℤ) (-1) (by norm_num)
  have hβ : e.hom ≫ g⟦(-1 : ℤ)⟧' ≫ u.hom.app X = 0 := by
    refine hf j _ ?_
    have h := u.hom.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at h
    rw [Category.assoc, Category.assoc, ← h, ← Functor.map_comp_assoc, hg, Functor.map_zero,
      zero_comp, comp_zero]
  apply (shiftFunctor D (-1 : ℤ)).map_injective
  rw [Functor.map_zero, ← cancel_epi e.hom, ← cancel_mono (u.hom.app X)]
  simpa using hβ

private lemma isIso_of_bijective_on_generators
    [HasZeroObject D] [Pretriangulated D]
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    {X Y : D} (f : X ⟶ Y)
    (hf : ∀ i, Function.Bijective (fun g : E i ⟶ X ↦ g ≫ f)) : IsIso f := by
  obtain ⟨Z, q, d, hT⟩ := distinguished_cocone_triangle f
  apply (Triangle.isZero₃_iff_isIso₁ _ hT).1
  by_contra hz
  obtain ⟨i, g, hg⟩ := hE Z hz
  apply hg
  have hgd : g ≫ d = 0 := by
    apply comp_shift_eq_zero E hshift f
      (fun j β hβ ↦ (hf j).1 (by simpa using hβ)) i (g ≫ d)
    have hdf : d ≫ f⟦1⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    simp [hdf]
  obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₃ _ hT g hgd
  obtain ⟨γ, hγ⟩ := (hf i).2 β
  dsimp only at hγ
  have hfq : f ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT
  dsimp only [Triangle.mk_mor₂] at hβ
  rw [hβ, ← hγ, Category.assoc, hfq, comp_zero]

end ShiftDetection

section CoproductElements

variable {D : Type u} [Category.{v} D] (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
  {J : Type w} (X : J → D) [HasCoproduct X]
  [PreservesLimitsOfShape (Discrete J) H]

private lemma coproduct_elements_bijective :
    Function.Bijective (fun a : H.obj (op (∐ X)) ↦
      fun j ↦ H.map (Sigma.ι X j).op a) := by
  let c := (H ⋙ forget AddCommGrpCat).mapCone (Cofan.op (Cofan.mk (∐ X) (Sigma.ι X)))
  have hc : IsLimit c := isLimitOfPreserves (H ⋙ forget AddCommGrpCat)
    (Cofan.IsColimit.op (coproductIsCoproduct X))
  constructor
  · intro a b hab
    apply (Types.isLimitEquivSections hc).injective
    apply Subtype.ext
    funext j
    exact congrFun hab j.as
  · intro a
    let s : ((Discrete.functor (fun j ↦ op (X j))) ⋙ H ⋙
        forget AddCommGrpCat).sections := ⟨fun j ↦ a j.as, by
          intro ⟨j⟩ ⟨k⟩ f
          obtain rfl := Discrete.eq_of_hom f
          obtain rfl := Subsingleton.elim f (𝟙 (Discrete.mk j))
          simp⟩
    refine ⟨(Types.isLimitEquivSections hc).symm s, ?_⟩
    funext j
    exact Types.isLimitEquivSections_symm_apply hc s ⟨j⟩

end CoproductElements

/- Products of distinguished triangles in the opposite category give the exactness
of countable coproducts needed for descent through generator-coproduct covers. -/
section CoproductExactness

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{w} D] {J : Type w}

omit [Preadditive D] [HasShift D ℤ] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private lemma opCoproductIsoProduct_naturality (X Y : J → D) (f : ∀ j, X j ⟶ Y j) :
    (opCoproductIsoProduct Y).hom ≫ Limits.Pi.map (fun j ↦ (f j).op) =
      (Limits.Sigma.map f).op ≫ (opCoproductIsoProduct X).hom := by
  apply Pi.hom_ext
  intro j
  simp [← op_comp]

private lemma sigma_coyoneda_exact (T : J → Triangle D)
    (hT : ∀ j, T j ∈ distTriang D) {A : D}
    (f : A ⟶ ∐ fun j ↦ (T j).obj₂)
    (hf : f ≫ Limits.Sigma.map (fun j ↦ (T j).mor₂) = 0) :
    ∃ g : A ⟶ ∐ fun j ↦ (T j).obj₁,
      g ≫ Limits.Sigma.map (fun j ↦ (T j).mor₁) = f := by
  let T' : J → Triangle Dᵒᵖ := fun j ↦ (triangleOpEquivalence D).functor.obj (op (T j))
  have hT' : ∀ j, T' j ∈ distTriang Dᵒᵖ := fun j ↦ op_distinguished _ (hT j)
  let P := productTriangle T'
  have hP : P ∈ distTriang Dᵒᵖ := productTriangle_distinguished T' hT'
  let e₁ : op (∐ fun j ↦ (T j).obj₁) ≅ P.obj₃ := opCoproductIsoProduct (fun j ↦ (T j).obj₁)
  let e₂ : op (∐ fun j ↦ (T j).obj₂) ≅ P.obj₂ := opCoproductIsoProduct (fun j ↦ (T j).obj₂)
  let e₃ : op (∐ fun j ↦ (T j).obj₃) ≅ P.obj₁ := opCoproductIsoProduct (fun j ↦ (T j).obj₃)
  have he₂ : e₃.hom ≫ P.mor₁ =
      (Limits.Sigma.map (fun j ↦ (T j).mor₂)).op ≫ e₂.hom :=
    opCoproductIsoProduct_naturality _ _ _
  have he₁ : e₂.hom ≫ P.mor₂ =
      (Limits.Sigma.map (fun j ↦ (T j).mor₁)).op ≫ e₁.hom :=
    opCoproductIsoProduct_naturality _ _ _
  have hz : P.mor₁ ≫ (e₂.inv ≫ f.op) = 0 := by
    apply (cancel_epi e₃.hom).1
    rw [← Category.assoc e₃.hom P.mor₁, he₂]
    simp [← op_comp, hf]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ P hP (e₂.inv ≫ f.op) hz
  refine ⟨(e₁.hom ≫ g).unop, Quiver.Hom.op_inj ?_⟩
  rw [op_comp, Quiver.Hom.op_unop, ← Category.assoc, ← he₁, Category.assoc, ← hg,
    Iso.hom_inv_id_assoc]

end CoproductExactness

/- A componentwise inclusion of kernels on the generators survives a countable
coproduct. This is the descent step in the telescope argument. -/
section KernelDescent

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{0} D] {ι : Type w} (E : ι → D)
  (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
    (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
      α = γ ≫ Limits.Sigma.map β)

include hE'

private lemma sigma_desc_kills_kernel
    (P X : ℕ → D) (q : ∀ n, P n ⟶ X n) {Y : D} (g : ∀ n, P n ⟶ Y)
    (hg : ∀ n i (f : E i ⟶ P n), f ≫ q n = 0 → f ≫ g n = 0)
    (i : ι) (α : E i ⟶ ∐ P) (hα : α ≫ Limits.Sigma.map q = 0) :
    α ≫ Sigma.desc g = 0 := by
  choose K k d hT using fun n ↦ distinguished_cocone_triangle₁ (q n)
  obtain ⟨β, hβ⟩ := sigma_coyoneda_exact
    (fun n ↦ Triangle.mk (k n) (q n) (d n)) hT α hα
  obtain ⟨j, f, γ, rfl⟩ := hE' K i β
  dsimp only [Triangle.mk_mor₁] at hβ
  rw [← hβ, Category.assoc, Category.assoc]
  have hz : Limits.Sigma.map f ≫ Limits.Sigma.map k ≫ Sigma.desc g = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [Limits.Sigma.ι_map_assoc, Sigma.ι_comp_desc, comp_zero]
    rw [← Category.assoc]
    apply hg n (j n) (f n ≫ k n)
    have hz : k n ≫ q n = 0 := comp_distTriang_mor_zero₁₂ _ (hT n)
    simp [hz]
  rw [hz, comp_zero]

end KernelDescent

/- The initial element is surjective on the generators. A subsequent cone kills
precisely the generator maps in its evaluation kernel, and the element extends. -/
section Approximation

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max w v} D] {ι : Type w} (E : ι → D)
  (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H]

omit [Preadditive D] [HasShift D ℤ] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [H.IsHomological] in
private lemma exists_generator_surjective_element :
    ∃ (X : D) (a : H.obj (op X)),
      ∀ i, Function.Surjective (fun f : E i ⟶ X ↦ H.map f.op a) := by
  let J := Σ i, H.obj (op (E i))
  let Y : J → D := fun j ↦ E j.1
  obtain ⟨a, ha⟩ := (coproduct_elements_bijective H Y).2 (fun j ↦ j.2)
  exact ⟨∐ Y, a, fun i b ↦ ⟨Sigma.ι Y ⟨i, b⟩, congrFun ha ⟨i, b⟩⟩⟩

private lemma exists_kernel_killing_extension (X : D) (a : H.obj (op X)) :
    ∃ (Y : D) (t : X ⟶ Y) (b : H.obj (op Y)), H.map t.op b = a ∧
      ∀ i (f : E i ⟶ X), H.map f.op a = 0 → f ≫ t = 0 := by
  let J := Σ i, { f : E i ⟶ X // H.map f.op a = 0 }
  let K : J → D := fun j ↦ E j.1
  let k : ∐ K ⟶ X := Sigma.desc (fun j ↦ j.2.1)
  have hk : H.map k.op a = 0 := by
    apply (coproduct_elements_bijective H K).1
    funext j
    dsimp only
    simp only [map_zero, ← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp]
    simpa [k] using j.2.2
  obtain ⟨Y, t, d, hT⟩ := distinguished_cocone_triangle k
  obtain ⟨b, hb⟩ := exists_map_op_eq_of_distTriang H _ _ _ hT a hk
  refine ⟨Y, t, b, hb, fun i f hf ↦ ?_⟩
  have hkt := comp_distTriang_mor_zero₁₂ _ hT
  have h := congrArg (fun z ↦ Sigma.ι K ⟨i, f, hf⟩ ≫ z) hkt
  simpa [k] using h

end Approximation

section Telescope

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max w v} D] [HasCoproducts.{0} D] {ι : Type w} (E : ι → D)
  (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H]

omit [HasCoproducts.{max w v} D] [HasCoproducts.{0} D]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H] in
private lemma comp_eq_of_evaluation_eq {X Y : D} (a : H.obj (op X))
    (t : X ⟶ Y) (ht : ∀ i (f : E i ⟶ X), H.map f.op a = 0 → f ≫ t = 0)
    (i : ι) (f g : E i ⟶ X) (h : H.map f.op a = H.map g.op a) :
    f ≫ t = g ≫ t := by
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  exact ht i (f - g) (map_op_sub_eq_zero H h)

omit [HasCoproducts.{0} D]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H] in
private lemma coproduct_comp_eq_of_evaluation_eq
    {J : Type (max w v)} (j : J → ι) {X Y : D} (a : H.obj (op X))
    (t : X ⟶ Y) (ht : ∀ i (f : E i ⟶ X), H.map f.op a = 0 → f ≫ t = 0)
    (f g : (∐ fun x ↦ E (j x)) ⟶ X) (h : H.map f.op a = H.map g.op a) :
    f ≫ t = g ≫ t := by
  apply Sigma.hom_ext
  intro x
  simp only [← Category.assoc]
  apply comp_eq_of_evaluation_eq E H a t ht (j x)
  simpa only [map_op_comp_apply] using congrArg (H.map (Sigma.ι (fun x ↦ E (j x)) x).op) h

/- Work with the tail of the tower, so all maps `u n` already kill the initial
evaluation kernel. Cover each term by a coproduct of generators `P n`. The maps
`g n` below are finite partial sums giving a left inverse to the telescope after
descent; no vanishing of arbitrary generator maps is asserted. -/
private lemma telescope_injective_of_kernel_killing
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
      (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (B : D) (aB : H.obj (op B))
    (hB : ∀ i, Function.Surjective (fun f : E i ⟶ B ↦ H.map f.op aB))
    (X : ℕ → D) (t : ∀ n, X n ⟶ X (n + 1)) (a : ∀ n, H.obj (op (X n)))
    (ha : ∀ n, H.map (t n).op (a (n + 1)) = a n)
    (ht : ∀ n i (f : E i ⟶ X n), H.map f.op (a n) = 0 → f ≫ t n = 0)
    (u : ∀ n, B ⟶ X n) (hu : ∀ n, u n ≫ t n = u (n + 1))
    (hua : ∀ n, H.map (u n).op (a n) = aB)
    (huz : ∀ n i (f : E i ⟶ B), H.map f.op aB = 0 → f ≫ u n = 0)
    (i : ι) (α : E i ⟶ ∐ X)
    (hα : α ≫ (𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1))) = 0) :
    α = 0 := by
  classical
  let J (n : ℕ) := Σ i, E i ⟶ X n
  let F (n : ℕ) : J n → D := fun j ↦ E j.1
  let P (n : ℕ) := ∐ F n
  let q (n : ℕ) : P n ⟶ X n := Sigma.desc fun j ↦ j.2
  have hq : ∀ n i, Function.Surjective (fun f : E i ⟶ P n ↦ f ≫ q n) := by
    intro n i f
    exact ⟨Sigma.ι (F n) ⟨i, f⟩, by simp [q]⟩
  choose δ hδ using fun n (j : J n) ↦ hB j.1 (H.map j.2.op (a n))
  let d (n : ℕ) : P n ⟶ B := Sigma.desc (δ n)
  have hd (n : ℕ) : H.map (d n).op aB = H.map (q n).op (a n) := by
    apply (coproduct_elements_bijective H (F n)).1
    funext j
    simp only [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp]
    simpa [d, q] using hδ n j
  let s (n : ℕ) : P n ⟶ P (n + 1) :=
    Sigma.desc fun j ↦ Sigma.ι (F (n + 1)) ⟨j.1, j.2 ≫ t n⟩
  have hs (n : ℕ) : s n ≫ q (n + 1) = q n ≫ t n := by
    apply Sigma.hom_ext
    intro j
    simp [s, q]
  have hsd (n m : ℕ) : (s n ≫ d (n + 1)) ≫ u m = d n ≫ u m := by
    apply coproduct_comp_eq_of_evaluation_eq E H (fun j : J n ↦ j.1)
      aB (u m) (huz m)
    simp only [map_op_comp_apply, hd]
    rw [← map_op_comp_apply, hs]
    simp [ha]
  have hqt (n : ℕ) : q n ≫ t n = d n ≫ u (n + 1) := by
    rw [← hu, ← Category.assoc]
    apply coproduct_comp_eq_of_evaluation_eq E H (fun j : J n ↦ j.1)
      (a n) (t n) (ht n)
    simp [hua, hd]
  let g (n : ℕ) : P n ⟶ ∐ X :=
    q n ≫ Sigma.ι X n - d n ≫ u n ≫ Sigma.ι X n -
      ∑ k ∈ Finset.range n, d n ≫ u k ≫ Sigma.ι X k
  have hg (n : ℕ) (j : ι) (f : E j ⟶ P n) (hf : f ≫ q n = 0) :
      f ≫ g n = 0 := by
    have hfd : H.map (f ≫ d n).op aB = 0 := by
      simp only [map_op_comp_apply, hd]
      rw [← map_op_comp_apply, hf]
      simp
    have hfu (k : ℕ) : f ≫ d n ≫ u k = 0 := by
      simpa only [Category.assoc] using huz k j (f ≫ d n) hfd
    simp [g, Preadditive.comp_sub, Preadditive.comp_sum, ← Category.assoc,
      hf, hfu]
  have hgs (n : ℕ) : g n - s n ≫ g (n + 1) = q n ≫ Sigma.ι X n := by
    simp only [g, Preadditive.comp_sub, Preadditive.comp_add, Preadditive.comp_sum,
      ← Category.assoc, hs, hqt, hsd, Finset.sum_range_succ]
    abel
  let τX := 𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1))
  let τP := 𝟙 (∐ P) - Sigma.desc (fun n ↦ s n ≫ Sigma.ι P (n + 1))
  have hτq : τP ≫ Limits.Sigma.map q = Limits.Sigma.map q ≫ τX := by
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Sigma.ι_map,
      colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
      Category.assoc, Category.comp_id, Sigma.ι_map_assoc, colimit.ι_desc, sub_right_inj, τP, τX]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ Sigma.ι X (n + 1)) (hs n)
  have hτg : τP ≫ Sigma.desc g = Limits.Sigma.map q := by
    apply Sigma.hom_ext
    intro n
    simpa [τP, Preadditive.comp_sub, Preadditive.sub_comp] using hgs n
  obtain ⟨β, hβ⟩ := surjective_sigma_of_factorsThroughSigma E hE' P X q hq i α
  dsimp only at hβ
  have hβτ : (β ≫ τP) ≫ Limits.Sigma.map q = 0 := by
    rw [Category.assoc, hτq, ← Category.assoc, hβ]
    exact hα
  have hz := sigma_desc_kills_kernel E hE' P X q g hg i (β ≫ τP) hβτ
  simpa only [Category.assoc, hτg, hβ] using hz

omit [HasCoproducts.{max w v} D]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H] in
private lemma telescope_evaluation_bijective
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
      (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (B : D) (aB : H.obj (op B))
    (hB : ∀ i, Function.Surjective (fun f : E i ⟶ B ↦ H.map f.op aB))
    (X : ℕ → D) (t : ∀ n, X n ⟶ X (n + 1)) (a : ∀ n, H.obj (op (X n)))
    (ht : ∀ n i (f : E i ⟶ X n), H.map f.op (a n) = 0 → f ≫ t n = 0)
    (u : ∀ n, B ⟶ X n) (hu : ∀ n, u n ≫ t n = u (n + 1))
    (hua : ∀ n, H.map (u n).op (a n) = aB)
    (huz : ∀ n i (f : E i ⟶ B), H.map f.op aB = 0 → f ≫ u n = 0)
    (Y : D) (q : ∐ X ⟶ Y) (d : Y ⟶ (∐ X)⟦(1 : ℤ)⟧) (b : H.obj (op Y))
    (hT : Triangle.mk (𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1))) q d
      ∈ distTriang D)
    (hb : ∀ n, H.map (Sigma.ι X n ≫ q).op b = a n)
    (hshift : ∀ i (f : E i ⟶ (∐ X)⟦(1 : ℤ)⟧),
      f ≫ (𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1)))⟦1⟧' = 0 → f = 0)
    (i : ι) : Function.Bijective (fun f : E i ⟶ Y ↦ H.map f.op b) := by
  have hq (n : ℕ) : t n ≫ Sigma.ι X (n + 1) ≫ q = Sigma.ι X n ≫ q := by
    have hz := congrArg (fun f ↦ Sigma.ι X n ≫ f) (comp_distTriang_mor_zero₁₂ _ hT)
    have hz' : Sigma.ι X n ≫ q - t n ≫ Sigma.ι X (n + 1) ≫ q = 0 := by
      simpa [Preadditive.comp_sub, Preadditive.sub_comp] using hz
    exact (sub_eq_zero.mp hz').symm
  let r : B ⟶ Y := u 0 ≫ Sigma.ι X 0 ≫ q
  have hur (n : ℕ) : u n ≫ Sigma.ι X n ≫ q = r := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← hu, Category.assoc, hq, ih]
  have hr : H.map r.op b = aB := by
    have hb' := hb 0
    simp only [r, map_op_comp_apply] at hb' ⊢
    rw [hb', hua]
  have hfactor (f : E i ⟶ Y) : ∃ g : E i ⟶ B, g ≫ r = f := by
    have hfd : f ≫ d = 0 := by
      apply hshift i (f ≫ d)
      have hz := comp_distTriang_mor_zero₃₁ _ hT
      dsimp only [Triangle.mk_mor₃, Triangle.mk_mor₁] at hz
      simpa only [Category.assoc, comp_zero] using congrArg (fun z ↦ f ≫ z) hz
    obtain ⟨α, hα⟩ := Triangle.coyoneda_exact₃ _ hT f hfd
    dsimp only [Triangle.mk_mor₂] at hα
    obtain ⟨j, β, γ, hγ⟩ := hE' X i α
    choose δ hδ using fun n ↦ hB (j n) (H.map (β n).op (a n))
    have hβ (n : ℕ) : β n ≫ t n = (δ n ≫ u n) ≫ t n := by
      apply comp_eq_of_evaluation_eq E H (a n) (t n) (ht n) (j n)
      simp [hua, hδ]
    have hβq (n : ℕ) : β n ≫ Sigma.ι X n ≫ q = δ n ≫ r := by
      rw [← hq, ← Category.assoc (β n), hβ]
      simp [hq, hur]
    have hm : Limits.Sigma.map β ≫ q = Sigma.desc δ ≫ r := by
      apply Sigma.hom_ext
      intro n
      simpa using hβq n
    refine ⟨γ ≫ Sigma.desc δ, ?_⟩
    rw [Category.assoc, ← hm, ← Category.assoc, ← hγ, ← hα]
  have hzero (f : E i ⟶ Y) (hf : H.map f.op b = 0) : f = 0 := by
    obtain ⟨g, rfl⟩ := hfactor f
    have hg : H.map g.op aB = 0 := by
      simpa only [map_op_comp_apply, hr] using hf
    have hgu := huz 0 i g hg
    simp [r, ← Category.assoc, hgu]
  constructor
  · intro f g hfg
    exact sub_eq_zero.mp (hzero _ (map_op_sub_eq_zero H hfg))
  · intro c
    obtain ⟨f, hf⟩ := hB i c
    refine ⟨f ≫ r, ?_⟩
    simpa only [map_op_comp_apply, hr] using hf

end Telescope

section TelescopeElement

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{0} D] (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
  [PreservesLimitsOfShape (Discrete ℕ) H]

private lemma exists_telescope_element
    (X : ℕ → D) (t : ∀ n, X n ⟶ X (n + 1)) (a : ∀ n, H.obj (op (X n)))
    (ha : ∀ n, H.map (t n).op (a (n + 1)) = a n) :
    ∃ (Y : D) (q : ∐ X ⟶ Y) (d : Y ⟶ (∐ X)⟦(1 : ℤ)⟧) (b : H.obj (op Y)),
      Triangle.mk (𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1))) q d
        ∈ distTriang D ∧
      ∀ n, H.map (Sigma.ι X n ≫ q).op b = a n := by
  obtain ⟨c, hc⟩ := (coproduct_elements_bijective H X).2 a
  have hc' (n : ℕ) : H.map (Sigma.ι X n).op c = a n := congrFun hc n
  let τ := 𝟙 (∐ X) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι X (n + 1))
  have hτ : H.map τ.op c = 0 := by
    apply (coproduct_elements_bijective H X).1
    funext n
    have hι : Sigma.ι X n ≫ τ = Sigma.ι X n - t n ≫ Sigma.ι X (n + 1) := by
      simp [τ, Preadditive.comp_sub]
    dsimp only
    rw [map_zero, ← H.map_comp_apply, ← op_comp, hι, map_op_sub_apply, op_comp,
      H.map_comp_apply, hc', hc', ha, sub_self]
  obtain ⟨Y, q, d, hT⟩ := distinguished_cocone_triangle τ
  obtain ⟨b, hb⟩ := exists_map_op_eq_of_distTriang H _ _ _ hT c hτ
  refine ⟨Y, q, d, b, hT, fun n ↦ ?_⟩
  rw [op_comp, H.map_comp_apply, hb, hc']

end TelescopeElement

section SeededApproximation

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max w v} D] [HasCoproducts.{0} D] {ι : Type w} (E : ι → D)
  (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H]
  [PreservesLimitsOfShape (Discrete ℕ) H]

/- Run the construction from any element which is surjective on generators.
Keeping the map from that starting object is essential for the final argument. -/
private lemma exists_generator_bijective_extension
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
      (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (hshift : ∀ i, ∃ j, Nonempty (E j ≅ (E i)⟦(-1 : ℤ)⟧))
    (B : D) (aB : H.obj (op B))
    (hB : ∀ i, Function.Surjective (fun f : E i ⟶ B ↦ H.map f.op aB)) :
    ∃ (Y : D) (b : H.obj (op Y)) (r : B ⟶ Y),
      H.map r.op b = aB ∧ ∀ i, Function.Bijective (fun f : E i ⟶ Y ↦ H.map f.op b) := by
  classical
  let S := Σ X : D, H.obj (op X)
  have hs (s : S) : ∃ s' : S, ∃ t : s.1 ⟶ s'.1,
      H.map t.op s'.2 = s.2 ∧
        ∀ i (f : E i ⟶ s.1), H.map f.op s.2 = 0 → f ≫ t = 0 := by
    obtain ⟨Y, t, b, h₁, h₂⟩ := exists_kernel_killing_extension E H s.1 s.2
    exact ⟨⟨Y, b⟩, t, h₁, h₂⟩
  choose next step hstep hkill using hs
  let seq : ℕ → S := fun n ↦ Nat.rec ⟨B, aB⟩ (fun _ s ↦ next s) n
  let X (n : ℕ) := (seq (n + 1)).1
  let a (n : ℕ) : H.obj (op (X n)) := (seq (n + 1)).2
  let t (n : ℕ) : X n ⟶ X (n + 1) := step (seq (n + 1))
  have ha (n : ℕ) : H.map (t n).op (a (n + 1)) = a n := hstep (seq (n + 1))
  have ht (n : ℕ) (i : ι) (f : E i ⟶ X n) (hf : H.map f.op (a n) = 0) :
      f ≫ t n = 0 := hkill (seq (n + 1)) i f hf
  let u : ∀ n, B ⟶ X n := Nat.rec (motive := fun n ↦ B ⟶ X n)
    (step ⟨B, aB⟩) (fun n u ↦ u ≫ t n)
  have hu (n : ℕ) : u n ≫ t n = u (n + 1) := rfl
  have hua (n : ℕ) : H.map (u n).op (a n) = aB := by
    induction n with
    | zero => exact hstep ⟨B, aB⟩
    | succ n ih =>
      rw [← hu]
      simpa only [map_op_comp_apply, ha] using ih
  have huz (n : ℕ) (i : ι) (f : E i ⟶ B) (hf : H.map f.op aB = 0) : f ≫ u n = 0 := by
    induction n with
    | zero => exact hkill ⟨B, aB⟩ i f hf
    | succ n ih => rw [← hu, ← Category.assoc, ih, zero_comp]
  obtain ⟨Y, q, d, b, hT, hb⟩ := exists_telescope_element H X t a ha
  let r := u 0 ≫ Sigma.ι X 0 ≫ q
  have hr : H.map r.op b = aB := by
    dsimp only [r]
    rw [op_comp, H.map_comp, ConcreteCategory.comp_apply, hb, hua]
  refine ⟨Y, b, r, hr, ?_⟩
  exact telescope_evaluation_bijective E H hE' B aB hB X t a ht u hu hua huz Y q d b hT hb
    fun i f hf ↦ comp_shift_eq_zero E hshift _
      (fun j α hα ↦ telescope_injective_of_kernel_killing E H hE' B aB hB X t a ha ht
        u hu hua huz j α hα) i f hf

end SeededApproximation

section Representability

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max w v} D] [HasCoproducts.{0} D] {ι : Type w} (E : ι → D)
  (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H]
  [PreservesLimitsOfShape (Discrete ℕ) H]

omit [HasCoproducts.{max w v} D] [HasCoproducts.{0} D] [H.IsHomological]
  [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H]
  [PreservesLimitsOfShape (Discrete ℕ) H] in
private lemma isIso_of_generator_evaluations
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hshift : ∀ i, ∃ j, Nonempty (E j ≅ (E i)⟦(-1 : ℤ)⟧))
    {X Y : D} (a : H.obj (op X)) (b : H.obj (op Y))
    (ha : ∀ i, Function.Bijective (fun f : E i ⟶ X ↦ H.map f.op a))
    (hb : ∀ i, Function.Bijective (fun f : E i ⟶ Y ↦ H.map f.op b))
    (f : X ⟶ Y) (hf : H.map f.op b = a) : IsIso f := by
  apply isIso_of_bijective_on_generators E hshift hE f
  intro i
  constructor
  · intro g h hgh
    apply (ha i).1
    have hh := congrArg (fun k : E i ⟶ Y ↦ H.map k.op b) hgh
    simpa only [map_op_comp_apply, hf] using hh
  · intro g
    obtain ⟨h, hh⟩ := (ha i).2 (H.map g.op b)
    refine ⟨h, (hb i).1 ?_⟩
    simpa only [map_op_comp_apply, hf] using hh

/- Upgrade generator-wise representability using the seeded construction. To kill
a map in the evaluation kernel, start again from its cone. To represent an element
on `X`, start again from `Z ⊞ X`. In both cases the comparison from `Z` is an
isomorphism because the shifted generators detect isomorphisms. -/
private lemma exists_representing_element_of_shift_closed
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι)
      (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β)
    (hshift : ∀ i, ∃ j, Nonempty (E j ≅ (E i)⟦(-1 : ℤ)⟧)) :
    ∃ (Z : D) (aZ : H.obj (op Z)),
      ∀ X : D, Function.Bijective (fun f : X ⟶ Z ↦ H.map f.op aZ) := by
  obtain ⟨B, aB, hB⟩ := exists_generator_surjective_element E H
  obtain ⟨Z, aZ, _, _, hZ⟩ := exists_generator_bijective_extension E H hE' hshift B aB hB
  refine ⟨Z, aZ, fun X ↦ ?_⟩
  have key {C : D} (w : Z ⟶ C) (c : H.obj (op C)) (hw : H.map w.op c = aZ) :
      ∃ (Y : D) (r : C ⟶ Y) (b : H.obj (op Y)),
        H.map r.op b = c ∧ H.map (w ≫ r).op b = aZ ∧ IsIso (w ≫ r) := by
    have hC (i : ι) : Function.Surjective (fun g : E i ⟶ C ↦ H.map g.op c) := fun a ↦ by
      obtain ⟨g, hg⟩ := (hZ i).2 a
      exact ⟨g ≫ w, by simpa only [map_op_comp_apply, hw] using hg⟩
    obtain ⟨Y, b, r, hr, hY⟩ := exists_generator_bijective_extension E H hE' hshift C c hC
    have hs : H.map (w ≫ r).op b = aZ := by rw [map_op_comp_apply, hr, hw]
    exact ⟨Y, r, b, hr, hs, isIso_of_generator_evaluations E H hE hshift aZ b hZ hY _ hs⟩
  have hzero (f : X ⟶ Z) (hf : H.map f.op aZ = 0) : f = 0 := by
    obtain ⟨C, t, d, hT⟩ := distinguished_cocone_triangle f
    obtain ⟨c, hc⟩ := exists_map_op_eq_of_distTriang H _ _ _ hT aZ hf
    obtain ⟨Y, r, b, -, -, hI⟩ := key t c hc
    apply (cancel_mono (t ≫ r)).1
    have hft : f ≫ t = 0 := comp_distTriang_mor_zero₁₂ _ hT
    simp [← Category.assoc, hft]
  constructor
  · intro f g h
    exact sub_eq_zero.mp (hzero _ (map_op_sub_eq_zero H h))
  · intro a
    let c : H.obj (op (Z ⊞ X)) :=
      H.map (biprod.fst : Z ⊞ X ⟶ Z).op aZ + H.map (biprod.snd : Z ⊞ X ⟶ X).op a
    have hcZ : H.map (biprod.inl : Z ⟶ Z ⊞ X).op c = aZ := by
      simp [c, map_add, ← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp]
    have hcX : H.map (biprod.inr : X ⟶ Z ⊞ X).op c = a := by
      simp [c, map_add, ← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp]
    obtain ⟨Y, r, b, hr, hs, hI⟩ := key biprod.inl c hcZ
    have hi : H.map (inv (biprod.inl ≫ r)).op aZ = b := by
      rw [← hs, ← map_op_comp_apply, IsIso.inv_hom_id, op_id, H.map_id]
      rfl
    exact ⟨biprod.inr ≫ r ≫ inv (biprod.inl ≫ r), by
      simpa only [map_op_comp_apply, hi, hr] using hcX⟩

end Representability

section YonedaElement

variable {D : Type u} [Category.{v} D] [Preadditive D]
  (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive]

private lemma exists_iso_of_representing_element (Z : D) (a : H.obj (op Z))
    (ha : ∀ X : D, Function.Bijective (fun f : X ⟶ Z ↦ H.map f.op a)) :
    Nonempty (preadditiveYoneda.obj Z ≅ H) := by
  let η : preadditiveYoneda.obj Z ⟶ H :=
    { app := fun X ↦ AddCommGrpCat.ofHom
        { toFun := fun f : X.unop ⟶ Z ↦ H.map f.op a
          map_zero' := by
            have h : H.map (0 : X.unop ⟶ Z).op a = 0 := by simp
            exact h
          map_add' := fun (f g : X.unop ⟶ Z) ↦ by
            have h : H.map (f + g).op a = H.map f.op a + H.map g.op a := by simp
            exact h }
      naturality := fun X Y f ↦ AddCommGrpCat.ext fun (g : X.unop ⟶ Z) ↦ by
        have h : H.map (f.unop ≫ g).op a = H.map f (H.map g.op a) := by simp
        exact h }
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact (ConcreteCategory.isIso_iff_bijective (η.app X)).2 (ha X.unop)
  exact ⟨asIso η⟩

end YonedaElement


/-- **Brown representability**, weak version: let `𝒟` be a triangulated category with direct
sums and let `E : ι → 𝒟` be a family of objects such that every nonzero object of `𝒟` receives a
nonzero morphism from some `E i`, and such that every morphism from some `E i` to a countable
direct sum `∐ X`, `X : ℕ → 𝒟`, factors through a direct sum `∐ fun n ↦ E (j n)` of members of
the family via a direct sum of morphisms `E (j n) ⟶ X n`. Then a contravariant cohomological
functor `H : 𝒟ᵒᵖ ⥤ AddCommGrpCat` which transforms direct sums into products is representable. -/
@[stacks 0GYG]
public theorem exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{max w v} D] {ι : Type w} (E : ι → D)
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ X n)
      (γ : E i ⟶ ∐ fun n ↦ E (j n)), α = γ ≫ Limits.Sigma.map β)
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    [∀ J : Type (max w v), PreservesLimitsOfShape (Discrete J) H] :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  let : HasCoproducts.{0} D := has_smallest_coproducts_of_hasCoproducts
  let : PreservesLimitsOfShape (Discrete ℕ) H := preservesLimitsOfShape_of_equiv
    (Discrete.equivalence (Equiv.ulift : ULift.{max w v} ℕ ≃ ℕ)) H
  let E' : ι × ℤ → D := fun i ↦ (E i.1)⟦i.2⟧
  have hE₁ (X : D) (hX : ¬ IsZero X) : ∃ (i : ι × ℤ) (f : E' i ⟶ X), f ≠ 0 := by
    obtain ⟨i, f, hf⟩ := hE X hX
    refine ⟨⟨i, 0⟩, (shiftFunctorZero D ℤ).hom.app (E i) ≫ f, ?_⟩
    intro h
    apply hf
    apply (cancel_epi ((shiftFunctorZero D ℤ).hom.app (E i))).1
    simpa using h
  have hE₂ (X : ℕ → D) (i : ι × ℤ) (α : E' i ⟶ ∐ X) :
      ∃ (j : ℕ → ι × ℤ) (β : ∀ n, E' (j n) ⟶ X n)
        (γ : E' i ⟶ ∐ fun n ↦ E' (j n)), α = γ ≫ Limits.Sigma.map β := by
    obtain ⟨j, β, γ, hγ⟩ := equivalence_factorsThroughSigma E hE' (shiftEquiv D i.2) X i.1 α
    exact ⟨fun n ↦ ⟨j n, i.2⟩, β, γ, hγ⟩
  have hE₃ (i : ι × ℤ) : ∃ j, Nonempty (E' j ≅ (E' i)⟦(-1 : ℤ)⟧) :=
    ⟨⟨i.1, i.2 + (-1)⟩, ⟨(shiftFunctorAdd D i.2 (-1)).app (E i.1)⟩⟩
  obtain ⟨Z, a, ha⟩ := exists_representing_element_of_shift_closed E' H hE₁ hE₂ hE₃
  exact ⟨Z, exists_iso_of_representing_element H Z a ha⟩

end CategoryTheory.Pretriangulated
