module

public import StacksFrontier.AlgebraicTopology.DoldKan.Cosimplicial
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Cosimplicial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalized cochain complex carries homotopic maps to homotopic maps

Let `A` be an abelian category. The normalized cochain complex `Q(U)` of a cosimplicial object
`U` of `A` ([Stacks, Tag 019I]) is the quotient of the Moore cochain complex `s(U)` with
`Q(U)⁰ = U₀` and `Q(U)ⁿ⁺¹` the cokernel of the cofaces `δⁿ⁺¹ᵢ : Uₙ ⟶ Uₙ₊₁`, `i ≤ n`. These
conditions on the projection `π : s ⟶ Q` determine `Q` up to unique isomorphism under `s`, and
this file proves that any functor `Q` with such a projection carries homotopic morphisms of
cosimplicial objects to homotopic maps of cochain complexes.

The proof compares `Q` with the normalized cochain complex of [Stacks, Tag 019I], whose projection
is a split epimorphism. This gives a section `σ : Q(U) ⟶ s(U)` of `π`, so that
`Q(a) = σ ≫ s(a) ≫ π`, and the homotopy between `s(a)` and `s(b)` given by the first half of
[Stacks, Tag 01A0] passes to `Q(a)` and `Q(b)`.

## Main results

* `AlgebraicTopology.homotopic_normalizedCochainComplex_map`: if `a, b : U ⟶ V` are homotopic
  morphisms of cosimplicial objects of an abelian category, then `Q(a), Q(b) : Q(U) ⟶ Q(V)` are
  homotopic maps of cochain complexes.

## References

* [Stacks, Tag 01A0](https://stacks.math.columbia.edu/tag/01A0)
* [Stacks, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks, Tag 0FKJ](https://stacks.math.columbia.edu/tag/0FKJ)
-/

@[expose] public section

open CategoryTheory Limits Simplicial Opposite

universe v u

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism of cochain complexes which is an isomorphism in degree `0` and, in each degree
`n + 1`, a cokernel of a fixed morphism `g n`, is an epimorphism in each degree. -/
private lemma epi_f_of_cokernel {K L : CochainComplex A ℕ} {Y : ℕ → A}
    (g : ∀ n, Y n ⟶ K.X (n + 1)) (p : K ⟶ L) (hp₀ : IsIso (p.f 0))
    (hp : ∀ n, ∃ e : cokernel (g n) ≅ L.X (n + 1), cokernel.π _ ≫ e.hom = p.f (n + 1)) :
    ∀ n, Epi (p.f n)
  | 0 => inferInstance
  | n + 1 => by
      obtain ⟨e, he⟩ := hp n
      rw [← he]
      infer_instance

/-- Two morphisms out of a cochain complex `K`, each an isomorphism in degree `0` and, in each
degree `n + 1`, a cokernel of the same morphism `g n`, are related by a morphism of cochain
complexes under `K`. -/
private lemma exists_comp_eq_of_cokernel {K L L' : CochainComplex A ℕ} {Y : ℕ → A}
    (g : ∀ n, Y n ⟶ K.X (n + 1)) (p : K ⟶ L) (p' : K ⟶ L') (hp₀ : IsIso (p.f 0))
    (hp : ∀ n, ∃ e : cokernel (g n) ≅ L.X (n + 1), cokernel.π _ ≫ e.hom = p.f (n + 1))
    (hp' : ∀ n, ∃ e : cokernel (g n) ≅ L'.X (n + 1), cokernel.π _ ≫ e.hom = p'.f (n + 1)) :
    ∃ φ : L ⟶ L', p ≫ φ = p' := by
  have hepi := epi_f_of_cokernel g p hp₀ hp
  have hf : ∀ n, ∃ f : L.X n ⟶ L'.X n, p.f n ≫ f = p'.f n := by
    rintro (_ | n)
    · exact ⟨inv (p.f 0) ≫ p'.f 0, IsIso.hom_inv_id_assoc _ _⟩
    · obtain ⟨e, he⟩ := hp n
      obtain ⟨e', he'⟩ := hp' n
      refine ⟨e.inv ≫ e'.hom, ?_⟩
      rw [← he, ← he', Category.assoc, Iso.hom_inv_id_assoc]
  choose f hf using hf
  refine ⟨{ f := f, comm' := fun i j _ => ?_ }, HomologicalComplex.hom_ext _ _ fun n =>
    (HomologicalComplex.comp_f _ _ n).trans (hf n)⟩
  have := hepi i
  rw [← cancel_epi (p.f i), reassoc_of% (hf i), p'.comm, p.comm_assoc, hf j]

/-- **Stacks 01A0**, the assertion for the normalized cochain complex.
Let `A` be an abelian category, and let `Q` be the normalized cochain complex functor of
[Stacks, Tag 019I], given with its projection `π : s ⟶ Q` from the Moore cochain complex: `π` is
an isomorphism in degree `0` and, in each degree `n + 1`, a cokernel of the cofaces
`δⁿ⁺¹ᵢ : Uₙ ⟶ Uₙ₊₁`, `i ≤ n`. Let `a, b : U ⟶ V` be homotopic morphisms of cosimplicial objects
of `A`: related by a chain of morphisms consecutive members of which admit a homotopy in one
direction or the other, a homotopy from `a` to `b` being a family of morphisms
`h_{n, α} : Uₙ ⟶ Vₙ` indexed by the simplices `α ∈ Δ[1]ₙ` with
`h_{m, α} ∘ U(g) = V(g) ∘ h_{n, α ∘ g}` for every morphism `g : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`, whose
components at the constant maps `⦋n⦌ ⟶ ⦋1⦌` with values `0` and `1` are `a_n` and `b_n`
([Stacks, Tag 0FKJ]). Then `Q(a), Q(b) : Q(U) ⟶ Q(V)` are homotopic maps of cochain
complexes. -/
@[stacks 01A0 "the second assertion, for the normalized cochain complex `Q`; the first, for the \
  Moore cochain complex `s`, is `homotopic_alternatingCofaceMapComplex_map`. `Q` is any functor \
  with a natural transformation `π : s ⟶ Q` which is an isomorphism in degree `0` and a cokernel \
  of the cofaces `δⁿ⁺¹ᵢ`, `i ≤ n`, in degree `n + 1`, the characterization of `Q` and of \
  `s(U) → Q(U)` given in 019I, which determines `Q` up to unique isomorphism under `s`. A \
  homotopy is given by its family of components as in 0FKJ and 07KB, and being homotopic is \
  spelled `Relation.EqvGen` of the existence of such a family, as in 019S"]
public theorem homotopic_normalizedCochainComplex_map
    (Q : CosimplicialObject A ⥤ CochainComplex A ℕ) (π : alternatingCofaceMapComplex A ⟶ Q)
    (hπ₀ : ∀ U : CosimplicialObject A, IsIso ((π.app U).f 0))
    (hπ : ∀ (U : CosimplicialObject A) (n : ℕ),
      ∃ e : cokernel (Sigma.desc (f := fun _ : Fin (n + 1) => U.obj ⦋n⦌)
          fun i => U.δ i.castSucc) ≅ (Q.obj U).X (n + 1),
        cokernel.π _ ≫ e.hom = (π.app U).f (n + 1))
    {U V : CosimplicialObject A} {a b : U ⟶ V}
    (h : Relation.EqvGen
      (fun a b : U ⟶ V => ∃ h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
          (U.obj n ⟶ V.obj n),
        (∀ ⦃n m : SimplexCategory⦄ (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
            U.map g ≫ h m α = h n ((Δ[1] : SSet.{0}).map g.op α) ≫ V.map g) ∧
          (∀ n : SimplexCategory, h n (SSet.stdSimplex.const 1 0 (op n)) = a.app n) ∧
          (∀ n : SimplexCategory, h n (SSet.stdSimplex.const 1 1 (op n)) = b.app n)) a b) :
    homotopic A (ComplexShape.up ℕ) (Q.map a) (Q.map b) := by
  obtain ⟨-, Q₀, π₀, hπ₀', hπ', hsplit, -, -, -⟩ := exists_normalizedCochainComplex A
  let g : ∀ n, (∐ fun _ : Fin (n + 1) => U.obj ⦋n⦌) ⟶ U.obj ⦋n + 1⦌ := fun n =>
    Sigma.desc fun i => U.δ i.castSucc
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_cokernel g (π.app U) (π₀.app U) (hπ₀ U) (hπ U) (hπ' U)
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_cokernel g (π₀.app U) (π.app U) (hπ₀' U) (hπ' U) (hπ U)
  have : Epi (π.app U) := HomologicalComplex.epi_of_epi_f _ (epi_f_of_cokernel g _ (hπ₀ U) (hπ U))
  have hι : (section_ π₀).app U ≫ π₀.app U = 𝟙 _ := by
    rw [← NatTrans.comp_app, IsSplitEpi.id, NatTrans.id_app]
  obtain ⟨σ, hσ⟩ : ∃ σ : Q.obj U ⟶ (alternatingCofaceMapComplex A).obj U,
      σ ≫ π.app U = 𝟙 _ := by
    refine ⟨ψ ≫ (section_ π₀).app U, ?_⟩
    calc (ψ ≫ (section_ π₀).app U) ≫ π.app U
        = ψ ≫ (section_ π₀).app U ≫ π₀.app U ≫ φ := by rw [← hφ, Category.assoc]
      _ = ψ ≫ φ := by rw [reassoc_of% hι]
      _ = 𝟙 _ := by rw [← cancel_epi (π.app U), reassoc_of% hψ, hφ, Category.comp_id]
  have hQ : ∀ c : U ⟶ V, Q.map c = σ ≫ (alternatingCofaceMapComplex A).map c ≫ π.app V :=
    fun c => by rw [π.naturality, reassoc_of% hσ]
  obtain ⟨H⟩ := homotopic_alternatingCofaceMapComplex_map h
  rw [hQ a, hQ b]
  exact ⟨(H.compRight (π.app V)).compLeft _⟩

end AlgebraicTopology
