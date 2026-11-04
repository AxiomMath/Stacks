module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.Homology.KFlat.Closure
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# Tensoring with a complex does not depend on the chosen K-flat resolution

Let `R` be a commutative ring and let `G` be a cochain complex of `R`-modules. Say that a
quasi-isomorphism `q : P ⟶ X` from a K-flat complex *computes* `X ⊗^𝐋_R G` if
`Tot(P ⊗_R G) ⟶ Tot(X ⊗_R G)` is a quasi-isomorphism. The main result here is that whether this
holds does not depend on the K-flat resolution `q`: if one K-flat resolution of `X` computes
`X ⊗^𝐋_R G`, then every K-flat resolution of `X` does.

This is the statement that makes a hypothesis of the shape "for every K-flat `P` and every
quasi-isomorphism `P ⟶ X`, tensoring with `G` stays a quasi-isomorphism" — the form in which
Stacks Tag 0BZ8 assumes that `A ⊗_R C` represents `A ⊗^𝐋_R C` — usable at a resolution one did
not choose. The second group of results below is the compatibility of that notion with a K-flat
factor: if tensoring `p` with `G` is a quasi-isomorphism and `L` is K-flat, then tensoring
`p ⊗ 1_L` with `G` is one as well, which is the "`P ⊗_R B ⊗_R C ⟶ A ⊗_R B ⊗_R C` reduces to
`P ⊗_R C ⟶ A ⊗_R C`" step of that proof.

## Main results

* `CochainComplex.DerivedTensor.quasiIso_trightCochain_map`: **Stacks 064L on the right** — a
  quasi-isomorphism between K-flat complexes stays a quasi-isomorphism after tensoring on the
  right with any complex. The left-hand form is
  `CochainComplex.DerivedTensor.quasiIso_tleftCochain_map`.
* `CochainComplex.DerivedTensor.quasiIso_whiskerRight_whiskerRight_of_kFlat` and its
  tensor–total form `CochainComplex.DerivedTensor.quasiIso_trightCochain_map_whiskerRight`: the
  two fixed factors of an iterated tensor product may be interchanged when one of them is
  K-flat.
* `CochainComplex.DerivedTensor.quasiIso_trightCochain_map_of_kFlat_resolution`: the
  independence of the K-flat resolution stated above.

## Implementation notes

*Why the two fixed factors can be interchanged without a braided-category instance.* The
interchange needs only the associator — an instance, from Mathlib's monoidal structure on
cochain complexes — and the single isomorphism `G ⊗ L ≅ L ⊗ G`, which is
`CochainComplex.koszulBraiding`; no `BraidedCategory` instance is introduced, and the naturality
that would come with one is replaced by `MonoidalCategory.whisker_exchange` at the one morphism
where it is needed.

*Why the statements are kept at one level of `TrightCochain`.* The tensor–total functor
`TrightCochain L` and the monoidal whiskering `· ▷ L` are definitionally equal, and
`CochainComplex.DerivedTensor.trightCochain_map_eq_whiskerRight` is that equality — but only at
one level: identifying `(TrightCochain G).map ((TrightCochain L).map p)` with `(p ▷ L) ▷ G`
requires the `HasMapBifunctor` instance arguments of the two spellings of `X ⊗ G` to be unfolded
against each other, which does not terminate within the elaboration budget. Every statement
below therefore mixes the two spellings only one level deep, and the interchange result is
stated twice, once in each spelling, so that its consumers never have to nest them.

*The lifted monoidal structure.* `CochainComplex.KFlat` and the tensor–total functors are stated
against the large-universe monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Monoidal/LargeUniverse.lean`, whose module universe is
independent of the ring's; Mathlib's own instance on `ModuleCat.{u} R` is reached first by
instance search and fails on universe unification without falling through, so the lifted
instances are settled for this file. The independence result is stated at a module universe
equal to the ring's, which is the generality of
`CochainComplex.KFlat.exists_kFlat_factorization_up_to_homotopy` (Stacks 0G6M), the input its
proof rests on.

## References

* [The Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L), tensoring a
  quasi-isomorphism between K-flat complexes.
* [The Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M), the derived tensor
  product built from a K-flat resolution.
* [The Stacks Project, Tag 0G6M](https://stacks.math.columbia.edu/tag/0G6M), factoring a map out
  of a K-flat complex through a K-flat resolution of its target.
* [The Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ), K-flatness, and
  [Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0), that a K-flat complex preserves
  quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

open MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-! ### Elementary transfers of the quasi-isomorphism property -/

/-- A morphism flanked by two isomorphisms is a quasi-isomorphism exactly when it is one. -/
theorem quasiIso_sandwich_iff {X Y Z W : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) [IsIso a] [IsIso c] :
    QuasiIso (a ≫ b ≫ c) ↔ QuasiIso b := by
  have ha : QuasiIso a := quasiIso_of_isIso a
  have hc : QuasiIso c := quasiIso_of_isIso c
  rw [quasiIso_iff_comp_left (hφ := ha) a (b ≫ c),
    quasiIso_iff_comp_right (hφ' := hc) b c]

/-- Homotopic morphisms are quasi-isomorphisms together. -/
theorem quasiIso_congr_of_homotopy {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) : QuasiIso f ↔ QuasiIso g := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff f,
    ← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff g,
    HomotopyCategory.eq_of_homotopy f g h]

/-- Tensoring on the right with a fixed complex is whiskering on the right. -/
theorem trightCochain_map_eq_whiskerRight (L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : X ⟶ Y) :
    (TrightCochain L).map f = f ▷ L := rfl

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism after tensoring on
the right with any complex. This is the companion of `quasiIso_tleftCochain_map` (Stacks 064L),
whose fixed factor is the left one. -/
@[stacks 064L]
theorem quasiIso_trightCochain_map
    {P Q : CochainComplex (ModuleCat.{max u v} R) ℤ} (α : P ⟶ Q) [QuasiIso α]
    (hP : P.KFlat) (hQ : Q.KFlat) (L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    QuasiIso ((TrightCochain L).map α) := by
  have hl : QuasiIso ((TleftCochain L).map α) := quasiIso_tleftCochain_map α hP hQ L
  have heq : (TleftCochain L).map α ≫ (tensorFlipIso L Q).hom =
      (tensorFlipIso L P).hom ≫ (TrightCochain L).map α :=
    tensorFlipIso_naturality L α
  have hβP : QuasiIso (tensorFlipIso L P).hom := quasiIso_of_isIso _
  have hβQ : QuasiIso (tensorFlipIso L Q).hom := quasiIso_of_isIso _
  have hc : QuasiIso ((tensorFlipIso L P).hom ≫ (TrightCochain L).map α) := by
    rw [← heq]
    exact quasiIso_comp (hφ := hl) (hφ' := hβQ) _ _
  exact (quasiIso_iff_comp_left (hφ := hβP) _ _).1 hc

/-! ### Interchanging two fixed factors -/

/-- Tensoring on the right with `L` and then with `G` is tensoring on the right with `L ⊗ G`, up
to the associator. -/
theorem quasiIso_whiskerRight_whiskerRight_iff
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (p : X ⟶ Y)
    (L G : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    QuasiIso ((p ▷ L) ▷ G) ↔ QuasiIso (p ▷ (L ⊗ G)) := by
  rw [MonoidalCategory.whiskerRight_tensor_symm p L G]
  exact quasiIso_sandwich_iff _ _ _

/-- The fixed factor of a tensor product may be replaced by an isomorphic complex. -/
theorem quasiIso_whiskerRight_iff_of_iso
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (p : X ⟶ Y)
    {L L' : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : L ≅ L') :
    QuasiIso (p ▷ L') ↔ QuasiIso (p ▷ L) := by
  have h := MonoidalCategory.whisker_exchange p e.hom
  have key : p ▷ L' = inv (X ◁ e.hom) ≫ p ▷ L ≫ (Y ◁ e.hom) := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [key]
  exact quasiIso_sandwich_iff _ _ _

/-- **The two fixed factors of an iterated tensor product may be interchanged**, when one of them
is K-flat: if tensoring `p` on the right with `G` is a quasi-isomorphism and `L` is K-flat, then
tensoring it first with `L` and then with `G` is one too.

Tensoring with the K-flat `L` preserves quasi-isomorphisms (Stacks 06Y0), which gives the
statement with the two factors in the other order; the associator and the Koszul symmetry
`G ⊗ L ≅ L ⊗ G` of total complexes carry it to this one. -/
theorem quasiIso_whiskerRight_whiskerRight_of_kFlat
    (L G : CochainComplex (ModuleCat.{max u v} R) ℤ) (hL : L.KFlat)
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (p : X ⟶ Y)
    (h : QuasiIso (p ▷ G)) :
    QuasiIso ((p ▷ L) ▷ G) := by
  have := h
  have h₀ : QuasiIso ((TrightCochain L).map (p ▷ G)) := quasiIso_tright_map L hL (p ▷ G)
  have h₁ : QuasiIso ((p ▷ G) ▷ L) := by
    rw [← trightCochain_map_eq_whiskerRight L (p ▷ G)]
    exact h₀
  rw [quasiIso_whiskerRight_whiskerRight_iff] at h₁
  exact (quasiIso_whiskerRight_whiskerRight_iff p L G).2
    ((quasiIso_whiskerRight_iff_of_iso p (CochainComplex.koszulBraiding G L)).2 h₁)

/-- The form of `quasiIso_whiskerRight_whiskerRight_of_kFlat` that the tensor–total functors
state: if `- ⊗ G` carries `p` to a quasi-isomorphism and `L` is K-flat, then it carries
`p ⊗ 1_L` to one. -/
theorem quasiIso_trightCochain_map_whiskerRight
    (L G : CochainComplex (ModuleCat.{max u v} R) ℤ) (hL : L.KFlat)
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (p : X ⟶ Y)
    (h : QuasiIso ((TrightCochain G).map p)) :
    QuasiIso ((TrightCochain G).map (p ▷ L)) := by
  rw [trightCochain_map_eq_whiskerRight G p] at h
  rw [trightCochain_map_eq_whiskerRight G (p ▷ L)]
  exact quasiIso_whiskerRight_whiskerRight_of_kFlat L G hL p h

/-- Tensoring on the right with a fixed complex carries homotopic morphisms to homotopic
morphisms, so the two are quasi-isomorphisms together. -/
theorem quasiIso_trightCochain_map_congr (G : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {X Y : CochainComplex (ModuleCat.{max u v} R) ℤ} {f g : X ⟶ Y} (h : Homotopy f g) :
    QuasiIso ((TrightCochain G).map f) ↔ QuasiIso ((TrightCochain G).map g) :=
  quasiIso_congr_of_homotopy (TrightCochain_preservesHomotopyRel G ⟨h⟩).some

/-! ### Independence of the K-flat resolution -/

/-- **Tensoring a K-flat resolution with a fixed complex does not depend on the resolution.** If
one quasi-isomorphism `P₀ ⟶ X` from a K-flat complex stays a quasi-isomorphism after tensoring
with `G`, then so does every other.

Both sources map to a K-flat complex `N` over `X` by Stacks 0G6M, applied to the map out of
`P₀ ⊞ P` with components the two resolutions; the two comparison maps `P₀ ⟶ N` and `P ⟶ N` are
quasi-isomorphisms between K-flat complexes, so tensoring with `G` keeps them
quasi-isomorphisms, and the hypothesis then says that tensoring the quasi-isomorphism
`N ⟶ X` with `G` is a quasi-isomorphism, which is what the conclusion needs. -/
theorem quasiIso_trightCochain_map_of_kFlat_resolution
    (G : CochainComplex (ModuleCat.{u} R) ℤ) {X P₀ P : CochainComplex (ModuleCat.{u} R) ℤ}
    (q₀ : P₀ ⟶ X) [QuasiIso q₀] (hP₀ : CochainComplex.KFlat.{u, u} P₀)
    (h₀ : QuasiIso ((TrightCochain G).map q₀))
    (q : P ⟶ X) [QuasiIso q] (hP : CochainComplex.KFlat.{u, u} P) :
    QuasiIso ((TrightCochain G).map q) := by
  have hsum : CochainComplex.KFlat.{u, u} (P₀ ⊞ P) :=
    (CochainComplex.KFlat.kFlat_two_out_of_three_of_degreewiseSplit
      (ShortComplex.mk (biprod.inl : P₀ ⟶ P₀ ⊞ P) (biprod.snd : P₀ ⊞ P ⟶ P) (by simp))
      (fun n => (ShortComplex.Splitting.ofHasBinaryBiproduct P₀ P).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n))).2.1 hP₀ hP
  obtain ⟨N, b, c, hN, hc, ⟨hhom⟩, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_factorization_up_to_homotopy (biprod.desc q₀ q) hsum
  have := hc
  -- each component `i` of `b` factors a resolution `q'` through `c` up to homotopy, so it is a
  -- quasi-isomorphism between K-flat complexes, which stays one after tensoring with `G`
  have key : ∀ {P' : CochainComplex (ModuleCat.{u} R) ℤ} (i : P' ⟶ P₀ ⊞ P) (q' : P' ⟶ X)
      [QuasiIso q'], i ≫ biprod.desc q₀ q = q' → CochainComplex.KFlat.{u, u} P' →
      Nonempty (Homotopy q' ((i ≫ b) ≫ c)) ∧ QuasiIso ((TrightCochain G).map (i ≫ b)) := by
    intro P' i q' _ hi hP'
    have e : Homotopy q' ((i ≫ b) ≫ c) :=
      (Homotopy.ofEq hi.symm).trans
        ((hhom.compLeft i).trans (Homotopy.ofEq (Category.assoc _ _ _).symm))
    have hb : QuasiIso (i ≫ b) :=
      quasiIso_of_comp_right (i ≫ b) c
        (hφφ' := (quasiIso_congr_of_homotopy.{u, u} e).1 inferInstance)
    exact ⟨⟨e⟩, quasiIso_trightCochain_map.{u, u} _ hP' hN G⟩
  obtain ⟨⟨e₀⟩, ht₀⟩ := key biprod.inl q₀ (biprod.inl_desc q₀ q) hP₀
  obtain ⟨⟨e₁⟩, ht₁⟩ := key biprod.inr q (biprod.inr_desc q₀ q) hP
  -- hence tensoring `c` with `G` is one, and so is tensoring `q` with `G`
  have hqc : QuasiIso ((TrightCochain G).map c) := by
    have h' : QuasiIso ((TrightCochain G).map ((biprod.inl ≫ b) ≫ c)) :=
      (quasiIso_trightCochain_map_congr.{u, u} G e₀).1 h₀
    rw [Functor.map_comp] at h'
    exact quasiIso_of_comp_left (hφ := ht₀) _ _ (hφφ' := h')
  refine (quasiIso_trightCochain_map_congr.{u, u} G e₁).2 ?_
  rw [Functor.map_comp]
  exact quasiIso_comp (hφ := ht₁) (hφ' := hqc) _ _

end CochainComplex.DerivedTensor

end
