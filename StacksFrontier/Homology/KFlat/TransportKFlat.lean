module
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Algebra.Homology.HomotopyCategory.JointAcyclicity
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# K-flatness along a functor carrying one bifunctor to another

Let `F : A ⥤ B ⥤ D` and `F' : A' ⥤ B' ⥤ D'` be additive bifunctors between abelian categories,
and let `G₁ : A ⥤ A'`, `G₂ : B ⥤ B'`, `G₃ : D ⥤ D'` be additive functors such that `G₃` carries
`F` to `F'` along `G₁` and `G₂` (natural isomorphisms `G₃(F(a, b)) ≅ F'(G₁ a, G₂ b)`) and
commutes with the coproducts in a total complex, so that `G₃ Tot(F(K, L)) ≅ Tot(F'(G₁ K, G₂ L))`
(`CochainComplex.KFlatBifunctor.transportComplexIso`). This file records the two formal
consequences for K-flatness that the stalk arguments of [Stacks, Tag 06YB] and
[Stacks, Tag 06YC] rest on.

* **Detection by a family.** If a family of such data has the `G₃` jointly reflecting
  isomorphisms and exact, and the `G₁` preserve acyclicity, then a complex `L` is K-flat for `F`
  as soon as every `G₂ L` is K-flat for `F'`: for an acyclic `N`, the total complex `Tot(F(N, L))`
  is acyclic because each `G₃ Tot(F(N, L)) ≅ Tot(F'(G₁ N, G₂ L))` is.
* **Preservation through a retract.** If every acyclic complex of `A'` is a retract of `G₁` of an
  acyclic complex of `A`, and `G₃` is exact, then `G₂` carries K-flat complexes for `F` to K-flat
  complexes for `F'`: `Tot(F'(N, G₂ L))` is a retract of `Tot(F'(G₁ N', G₂ L)) ≅ G₃ Tot(F(N', L))`.
  For a point of a site, `G₁` is the stalk functor and `N'` is the skyscraper complex of `N`.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_of_forall_kFlat_map`
* `CochainComplex.KFlatBifunctor.kFlat_map_of_retract`
* `HomologicalComplex.Acyclic.of_retract`: a retract of an acyclic complex is acyclic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- A retract of an acyclic complex is acyclic: its homology is a retract of zero. -/
theorem Acyclic.of_retract {K K' : HomologicalComplex C c} (hK' : K'.Acyclic) (i : K ⟶ K')
    (p : K' ⟶ K) (h : i ≫ p = 𝟙 K) : K.Acyclic := fun n => by
  rw [exactAt_iff_isZero_homology]
  have hz := (exactAt_iff_isZero_homology K' n).1 (hK' n)
  rw [IsZero.iff_id_eq_zero, ← homologyMap_id, ← h, homologyMap_comp,
    hz.eq_of_tgt (homologyMap i n) 0, zero_comp]

end HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {A B D A' B' D' : Type*}
  [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
  [Abelian A] [Abelian B] [Abelian D] [Abelian A'] [Abelian B'] [Abelian D']
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ B' ⥤ D') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ : CochainComplex A' ℤ) (K₂ : CochainComplex B' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]

section Family

variable {ι : Type*} (G₁ : ι → A ⥤ A') (G₂ : ι → B ⥤ B') (G₃ : ι → D ⥤ D')
  [∀ i, (G₁ i).Additive] [∀ i, (G₂ i).Additive] [∀ i, (G₃ i).Additive]
  [∀ i, (G₃ i).PreservesHomology]
  (ε : ∀ i (a : A) (b : B),
    (G₃ i).obj ((F.obj a).obj b) ≅ (F'.obj ((G₁ i).obj a)).obj ((G₂ i).obj b))
  (hε₁ : ∀ i {a a' : A} (f : a ⟶ a') (b : B),
    (G₃ i).map ((F.map f).app b) ≫ (ε i a' b).hom =
      (ε i a b).hom ≫ (F'.map ((G₁ i).map f)).app ((G₂ i).obj b))
  (hε₂ : ∀ i (a : A) {b b' : B} (g : b ⟶ b'),
    (G₃ i).map ((F.obj a).map g) ≫ (ε i a b').hom =
      (ε i a b).hom ≫ (F'.obj ((G₁ i).obj a)).map ((G₂ i).map g))
  [∀ i (n : ℤ), PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) (G₃ i)]
  [∀ i (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex (G₃ i)
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

include ε hε₁ hε₂ in
/-- **K-flatness is detected by a jointly conservative family of exact functors** carrying `F`
to `F'`: if the `G₃ i` are exact and jointly reflect isomorphisms, the `G₁ i` preserve
acyclicity, and every `G₂ i L` is K-flat for `F'`, then `L` is K-flat for `F`. -/
theorem kFlat_of_forall_kFlat_map (hG₃ : JointlyReflectIsomorphisms G₃)
    (hG₁ : ∀ i (N : CochainComplex A ℤ), N.Acyclic →
      (((G₁ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).Acyclic)
    (L : CochainComplex B ℤ)
    (hL : ∀ i, KFlat F' (((G₂ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    KFlat F L := by
  intro N hN
  rw [Stacks.Homology.acyclic_iff_forall_map G₃ hG₃]
  intro i
  exact fun n => (hL i _ (hG₁ i N hN) n).of_iso
    (transportComplexIso F F' (G₁ i) (G₂ i) (G₃ i) (ε i) (hε₁ i) (hε₂ i) N L).symm

end Family

section Retract

variable (G₁ : A ⥤ A') (G₂ : B ⥤ B') (G₃ : D ⥤ D')
  [G₁.Additive] [G₂.Additive] [G₃.Additive] [G₃.PreservesHomology]
  (ε : ∀ (a : A) (b : B), G₃.obj ((F.obj a).obj b) ≅ (F'.obj (G₁.obj a)).obj (G₂.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    G₃.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (G₁.map f)).app (G₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    G₃.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (G₁.obj a)).map (G₂.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G₃]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G₃
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

include G₃ ε hε₁ hε₂ in
/-- **K-flatness is preserved by a functor through which every acyclic complex is a retract**:
if `G₃` is exact and every acyclic complex of `A'` is a retract of `G₁` of an acyclic complex of
`A`, then `G₂` carries complexes K-flat for `F` to complexes K-flat for `F'`. -/
theorem kFlat_map_of_retract
    (hG₁ : ∀ N : CochainComplex A' ℤ, N.Acyclic → ∃ (N' : CochainComplex A ℤ)
      (i : N ⟶ (G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
      (p : (G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj N' ⟶ N),
      N'.Acyclic ∧ i ≫ p = 𝟙 N)
    (L : CochainComplex B ℤ) (hL : KFlat F L) :
    KFlat F' ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  intro N hN
  obtain ⟨N', i, p, hN', hip⟩ := hG₁ N hN
  have h₁ : ((G₃.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (totalComplex F N' L)).Acyclic := fun n => by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (G₃.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
      (hL N' hN' n))).of_iso (((totalComplex F N' L).sc n).mapHomologyIso G₃)
  let T := F'.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have h₂ : ((T.obj ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')).obj
      ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).Acyclic :=
    fun n => (h₁ n).of_iso (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ N' L)
  refine HomologicalComplex.Acyclic.of_retract h₂ ((T.map i).app _) ((T.map p).app _) ?_
  rw [← NatTrans.comp_app, ← T.map_comp, hip, T.map_id, NatTrans.id_app]

end Retract

end CochainComplex.KFlatBifunctor

namespace CochainComplex.KFlatBifunctor

open MonoidalCategory

/-! ### Strong monoidal functors

The two statements above for the tensor products of two abelian monoidal categories and a strong
monoidal functor, whose comparison `G(a ⊗ b) ≅ G a ⊗ G b` is the inverse of its tensorator; and the
same for the left variable, through `kFlatLeft_iff_kFlat_flip`. -/

section Monoidal

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  [MonoidalCategory A] [MonoidalCategory A']
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A) (ComplexShape.up ℤ)]
  [(curriedTensor A').Additive] [∀ X : A', ((curriedTensor A').obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A') (ComplexShape.up ℤ)]

section Single

variable (G : A ⥤ A') [G.Additive] [G.Monoidal] [G.PreservesHomology]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G]
  (hG : ∀ N : CochainComplex A' ℤ, N.Acyclic → ∃ (N' : CochainComplex A ℤ)
      (i : N ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
      (p : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N' ⟶ N),
      N'.Acyclic ∧ i ≫ p = 𝟙 N)

include hG in
/-- **A strong monoidal exact functor through which every acyclic complex is a retract preserves
K-flatness**, for the tensor products. -/
theorem kFlat_map_of_retract_of_monoidal
    [∀ (K L : CochainComplex A ℤ),
      HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G
        ((((curriedTensor A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
    (L : CochainComplex A ℤ) (hL : KFlat (curriedTensor A) L) :
    KFlat (curriedTensor A') ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  kFlat_map_of_retract (curriedTensor A) (curriedTensor A') G G G
    (fun a b => (Functor.Monoidal.μIso G a b).symm)
    (fun f b => (Functor.OplaxMonoidal.δ_natural_left G f b).symm)
    (fun a _ _ g => (Functor.OplaxMonoidal.δ_natural_right G a g).symm) hG L hL

include hG in
/-- **A strong monoidal exact functor through which every acyclic complex is a retract preserves
left K-flatness**, for the tensor products. -/
theorem kFlatLeft_map_of_retract_of_monoidal
    [(curriedTensor A).flip.Additive] [∀ X : A, ((curriedTensor A).flip.obj X).Additive]
    [∀ (K₁ K₂ : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A).flip (ComplexShape.up ℤ)]
    [(curriedTensor A').flip.Additive] [∀ X : A', ((curriedTensor A').flip.obj X).Additive]
    [∀ (K₁ K₂ : CochainComplex A' ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A').flip (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex A ℤ),
      HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G
        ((((curriedTensor A).flip.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
    (L : CochainComplex A ℤ) (hL : KFlatLeft (curriedTensor A) L) :
    KFlatLeft (curriedTensor A') ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  (kFlatLeft_iff_kFlat_flip _ _).2
    (kFlat_map_of_retract (curriedTensor A).flip (curriedTensor A').flip G G G
      (fun a b => (Functor.Monoidal.μIso G b a).symm)
      (fun f b => (Functor.OplaxMonoidal.δ_natural_right G b f).symm)
      (fun a _ _ g => (Functor.OplaxMonoidal.δ_natural_left G g a).symm) hG L
      ((kFlatLeft_iff_kFlat_flip _ _).1 hL))

end Single

section Family

variable {ι : Type*} (G : ι → A ⥤ A') [∀ i, (G i).Additive] [∀ i, (G i).Monoidal]
  [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
  [∀ i (n : ℤ), PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) (G i)]
  (hG : JointlyReflectIsomorphisms G)

include hG in
/-- **K-flatness is detected by a jointly conservative family of exact strong monoidal
functors**, for the tensor products. -/
theorem kFlat_of_forall_kFlat_map_of_monoidal
    [∀ i (K L : CochainComplex A ℤ),
      HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex (G i)
        ((((curriedTensor A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
    (L : CochainComplex A ℤ)
    (hL : ∀ i, KFlat (curriedTensor A') (((G i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    KFlat (curriedTensor A) L :=
  kFlat_of_forall_kFlat_map (curriedTensor A) (curriedTensor A') G G G
    (fun i a b => (Functor.Monoidal.μIso (G i) a b).symm)
    (fun i _ _ f b => (Functor.OplaxMonoidal.δ_natural_left (G i) f b).symm)
    (fun i a _ _ g => (Functor.OplaxMonoidal.δ_natural_right (G i) a g).symm) hG
    (fun i _ hN => hN.map (G i)) L hL

include hG in
/-- **Left K-flatness is detected by a jointly conservative family of exact strong monoidal
functors**, for the tensor products. -/
theorem kFlatLeft_of_forall_kFlatLeft_map_of_monoidal
    [(curriedTensor A).flip.Additive] [∀ X : A, ((curriedTensor A).flip.obj X).Additive]
    [∀ (K₁ K₂ : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A).flip (ComplexShape.up ℤ)]
    [(curriedTensor A').flip.Additive] [∀ X : A', ((curriedTensor A').flip.obj X).Additive]
    [∀ (K₁ K₂ : CochainComplex A' ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A').flip (ComplexShape.up ℤ)]
    [∀ i (K L : CochainComplex A ℤ),
      HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex (G i)
        ((((curriedTensor A).flip.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
    (L : CochainComplex A ℤ)
    (hL : ∀ i, KFlatLeft (curriedTensor A')
      (((G i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    KFlatLeft (curriedTensor A) L :=
  (kFlatLeft_iff_kFlat_flip _ _).2
    (kFlat_of_forall_kFlat_map (curriedTensor A).flip (curriedTensor A').flip G G G
      (fun i a b => (Functor.Monoidal.μIso (G i) b a).symm)
      (fun i _ _ f b => (Functor.OplaxMonoidal.δ_natural_right (G i) b f).symm)
      (fun i a _ _ g => (Functor.OplaxMonoidal.δ_natural_left (G i) g a).symm) hG
      (fun i _ hN => hN.map (G i)) L (fun i => (kFlatLeft_iff_kFlat_flip _ _).1 (hL i)))

end Family

end Monoidal

end CochainComplex.KFlatBifunctor
