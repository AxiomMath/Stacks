module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyDecalage

/-!
# Dévissage for the Alexander–Whitney map

A short complex of simplicial objects which is split in every simplicial degree — not
necessarily split as a complex of simplicial objects — is carried to a short exact sequence of
chain complexes by both sides of the Alexander–Whitney comparison: the degreewise splitting
survives tensoring, and the summands of the tensor complex are tensored degreewise. The
Alexander–Whitney map is a morphism between those two short exact sequences, so the long exact
homology sequences compare, and the degree in which the comparison is an isomorphism can be
raised by one. This is the inductive step of the dévissage.

## Main definitions

* `AlgebraicTopology.alexanderWhitneyNatTrans`: the Alexander–Whitney map as a natural
  transformation in the second simplicial object.
* `AlgebraicTopology.tensorGradedHom`: a degreewise morphism of complexes, tensored on the left
  with a fixed complex in each summand of the tensor complex.

## Main results

* `AlgebraicTopology.shortExact_map_tensorLeft_alternatingFaceMapComplex` and
  `AlgebraicTopology.shortExact_map_tensorComplex`: the two short exact sequences.
* `AlgebraicTopology.epi_homologyMap_alexanderWhitney_of_splitting` and
  `AlgebraicTopology.mono_homologyMap_alexanderWhitney_of_splitting`: the inductive steps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory

open scoped Simplicial

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]

/-! ### The two functors and the comparison between them -/

/-- Tensoring a chain complex on the left with a fixed chain complex, as a functor. -/
public def tensorLeftComplex (K : ChainComplex C ℕ) : ChainComplex C ℕ ⥤ ChainComplex C ℕ :=
  ((curriedTensor C).map₂HomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)).obj K

/-- Tensoring on the left with a fixed chain complex is an additive functor. -/
public instance tensorLeftComplex_additive (K : ChainComplex C ℕ) :
    (tensorLeftComplex K).Additive where
  map_add {L L'} φ ψ := by
    change HomologicalComplex.tensorHom (𝟙 K) (φ + ψ) =
      HomologicalComplex.tensorHom (𝟙 K) φ + HomologicalComplex.tensorHom (𝟙 K) ψ
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
    simp only [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.add_f_apply,
      Preadditive.comp_add, HomologicalComplex.id_f, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.id_whiskerRight,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- Tensoring on the left with a fixed simplicial object is an additive functor. -/
public instance tensorLeft_additive (M : SimplicialObject C) :
    (MonoidalCategory.tensorLeft M).Additive where
  map_add {X Y} f g := by
    change M ◁ (f + g) = M ◁ f + M ◁ g
    ext Z
    change M.obj Z ◁ (f + g).app Z = M.obj Z ◁ f.app Z + M.obj Z ◁ g.app Z
    rw [NatTrans.app_add, MonoidalPreadditive.whiskerLeft_add]

/-- The functor `tensorLeftComplex K` sends `L` to the tensor complex of `K` and `L`. -/
public lemma tensorLeftComplex_obj (K L : ChainComplex C ℕ) :
    (tensorLeftComplex K).obj L = HomologicalComplex.tensorObj K L := rfl

/-- The functor `tensorLeftComplex K` sends `φ` to the tensor product of `𝟙 K` with `φ`. -/
public lemma tensorLeftComplex_map (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (φ : L ⟶ L') : (tensorLeftComplex K).map φ = HomologicalComplex.tensorHom (𝟙 K) φ := rfl

variable (M : SimplicialObject C)

/-- The Alexander–Whitney map as a natural transformation: from the alternating face map complex
of the degreewise tensor product with `M` to the tensor product of the alternating face map
complex of `M` with the alternating face map complex. -/
public def alexanderWhitneyNatTrans :
    tensorLeft M ⋙ alternatingFaceMapComplex C ⟶
      alternatingFaceMapComplex C ⋙ tensorLeftComplex ((alternatingFaceMapComplex C).obj M) where
  app N := alexanderWhitney M N
  naturality N _N' g := (alexanderWhitney_naturality_right M N g).symm

/-! ### The degreewise splitting -/

/-- A degreewise morphism of chain complexes, tensored on the left with a fixed complex in each
summand of the tensor complex. -/
public def tensorGradedHom (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (ρ : ∀ q : ℕ, L.X q ⟶ L'.X q) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶ (HomologicalComplex.tensorObj K L').X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => (K.X p ◁ ρ q) ≫
    HomologicalComplex.ιTensorObj K L' p q n h)

/-- On the summand indexed by `p + q = n`, `tensorGradedHom K ρ n` is `K.X p ◁ ρ q`. -/
@[reassoc]
public lemma ι_tensorGradedHom (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (ρ : ∀ q : ℕ, L.X q ⟶ L'.X q) (n p q : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ tensorGradedHom K ρ n =
      (K.X p ◁ ρ q) ≫ HomologicalComplex.ιTensorObj K L' p q n h :=
  HomologicalComplex.ι_mapBifunctorDesc _ _ _ h

/-- On the summand indexed by `p + q = n`, `𝟙 K ⊗ φ` is `K.X p ◁ φ.f q`. -/
@[reassoc] private theorem ι_tensorHom_id_f (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (φ : L ⟶ L') (n p q : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom (𝟙 K) φ).f n =
      (K.X p ◁ φ.f q) ≫ HomologicalComplex.ιTensorObj K L' p q n h := by
  simp

/-- A degreewise retraction `ρ` of `φ` gives, after tensoring with `K`, a degreewise retraction
of `𝟙 K ⊗ φ`. -/
public lemma tensorHom_comp_tensorGradedHom (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (φ : L ⟶ L') (ρ : ∀ q : ℕ, L'.X q ⟶ L.X q) (hρ : ∀ q, φ.f q ≫ ρ q = 𝟙 _) (n : ℕ) :
    (HomologicalComplex.tensorHom (𝟙 K) φ).f n ≫ tensorGradedHom K ρ n = 𝟙 _ := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  rw [ι_tensorHom_id_f_assoc, ι_tensorGradedHom, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, hρ q]
  simp

/-- A degreewise section `σ` of `φ` gives, after tensoring with `K`, a degreewise section
of `𝟙 K ⊗ φ`. -/
public lemma tensorGradedHom_comp_tensorHom (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (φ : L ⟶ L') (σ : ∀ q : ℕ, L'.X q ⟶ L.X q) (hσ : ∀ q, σ q ≫ φ.f q = 𝟙 _) (n : ℕ) :
    tensorGradedHom K σ n ≫ (HomologicalComplex.tensorHom (𝟙 K) φ).f n = 𝟙 _ := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  rw [ι_tensorGradedHom_assoc, ι_tensorHom_id_f, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, hσ q]
  simp

/-- A degreewise splitting identity `ρ ≫ φ + ψ ≫ σ = 𝟙` survives tensoring on the left
with `K`. -/
public lemma tensorGradedHom_add_comp (K : ChainComplex C ℕ) {L L' L'' : ChainComplex C ℕ}
    (φ : L ⟶ L') (ψ : L' ⟶ L'') (ρ : ∀ q : ℕ, L'.X q ⟶ L.X q)
    (σ : ∀ q : ℕ, L''.X q ⟶ L'.X q)
    (hid : ∀ q, ρ q ≫ φ.f q + ψ.f q ≫ σ q = 𝟙 _) (n : ℕ) :
    tensorGradedHom K ρ n ≫ (HomologicalComplex.tensorHom (𝟙 K) φ).f n +
      (HomologicalComplex.tensorHom (𝟙 K) ψ).f n ≫ tensorGradedHom K σ n = 𝟙 _ := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  rw [Preadditive.comp_add, ι_tensorGradedHom_assoc, ι_tensorHom_id_f_assoc, ι_tensorGradedHom,
    ι_tensorHom_id_f, ← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← Preadditive.add_comp,
    ← MonoidalPreadditive.whiskerLeft_add, hid q]
  simp

/-! ### The two short exact sequences -/

variable (S : ShortComplex (SimplicialObject C))
  (r : ∀ q : ℕ, S.X₂ _⦋q⦌ ⟶ S.X₁ _⦋q⦌) (σ : ∀ q : ℕ, S.X₃ _⦋q⦌ ⟶ S.X₂ _⦋q⦌)

/-- The degreewise splitting of the alternating face map complexes of the degreewise tensor
product with `M`. -/
public def mooreSplitting (hr : ∀ q, S.f.app (op ⦋q⦌) ≫ r q = 𝟙 _)
    (hσ : ∀ q, σ q ≫ S.g.app (op ⦋q⦌) = 𝟙 _)
    (hid : ∀ q, r q ≫ S.f.app (op ⦋q⦌) + S.g.app (op ⦋q⦌) ≫ σ q = 𝟙 _) (n : ℕ) :
    ((S.map (tensorLeft M ⋙ alternatingFaceMapComplex C)).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting where
  r := M _⦋n⦌ ◁ r n
  s := M _⦋n⦌ ◁ σ n
  f_r := by
    change (M _⦋n⦌ ◁ S.f.app (op ⦋n⦌)) ≫ (M _⦋n⦌ ◁ r n) = _
    rw [← MonoidalCategory.whiskerLeft_comp, hr n, MonoidalCategory.whiskerLeft_id]
    rfl
  s_g := by
    change (M _⦋n⦌ ◁ σ n) ≫ (M _⦋n⦌ ◁ S.g.app (op ⦋n⦌)) = _
    rw [← MonoidalCategory.whiskerLeft_comp, hσ n, MonoidalCategory.whiskerLeft_id]
    rfl
  id := by
    change (M _⦋n⦌ ◁ r n) ≫ (M _⦋n⦌ ◁ S.f.app (op ⦋n⦌)) +
      (M _⦋n⦌ ◁ S.g.app (op ⦋n⦌)) ≫ (M _⦋n⦌ ◁ σ n) = _
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalPreadditive.whiskerLeft_add, hid n, MonoidalCategory.whiskerLeft_id]
    rfl

/-- The alternating face map complexes of the degreewise tensor product with `M` form a short
exact sequence. -/
public lemma shortExact_map_tensorLeft_alternatingFaceMapComplex
    (hr : ∀ q, S.f.app (op ⦋q⦌) ≫ r q = 𝟙 _)
    (hσ : ∀ q, σ q ≫ S.g.app (op ⦋q⦌) = 𝟙 _)
    (hid : ∀ q, r q ≫ S.f.app (op ⦋q⦌) + S.g.app (op ⦋q⦌) ≫ σ q = 𝟙 _) :
    (S.map (tensorLeft M ⋙ alternatingFaceMapComplex C)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => (mooreSplitting M S r σ hr hσ hid n).shortExact

/-- The degreewise splitting of the tensor complexes. -/
public def tensorSplitting (hr : ∀ q, S.f.app (op ⦋q⦌) ≫ r q = 𝟙 _)
    (hσ : ∀ q, σ q ≫ S.g.app (op ⦋q⦌) = 𝟙 _)
    (hid : ∀ q, r q ≫ S.f.app (op ⦋q⦌) + S.g.app (op ⦋q⦌) ≫ σ q = 𝟙 _) (n : ℕ) :
    ((S.map (alternatingFaceMapComplex C ⋙
      tensorLeftComplex ((alternatingFaceMapComplex C).obj M))).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting where
  r := tensorGradedHom ((alternatingFaceMapComplex C).obj M)
    (fun q => (show ((alternatingFaceMapComplex C).obj S.X₂).X q ⟶
      ((alternatingFaceMapComplex C).obj S.X₁).X q from r q)) n
  s := tensorGradedHom ((alternatingFaceMapComplex C).obj M)
    (fun q => (show ((alternatingFaceMapComplex C).obj S.X₃).X q ⟶
      ((alternatingFaceMapComplex C).obj S.X₂).X q from σ q)) n
  f_r := tensorHom_comp_tensorGradedHom _ ((alternatingFaceMapComplex C).map S.f) _
    (fun q => hr q) n
  s_g := tensorGradedHom_comp_tensorHom _ ((alternatingFaceMapComplex C).map S.g) _
    (fun q => hσ q) n
  id := tensorGradedHom_add_comp _ ((alternatingFaceMapComplex C).map S.f)
    ((alternatingFaceMapComplex C).map S.g) _ _ (fun q => hid q) n

/-- The tensor complexes form a short exact sequence. -/
public lemma shortExact_map_tensorComplex
    (hr : ∀ q, S.f.app (op ⦋q⦌) ≫ r q = 𝟙 _)
    (hσ : ∀ q, σ q ≫ S.g.app (op ⦋q⦌) = 𝟙 _)
    (hid : ∀ q, r q ≫ S.f.app (op ⦋q⦌) + S.g.app (op ⦋q⦌) ≫ σ q = 𝟙 _) :
    (S.map (alternatingFaceMapComplex C ⋙
      tensorLeftComplex ((alternatingFaceMapComplex C).obj M))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => (tensorSplitting M S r σ hr hσ hid n).shortExact


/-! ### The inductive steps -/

variable (hr : ∀ q, S.f.app (op ⦋q⦌) ≫ r q = 𝟙 _)
  (hσ : ∀ q, σ q ≫ S.g.app (op ⦋q⦌) = 𝟙 _)
  (hid : ∀ q, r q ≫ S.f.app (op ⦋q⦌) + S.g.app (op ⦋q⦌) ≫ σ q = 𝟙 _)

include hr hσ hid in
/-- **The epimorphism step of the dévissage.** For a degreewise split short complex of
simplicial objects whose middle term the Alexander–Whitney map inverts, the comparison for the
quotient is epi on homology in degree `n + 1` as soon as the comparison for the sub is epi on
homology in degree `n`. -/
public lemma epi_homologyMap_alexanderWhitney_of_splitting
    (hM₂ : QuasiIso (alexanderWhitney M S.X₂)) (n : ℕ)
    (hM₁ : Epi (HomologicalComplex.homologyMap (alexanderWhitney M S.X₁) n)) :
    Epi (HomologicalComplex.homologyMap (alexanderWhitney M S.X₃) (n + 1)) := by
  have := hM₂
  refine HomologicalComplex.HomologySequence.epi_homologyMap_τ₃
    (ShortComplex.mapNatTrans S (alexanderWhitneyNatTrans M))
    (shortExact_map_tensorLeft_alternatingFaceMapComplex M S r σ hr hσ hid)
    (shortExact_map_tensorComplex M S r σ hr hσ hid) (n + 1) ?_ ?_ ?_
  · change Epi (HomologicalComplex.homologyMap (alexanderWhitney M S.X₂) (n + 1))
    infer_instance
  · intro j hj
    obtain rfl : j = n := by simpa using hj
    exact hM₁
  · intro j hj
    change Mono (HomologicalComplex.homologyMap (alexanderWhitney M S.X₂) j)
    infer_instance

include hr hσ hid in
/-- **The monomorphism step of the dévissage.** For a degreewise split short complex of
simplicial objects whose middle term the Alexander–Whitney map inverts, the comparison for the
quotient is mono on homology in degree `n` as soon as the comparison for the sub is epi on
homology in degree `n` and mono on homology in the preceding degree. -/
public lemma mono_homologyMap_alexanderWhitney_of_splitting
    (hM₂ : QuasiIso (alexanderWhitney M S.X₂)) (n : ℕ)
    (hM₁ : Epi (HomologicalComplex.homologyMap (alexanderWhitney M S.X₁) n))
    (hM₁' : ∀ j, (ComplexShape.down ℕ).Rel n j →
      Mono (HomologicalComplex.homologyMap (alexanderWhitney M S.X₁) j)) :
    Mono (HomologicalComplex.homologyMap (alexanderWhitney M S.X₃) n) := by
  have := hM₂
  refine HomologicalComplex.HomologySequence.mono_homologyMap_τ₃
    (ShortComplex.mapNatTrans S (alexanderWhitneyNatTrans M))
    (shortExact_map_tensorLeft_alternatingFaceMapComplex M S r σ hr hσ hid)
    (shortExact_map_tensorComplex M S r σ hr hσ hid) n ?_ ?_ ?_
  · exact hM₁
  · change Mono (HomologicalComplex.homologyMap (alexanderWhitney M S.X₂) n)
    infer_instance
  · exact fun j hj => hM₁' j hj

end AlgebraicTopology


end
