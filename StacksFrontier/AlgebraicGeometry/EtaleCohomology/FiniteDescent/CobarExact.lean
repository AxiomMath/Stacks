module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.MonadCobar
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# The cobar resolution of a monad is exact when the left adjoint reflects exactness

Let `L ⊣ R` be an adjunction between abelian categories, with `L` additive, and let `T = L ⋙ R`
be the induced monad on `A`. The cobar, or Godement, resolution of an object `X : A` is the
augmented complex
`0 ⟶ X ⟶ T X ⟶ T² X ⟶ T³ X ⟶ ⋯`,
whose differentials are the alternating sums of the cofaces built from the unit of the
adjunction. `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.MonadCobar` builds it,
in `Aᵒᵖ`, as an augmented simplicial object which carries an extra degeneracy once `L` has been
applied, hence has contractible alternating face map complex. Here that contraction is converted
into exactness of the cobar complex itself.

The passage from `B` back to `A` is by two hypotheses on `L`, which in the geometric case are
discharged by `exact_of_exact_map_smallEtalePullbackAb` and
`mono_of_mono_smallEtalePullbackAb_map` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.PullbackConservative`: `L` reflects
exactness of short complexes, and `L` reflects monomorphisms. The monomorphism `X ⟶ T X` needs no
homological input at all: the triangle identity `L(η_X) ≫ ε_{L X} = 1` makes `L(η_X)` a split
monomorphism, and `L` reflects monomorphisms.

The contraction is used only through one elementary consequence of it. In a chain complex `K`
with a homotopy equivalence to a complex `S` concentrated in degree `0`, the homotopy
`hom ≫ inv ≃ 𝟙 K` writes the identity of `K_{n+1}` as `d ≫ a + b ≫ d`, and such a factorization
of the identity of the middle object of a short complex forces exactness there: the kernel of the
second map factors through the first. No homology is computed, and the same argument covers the
degree-`0` spot, where the relevant short complex `K_1 ⟶ K_0 ⟶ S_0` involves the augmentation
instead of a differential of `K`.

## Main results

* `Stacks.Cobar.exact_of_id_eq_comp_add_comp`: a short complex whose middle identity factors as
  `g ≫ a + b ≫ f` is exact.
* `Stacks.Cobar.exact_of_homotopyEquiv_succ` and `Stacks.Cobar.exact_zero_of_homotopyEquiv`: a
  chain complex homotopy equivalent to a complex concentrated in degree `0` is exact at every
  spot `n + 1`, and its augmented short complex `K_1 ⟶ K_0 ⟶ S_0` is exact as well.
* `Stacks.Cobar.exists_exact_cobar`: **the cobar resolution is exact.** For an adjunction
  `L ⊣ R` between abelian categories with `L` additive, reflecting exactness and reflecting
  monomorphisms, the augmented cobar complex `0 ⟶ X ⟶ T X ⟶ T² X ⟶ ⋯` of any `X : A` is exact.

## References

* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
* [Stacks Project, Tag 0G5P](https://stacks.math.columbia.edu/tag/0G5P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe v₁ v₂ u₁ u₂

namespace Stacks.Cobar

/-! ### Exactness from a factorization of the identity -/

/-- A short complex `X₁ ⟶ X₂ ⟶ X₃` in an abelian category is exact as soon as the identity of its
middle object factors as `g ≫ a + b ≫ f`: the kernel of `g` is then its own image under
`(- ≫ b) ≫ f`, so it factors through `f`. -/
public theorem exact_of_id_eq_comp_add_comp {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (S : ShortComplex C) (a : S.X₃ ⟶ S.X₂) (b : S.X₂ ⟶ S.X₁)
    (hab : S.g ≫ a + b ≫ S.f = 𝟙 S.X₂) : S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  have h1 := congrArg (fun φ => kernel.ι S.g ≫ φ) hab
  simp only [Preadditive.comp_add, ← Category.assoc, kernel.condition, zero_comp, zero_add,
    Category.comp_id] at h1
  rw [← h1, Category.assoc, cokernel.condition, comp_zero]

/-- Exactness transported along isomorphisms of the three objects of a short complex: if both
squares commute, an exact short complex stays exact. -/
public theorem exact_of_iso_conj {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {Y₁ Y₂ Y₃ Y₁' Y₂' Y₃' : C} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃} {hfg : f ≫ g = 0}
    {f' : Y₁' ⟶ Y₂'} {g' : Y₂' ⟶ Y₃'} {hfg' : f' ≫ g' = 0}
    (e₁ : Y₁ ≅ Y₁') (e₂ : Y₂ ≅ Y₂') (e₃ : Y₃ ≅ Y₃')
    (hf : e₁.hom ≫ f' = f ≫ e₂.hom) (hg : e₂.hom ≫ g' = g ≫ e₃.hom)
    (h : (ShortComplex.mk f g hfg).Exact) : (ShortComplex.mk f' g' hfg').Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := ShortComplex.mk f g hfg)
    (S₂ := ShortComplex.mk f' g' hfg') e₁ e₂ e₃ hf hg) h

/-! ### Contractible chain complexes are exact -/

section Contractible

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {K S : ChainComplex C ℕ}

/-- A chain complex homotopy equivalent to a complex `S` vanishing in positive degrees is exact
at every spot `n + 1`: the homotopy `hom ≫ inv ≃ 𝟙 K` factors the identity of `K_{n+1}` as
`d ≫ a + b ≫ d`, because `hom ≫ inv` itself vanishes in degree `n + 1`. -/
public theorem exact_of_homotopyEquiv_succ (he : HomotopyEquiv K S)
    (hS : ∀ n : ℕ, IsZero (S.X (n + 1))) (n : ℕ) :
    (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n) (K.d_comp_d _ _ _)).Exact := by
  refine exact_of_id_eq_comp_add_comp _ (-(he.homotopyHomInvId.hom n (n + 1)))
    (-(he.homotopyHomInvId.hom (n + 1) (n + 2))) ?_
  have hc := he.homotopyHomInvId.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, (hS n).eq_zero_of_tgt (he.hom.f (n + 1)), zero_comp] at hc
  change K.d (n + 1) n ≫ (-(he.homotopyHomInvId.hom n (n + 1)))
      + (-(he.homotopyHomInvId.hom (n + 1) (n + 2))) ≫ K.d (n + 2) (n + 1) = 𝟙 (K.X (n + 1))
  rw [Preadditive.comp_neg, Preadditive.neg_comp, ← neg_add,
    add_eq_zero_iff_eq_neg.mp hc.symm, neg_neg]

/-- The degree-`0` component of a homotopy equivalence to a complex vanishing in positive degrees
kills the image of the first differential: it is a chain map into a complex whose differentials
all vanish. -/
public theorem d_one_zero_comp_hom_f_zero (he : HomotopyEquiv K S)
    (hS : ∀ n : ℕ, IsZero (S.X (n + 1))) : K.d 1 0 ≫ he.hom.f 0 = 0 := by
  rw [← he.hom.comm 1 0, (hS 0).eq_zero_of_src (S.d 1 0), comp_zero]

/-- **The degree-`0` spot.** For a chain complex `K` homotopy equivalent to a complex `S`
vanishing in positive degrees, the *augmented* short complex `K_1 ⟶ K_0 ⟶ S_0` is exact: the
homotopy `hom ≫ inv ≃ 𝟙 K` factors the identity of `K_0` as `hom_0 ≫ inv_0 - h ≫ d_1`. -/
public theorem exact_zero_of_homotopyEquiv (he : HomotopyEquiv K S)
    (hS : ∀ n : ℕ, IsZero (S.X (n + 1))) :
    (ShortComplex.mk (K.d 1 0) (he.hom.f 0) (d_one_zero_comp_hom_f_zero he hS)).Exact := by
  refine exact_of_id_eq_comp_add_comp _ (he.inv.f 0) (-(he.homotopyHomInvId.hom 0 1)) ?_
  have hc := he.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add,
    HomologicalComplex.comp_f, HomologicalComplex.id_f] at hc
  change he.hom.f 0 ≫ he.inv.f 0 + (-(he.homotopyHomInvId.hom 0 1)) ≫ K.d 1 0 = 𝟙 (K.X 0)
  rw [hc, Preadditive.neg_comp]
  abel

end Contractible

/-! ### The alternating face map complex and its augmentation -/

/-- An additive functor commutes with the differential of the alternating face map complex: that
differential is an alternating sum of faces, and an additive functor preserves sums and
`ℤ`-scalings. -/
public theorem map_alternatingFaceMapComplex_d {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (Y : SimplicialObject C) (n : ℕ) :
    (AlternatingFaceMapComplex.obj (Y ⋙ F)).d (n + 1) n
      = F.map ((AlternatingFaceMapComplex.obj Y).d (n + 1) n) := by
  rw [AlternatingFaceMapComplex.obj_d_eq, AlternatingFaceMapComplex.obj_d_eq, F.map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [F.map_zsmul]; rfl

/-- The augmentation of an augmented simplicial object kills the first differential of the
alternating face map complex of its underlying simplicial object: this is the chain-map property
of `AlternatingFaceMapComplex.ε`. -/
public theorem d_one_zero_comp_hom_app_zero {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] (Y : SimplicialObject.Augmented C) :
    (AlternatingFaceMapComplex.obj Y.left).d 1 0 ≫ Y.hom.app (op ⦋0⦌) = 0 := by
  have hc := (AlternatingFaceMapComplex.ε.app Y).comm 1 0
  rw [AlternatingFaceMapComplex.ε_app_f_zero,
    (show ((SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C).obj Y).d 1 0 = 0 from
      HomologicalComplex.single_obj_d _ _ _ _ _), comp_zero] at hc
  exact hc.symm

/-- Passing to opposites turns a vanishing composite `f ≫ g = 0` into `g.unop ≫ f.unop = 0`. -/
private theorem unop_comp_eq_zero {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) : g.unop ≫ f.unop = 0 := by
  rw [← unop_comp, h, unop_zero]

/-! ### The contraction of the image of the cobar resolution -/

section Contraction

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {L : A ⥤ B} {R : B ⥤ A} [Preadditive B] [HasZeroObject B] (adj : L ⊣ R) (X : A)

/-- **The contraction, with its augmentation named.** This is
`Stacks.Cobar.exists_homotopyEquiv_alternatingFaceMapComplex` with one extra piece of information
retained: the degree-`0` component of the homotopy equivalence is the `L`-image of the
augmentation of the cobar resolution. That is what identifies the degree-`0` spot of the
contraction with the unit of the adjunction. -/
public theorem exists_homotopyEquiv_hom_f_zero (Z : SimplicialObject.Augmented Aᵒᵖ)
    (h : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = ((mnd L R).op.iterate (n + 1)).obj (op X))
    (hZ : Z.right = op X)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      Z.left.δ j = eqToHom (h (n + 1)) ≫
        (Godement.face (cod adj) (n + 1) j).app (op X) ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)),
      Z.left.σ j = eqToHom (h n) ≫
        (Godement.degeneracy (cos adj) n j).app (op X) ≫ eqToHom (h (n + 1)).symm)
    (hhom : Z.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ (cod adj).app (op X) ≫ eqToHom hZ.symm) :
    ∃ he : HomotopyEquiv
      (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z)))
      ((ChainComplex.single₀ Bᵒᵖ).obj (SimplicialObject.Augmented.point.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))),
      he.hom.f 0 = L.op.map (Z.hom.app (op ⦋0⦌)) :=
  ⟨(extraDegeneracy adj X ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z)
      (fun n => congrArg L.op.obj (h n)) (congrArg L.op.obj hZ)
      (fun n j => Godement.Prep.map_eq_eqToHom_comp L.op (hδ n j))
      (fun n j => Godement.Prep.map_eq_eqToHom_comp L.op (hσ n j))
      ((Category.comp_id _).trans (Godement.Prep.map_eq_eqToHom_comp L.op hhom))).homotopyEquiv,
    (AlternatingFaceMapComplex.ε_app_f_zero _).trans (Category.comp_id _)⟩

end Contraction

/-! ### Exactness of the cobar resolution -/

/-- **The cobar resolution is exact.**
Let `L ⊣ R` be an adjunction between abelian categories with `L` additive, and assume `L`
reflects exactness of short complexes and reflects monomorphisms. Let `T = L ⋙ R` be the induced
monad on `A` and let `X : A`. Then the augmented cobar complex
`0 ⟶ X ⟶ T X ⟶ T² X ⟶ T³ X ⟶ ⋯`
is exact: there are differentials `d n : T^{n+1} X ⟶ T^{n+2} X`, composing to zero with one
another and with the unit `η_X : X ⟶ T X`, such that `η_X` is a monomorphism and the complex is
exact at `T X` and at every `T^{n+2} X`. -/
public theorem exists_exact_cobar
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [L.Additive]
    (hrefl : ∀ S : ShortComplex A, (S.map L).Exact → S.Exact)
    (hmono : ∀ {P Q : A} (φ : P ⟶ Q), Mono (L.map φ) → Mono φ)
    (X : A) :
    ∃ (d : ∀ n : ℕ, ((Stacks.Cobar.mnd L R).iterate (n + 1)).obj X ⟶
          ((Stacks.Cobar.mnd L R).iterate (n + 2)).obj X)
      (haug : adj.unit.app X ≫ d 0 = 0)
      (hdd : ∀ n : ℕ, d n ≫ d (n + 1) = 0),
      Mono (adj.unit.app X) ∧ (ShortComplex.mk _ _ haug).Exact ∧
        ∀ n : ℕ, (ShortComplex.mk _ _ (hdd n)).Exact := by
  obtain ⟨Z, h, hZ, hobj, hδ, hσ, hhom⟩ := exists_augmented_cobar adj X
  obtain ⟨he, hε⟩ := exists_homotopyEquiv_hom_f_zero adj X Z h hZ hδ hσ hhom
  have hd : ∀ n : ℕ,
      (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).d (n + 1) n
        = L.op.map ((AlternatingFaceMapComplex.obj Z.left).d (n + 1) n) :=
    map_alternatingFaceMapComplex_d L.op Z.left
  have hS : ∀ n : ℕ, IsZero (((ChainComplex.single₀ Bᵒᵖ).obj
      (SimplicialObject.Augmented.point.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).X (n + 1)) :=
    fun n => HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)
  have hhom' : Z.hom.app (op ⦋0⦌)
      = eqToHom (hobj 0) ≫ (adj.unit.app X).op ≫ eqToHom hZ.symm := hhom
  -- the differentials of the cobar complex, read in `Aᵒᵖ`
  obtain ⟨D, hD⟩ : ∃ D : ∀ n : ℕ, op (((mnd L R).iterate (n + 2)).obj X) ⟶
        op (((mnd L R).iterate (n + 1)).obj X),
      ∀ n : ℕ, D n = eqToHom (hobj (n + 1)).symm ≫
        (AlternatingFaceMapComplex.obj Z.left).d (n + 1) n ≫ eqToHom (hobj n) :=
    ⟨_, fun _ => rfl⟩
  have hz : ∀ (i j k : ℕ) {W : Aᵒᵖ} (u : (AlternatingFaceMapComplex.obj Z.left).X k ⟶ W),
      (AlternatingFaceMapComplex.obj Z.left).d i j ≫
        (AlternatingFaceMapComplex.obj Z.left).d j k ≫ u = 0 := by
    intro i j k W u
    rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
  have hDD : ∀ n : ℕ, D (n + 1) ≫ D n = 0 := by
    intro n
    rw [hD (n + 1), hD n]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hz, comp_zero]
  have hdd : ∀ n : ℕ, (D n).unop ≫ (D (n + 1)).unop = 0 := fun n =>
    unop_comp_eq_zero _ _ (hDD n)
  -- the augmentation of the cobar resolution is the unit of the adjunction
  have hunit : eqToHom (hobj 0) ≫ (adj.unit.app X).op = Z.hom.app (op ⦋0⦌) ≫ eqToHom hZ := by
    rw [hhom']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have haug : adj.unit.app X ≫ (D 0).unop = 0 := by
    have hzero : (AlternatingFaceMapComplex.obj Z.left).d (0 + 1) 0 ≫ Z.hom.app (op ⦋0⦌)
        ≫ eqToHom hZ = 0 := by
      rw [← Category.assoc, (show (AlternatingFaceMapComplex.obj Z.left).d (0 + 1) 0 ≫
        Z.hom.app (op ⦋0⦌) = 0 from d_one_zero_comp_hom_app_zero Z), zero_comp]
    have hD0 : D 0 ≫ (adj.unit.app X).op = 0 := by
      rw [hD 0, Category.assoc, Category.assoc, hunit, hzero, comp_zero]
    exact unop_comp_eq_zero _ _ hD0
  -- the two complexes have the same differentials after applying `L`
  have hf : ∀ n : ℕ, L.op.map (eqToHom (hobj (n + 1))) ≫ L.op.map (D n)
      = (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
          ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).d (n + 1) n
        ≫ L.op.map (eqToHom (hobj n)) := by
    intro n
    rw [← Functor.map_comp, hD n]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [Functor.map_comp, ← hd n]
    rfl
  have hg0 : L.op.map (eqToHom (hobj 0)) ≫ L.op.map ((adj.unit.app X).op)
      = he.hom.f 0 ≫ L.op.map (eqToHom hZ) := by
    rw [← Functor.map_comp, hunit, Functor.map_comp, hε]
    rfl
  -- the unit is a split monomorphism after applying `L`, hence a monomorphism
  have hmono' : Mono (adj.unit.app X) := by
    have : IsSplitMono (L.map (adj.unit.app X)) :=
      ⟨⟨⟨adj.counit.app (L.obj X), adj.left_triangle_components X⟩⟩⟩
    exact hmono (adj.unit.app X) inferInstance
  refine ⟨fun n => (D n).unop, haug, hdd, hmono', ?_, ?_⟩
  · exact hrefl _ ((ShortComplex.exact_op_iff _).mp (exact_of_iso_conj
      (L.op.mapIso (eqToIso (hobj 1))) (L.op.mapIso (eqToIso (hobj 0)))
      (L.op.mapIso (eqToIso hZ)) (hf 0) hg0 (exact_zero_of_homotopyEquiv he hS)))
  · exact fun n => hrefl _ ((ShortComplex.exact_op_iff _).mp (exact_of_iso_conj
      (L.op.mapIso (eqToIso (hobj (n + 1 + 1)))) (L.op.mapIso (eqToIso (hobj (n + 1))))
      (L.op.mapIso (eqToIso (hobj n))) (hf (n + 1)) (hf n)
      (exact_of_homotopyEquiv_succ he hS n)))

end Stacks.Cobar

end
