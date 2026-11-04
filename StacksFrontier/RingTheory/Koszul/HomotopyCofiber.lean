module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.RingTheory.Koszul.Cone
public meta import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Mapping cones of composite endomorphisms

Let `A` be a cochain complex in an additive category and let `f, g : A ⟶ A`. The mapping cone
of the composite `g ≫ f` is not determined by the cones of `f` and of `g`, but it is always
homotopy equivalent to the cone of a suitable morphism from a shift of one to the other. This
file records that comparison, obtained by rotating the octahedron triangle of the composite in
the homotopy category.

The comparison is then applied to Koszul complexes. Adjoining an element `f` to a linear
functional `φ : E →ₗ[R] R`, that is passing from `φ` to the functional `(e, r) ↦ φ e + f * r`
on `E × R`, replaces the Koszul complex of `φ` by the mapping cone of multiplication by `f` on
it; this is recorded here in Mathlib's `HomologicalComplex.homotopyCofiber` vocabulary. Combining
that description with the comparison above shows that adjoining a *product* `f * g` gives a
complex homotopy equivalent to the cone of a map from the shifted complex for `f` to the complex
for `g`, both for a general functional and for a finite sequence of ring elements extended by one
more entry.

## Main results

* `Koszul.exists_homotopyEquiv_mappingCone_comp`: the cone of a composite `g ≫ f` is homotopy
  equivalent to the cone of some morphism `(mappingCone f)⟦-1⟧ ⟶ mappingCone g`.
* `Koszul.koszulComplex_coprod_smul_id_iso_homotopyCofiber`: the Koszul complex of the functional
  obtained from `φ` by adjoining `f` is isomorphic to the homotopy cofiber of `f • 𝟙` on the
  Koszul complex of `φ`.
* `Koszul.exists_homotopyEquiv_koszulComplex_coprod_mul_mappingCone`: adjoining a product `f * g`
  to `φ` gives a complex homotopy equivalent to the cone of a map from the shifted complex for `f`
  to the complex for `g`.
* `Koszul.exists_homotopyEquiv_koszulComplex_snoc_mul_mappingCone`: the same statement for the
  Koszul complex of a finite sequence whose last entry is a product `f * g`.

## Implementation notes

The results are stated for arbitrary endomorphisms of a cochain complex in an additive category
with binary biproducts and a zero object; the Koszul-complex applications specialize them to
multiplication by ring elements on a complex of modules. The Stacks Project uses homological
indexing, so its shift `[1]` is the shift `[-1]` appearing here, after passing to Mathlib's
cohomological convention.

`Koszul.koszulComplex_coprod_smul_id_iso_homotopyCofiber` is
`Stacks.MappingCone.NatIndexed.koszulComplex_phiPrime_iso_cone`, stated there for the explicit
cone complex `Stacks.MappingCone.NatIndexed.coneComplex`, transported to Mathlib's
`HomologicalComplex.homotopyCofiber`.

The direct sum `E ⊕ R` is represented throughout by the product module `E × R`. The nonnegatively
indexed homological Koszul complexes are extended by zero to integer-indexed cochain complexes
along `ComplexShape.embeddingDownNat`, placing homological degree `n` in cohomological degree
`-n`; this extension commutes with forming cones. A sequence of length `n` is represented by a
function `Fin n → R`, and its Koszul complex is formed from the linear functional on `Fin n → R`
whose values on the standard basis are the entries of the sequence.

## References

* [Stacks Project, Tag 062A](https://stacks.math.columbia.edu/tag/062A)
* [Stacks Project, Tag 0628](https://stacks.math.columbia.edu/tag/0628)
* [Stacks Project, Tag 062B](https://stacks.math.columbia.edu/tag/062B)
* [Stacks Project, Tag 062C](https://stacks.math.columbia.edu/tag/062C)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Koszul

/-! ## The cone of a composite endomorphism -/

/-- The cone of a composite of two endomorphisms is homotopy equivalent to the cone of a map
from the shifted cone of the first endomorphism to the cone of the second. -/
@[stacks 062A]
theorem exists_homotopyEquiv_mappingCone_comp
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C]
    (A : CochainComplex C ℤ) (f g : A ⟶ A) :
    ∃ (φ : (CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧ ⟶
        CochainComplex.mappingCone g),
      Nonempty
        (HomotopyEquiv (CochainComplex.mappingCone (g ≫ f))
          (CochainComplex.mappingCone φ)) := by
  let T := CochainComplex.mappingConeCompTriangle g f
  let F := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let φ := T.invRotate.mor₁
  refine ⟨φ, ?_⟩
  have hT : F.mapTriangle.obj T ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingConeCompTriangleh_distinguished g f
  have hTi' : (F.mapTriangle.obj T).invRotate ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
    inv_rot_of_distTriang _ hT
  have hTi : F.mapTriangle.obj T.invRotate ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
    isomorphic_distinguished _ hTi' _ (F.mapTriangleInvRotateIso.app T).symm
  have hcone := HomotopyCategory.mappingCone_triangleh_distinguished φ
  obtain ⟨e, he₂, he₃⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T.invRotate) (CochainComplex.mappingCone.triangleh φ) hTi hcone
    (𝟙 _) (𝟙 _) (by
      show F.map φ ≫ 𝟙 _ = 𝟙 _ ≫ F.map φ
      simp)
  let α : F.mapTriangle.obj T.invRotate ⟶ CochainComplex.mappingCone.triangleh φ :=
    ⟨𝟙 _, 𝟙 _, e, by
      show F.map φ ≫ 𝟙 _ = 𝟙 _ ≫ F.map φ
      simp, he₂, he₃⟩
  have hα₁ : IsIso α.hom₁ := by dsimp [α]; exact IsIso.id _
  have hα₂ : IsIso α.hom₂ := by dsimp [α]; exact IsIso.id _
  have hα₃ : IsIso α.hom₃ := isIso₃_of_isIso₁₂ α hTi hcone hα₁ hα₂
  obtain ⟨q, hq⟩ := F.map_surjective α.hom₃
  have hqIso : IsIso (F.map q) := by rw [hq]; exact hα₃
  obtain ⟨E, -⟩ :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).mp hqIso
  exact ⟨E⟩

universe w

-- The cone objects of `Stacks.MappingCone.NatIndexed.coneComplex` are
-- `ModuleCat.of R (K.X (n+1) × K.X n)`, so recognizing an element of one as a pair requires
-- unfolding `coneX` and `ModuleCat.of`; the `change` steps in the proofs below rely on that.
set_option backward.isDefEq.respectTransparency false

open scoped ExteriorAlgebra
open Preadditive

/-! ## The enlarged Koszul complex as a homotopy cofiber

The explicit cone complex `Stacks.MappingCone.NatIndexed.coneComplex` is compared degreewise with
Mathlib's `HomologicalComplex.homotopyCofiber`, which transports
`Stacks.MappingCone.NatIndexed.koszulComplex_phiPrime_iso_cone` to the homotopy cofiber. -/

section

open Stacks.MappingCone.NatIndexed

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- The degreewise comparison between the homotopy cofiber of `g : K ⟶ K` and the explicit cone
complex of `g`: in degree `0` both are `K₀`, and in degree `n + 1` both are `K_{n+1} ⊕ Kₙ`, up to
the order of the two summands. -/
private noncomputable def cofiberToConeX
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) :
    (n : ℕ) → (HomologicalComplex.homotopyCofiber g).X n ≅
      (coneComplex K K g).X n
  | 0 => HomologicalComplex.homotopyCofiber.XIso g 0 (by simp)
  | n + 1 =>
    (HomologicalComplex.homotopyCofiber.XIsoBiprod g (n + 1) n (by simp)) ≪≫
      (biprod.braiding (K.X n) (K.X (n + 1))) ≪≫
        (ModuleCat.biprodIsoProd (K.X (n + 1)) (K.X n))

private theorem biprodIsoProd_hom_fst (M N : ModuleCat.{max u v} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫
      ModuleCat.ofHom (LinearMap.fst R M N) = biprod.fst := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).1
  simp

private theorem biprodIsoProd_hom_snd (M N : ModuleCat.{max u v} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫
      ModuleCat.ofHom (LinearMap.snd R M N) = biprod.snd := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).1
  simp

private theorem cofiber_XIsoBiprod_snd
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (HomologicalComplex.homotopyCofiber.XIsoBiprod g i j hij).hom ≫ biprod.snd =
      HomologicalComplex.homotopyCofiber.sndX g i := by
  obtain rfl := (ComplexShape.down ℕ).next_eq' hij
  simp only [HomologicalComplex.homotopyCofiber.sndX, dite_eq_left hij]

private theorem cofiberToConeX_succ_fst
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) (n : ℕ) :
    (cofiberToConeX K g (n + 1)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (K.X (n + 1)) (K.X n)) =
      HomologicalComplex.homotopyCofiber.sndX g (n + 1) := by
  simp only [cofiberToConeX, Iso.trans_hom, Category.assoc]
  rw [biprodIsoProd_hom_fst]
  simp only [biprod.braiding_hom, biprod.lift_fst]
  exact cofiber_XIsoBiprod_snd K g (n + 1) n (by simp)

private theorem cofiberToConeX_succ_snd
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) (n : ℕ) :
    (cofiberToConeX K g (n + 1)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1)) (K.X n)) =
      HomologicalComplex.homotopyCofiber.fstX g (n + 1) n (by simp) := by
  simp only [cofiberToConeX, Iso.trans_hom, Category.assoc]
  rw [biprodIsoProd_hom_snd]
  simp [biprod.braiding_hom, HomologicalComplex.homotopyCofiber.fstX]

private theorem coneD0_formula
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) :
    (coneComplex K K g).d 1 0 =
      ModuleCat.ofHom (LinearMap.fst R (K.X 1) (K.X 0)) ≫ K.d 1 0 +
      ModuleCat.ofHom (LinearMap.snd R (K.X 1) (K.X 0)) ≫ g.f 0 := by
  apply ModuleCat.hom_ext
  ext x
  show coneD0lin K K g x = _
  rfl

private theorem coneDS_fst_formula
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) (n : ℕ) :
    (coneComplex K K g).d (n + 1 + 1) (n + 1) ≫
        ModuleCat.ofHom (LinearMap.fst R (K.X (n + 1)) (K.X n)) =
      ModuleCat.ofHom (LinearMap.fst R (K.X (n + 1 + 1)) (K.X (n + 1))) ≫ K.d (n + 1 + 1) (n + 1) +
      ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1 + 1)) (K.X (n + 1))) ≫ g.f (n + 1) := by
  apply ModuleCat.hom_ext
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_ofHom,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
  simp only [coneComplex, ChainComplex.of.d]
  show (coneDSlin K K g n x).1 = _
  rfl

private theorem coneDS_snd_formula
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) (n : ℕ) :
    (coneComplex K K g).d (n + 1 + 1) (n + 1) ≫
        ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1)) (K.X n)) =
      -(ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1 + 1)) (K.X (n + 1))) ≫
        K.d (n + 1) n) := by
  apply ModuleCat.hom_ext
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_neg,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply]
  simp only [coneComplex, ChainComplex.of.d]
  show (coneDSlin K K g n x).2 = _
  rfl

private theorem cofiberToConeX_zero_hom
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) :
    (cofiberToConeX K g 0).hom =
      HomologicalComplex.homotopyCofiber.sndX g 0 := by
  simp [cofiberToConeX, HomologicalComplex.homotopyCofiber.sndX]

private theorem cofiberToConeX_comm
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) (n : ℕ) :
    (cofiberToConeX K g (n + 1)).hom ≫ (coneComplex K K g).d (n + 1) n =
      (HomologicalComplex.homotopyCofiber g).d (n + 1) n ≫
        (cofiberToConeX K g n).hom := by
  cases n with
  | zero =>
    rw [coneD0_formula]
    simp only [comp_add, ← Category.assoc]
    rw [cofiberToConeX_succ_fst, cofiberToConeX_succ_snd, cofiberToConeX_zero_hom]
    exact (add_comm _ _).trans
      (HomologicalComplex.homotopyCofiber.d_sndX g 1 0 (by simp)).symm
  | succ n =>
    have hf :
        ((cofiberToConeX K g (n + 1 + 1)).hom ≫
          (coneComplex K K g).d (n + 1 + 1) (n + 1)) ≫
            ModuleCat.ofHom (LinearMap.fst R (K.X (n + 1)) (K.X n)) =
        ((HomologicalComplex.homotopyCofiber g).d (n + 1 + 1) (n + 1) ≫
          (cofiberToConeX K g (n + 1)).hom) ≫
            ModuleCat.ofHom (LinearMap.fst R (K.X (n + 1)) (K.X n)) := by
      rw [Category.assoc, coneDS_fst_formula]
      simp only [comp_add, ← Category.assoc]
      rw [cofiberToConeX_succ_fst, cofiberToConeX_succ_snd]
      calc
        _ = HomologicalComplex.homotopyCofiber.fstX g (n + 1 + 1) (n + 1) (by simp) ≫
              g.f (n + 1) +
            HomologicalComplex.homotopyCofiber.sndX g (n + 1 + 1) ≫
              K.d (n + 1 + 1) (n + 1) := add_comm _ _
        _ = HomologicalComplex.homotopyCofiber.d g (n + 1 + 1) (n + 1) ≫
              HomologicalComplex.homotopyCofiber.sndX g (n + 1) :=
          (HomologicalComplex.homotopyCofiber.d_sndX g (n + 1 + 1) (n + 1)
            (by simp)).symm
        _ = _ := by
          rw [← cofiberToConeX_succ_fst K g n]
          rfl
    have hs :
        ((cofiberToConeX K g (n + 1 + 1)).hom ≫
          (coneComplex K K g).d (n + 1 + 1) (n + 1)) ≫
            ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1)) (K.X n)) =
        ((HomologicalComplex.homotopyCofiber g).d (n + 1 + 1) (n + 1) ≫
          (cofiberToConeX K g (n + 1)).hom) ≫
            ModuleCat.ofHom (LinearMap.snd R (K.X (n + 1)) (K.X n)) := by
      rw [Category.assoc, coneDS_snd_formula]
      simp only [comp_neg, ← Category.assoc]
      rw [cofiberToConeX_succ_snd]
      calc
        _ = HomologicalComplex.homotopyCofiber.d g (n + 1 + 1) (n + 1) ≫
            HomologicalComplex.homotopyCofiber.fstX g (n + 1) n (by simp) :=
          (HomologicalComplex.homotopyCofiber.d_fstX g (n + 1 + 1) (n + 1) n
            (by simp) (by simp)).symm
        _ = _ := by
          rw [← cofiberToConeX_succ_snd K g n]
          rfl
    apply ModuleCat.hom_ext
    ext x
    apply Prod.ext
    · have h := congrArg (fun q => q.hom x) hf
      simpa only [coneComplex, coneX, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply] using h
    · have h := congrArg (fun q => q.hom x) hs
      simpa only [coneComplex, coneX, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply] using h

/-- The homotopy cofiber of `g : K ⟶ K` is isomorphic to the explicit cone complex of `g`. -/
private noncomputable def cofiberIsoCone
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (g : K ⟶ K) :
    HomologicalComplex.homotopyCofiber g ≅ coneComplex K K g :=
  HomologicalComplex.Hom.isoOfComponents (cofiberToConeX K g) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    exact cofiberToConeX_comm K g j)

/-- The isomorphism of `Stacks.MappingCone.NatIndexed.koszulComplex_phiPrime_iso_cone`, without
its degreewise components. -/
private noncomputable def coneIsoKoszul (φ : Module.Dual R E) (f : R) :
    coneComplex (Koszul.complex φ) (Koszul.complex φ)
        (mulByF (Koszul.complex φ) f) ≅
      Koszul.complex (phiPrime φ f) :=
  (koszulComplex_phiPrime_iso_cone φ f).choose

/-- Adjoining `f` to a linear functional `φ` turns its Koszul complex into the mapping cone of
multiplication by `f` on `Koszul.complex φ`. -/
theorem koszulComplex_coprod_smul_id_iso_homotopyCofiber
    (φ : E →ₗ[R] R) (f : R) :
    Nonempty
      (Koszul.complex (φ.coprod (f • LinearMap.id)) ≅
        HomologicalComplex.homotopyCofiber (f • 𝟙 (Koszul.complex φ))) := by
  have hφ : phiPrime φ f = φ.coprod (f • (LinearMap.id : R →ₗ[R] R)) := by
    apply LinearMap.ext
    rintro ⟨e, r⟩
    simp [phiPrime]
  rw [← hφ]
  exact ⟨(coneIsoKoszul φ f).symm ≪≫
    (cofiberIsoCone (Koszul.complex φ) (mulByF (Koszul.complex φ) f)).symm⟩

end

/-! ## Adjoining a product to a linear functional -/

/-- The extension by zero of a chain complex vanishes in positive cohomological degrees. -/
private lemma isZero_extend_X_of_pos {C : Type w} [Category C] [Preadditive C]
    [HasZeroObject C] (K : ChainComplex C ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((K.extend ComplexShape.embeddingDownNat).X i) :=
  K.isZero_extend_X _ _ fun m h => by
    change -(m : ℤ) = i at h
    omega

/-- The degreewise comparison between extension of a cone and the cone of the extended map. -/
private noncomputable def extendHomotopyCofiberXIso
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K L : ChainComplex C ℕ) (a : K ⟶ L) (i : ℤ) :
    ((HomologicalComplex.homotopyCofiber a).extend
      ComplexShape.embeddingDownNat).X i ≅
      (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat)).X i := by
  match i with
  | .ofNat 0 =>
      exact (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat
        (i := 0) (i' := 0) rfl) ≪≫
        HomologicalComplex.homotopyCofiber.XIso a 0 (by simp) ≪≫
        (HomologicalComplex.extendXIso L ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) rfl).symm ≪≫
        isoZeroBiprod (by
          exact isZero_extend_X_of_pos K 1 (by omega)) ≪≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) 0 1 rfl).symm
  | .ofNat (n + 1) =>
      exact IsZero.iso
        (isZero_extend_X_of_pos _ _ (by simp only [Int.ofNat_eq_natCast]; omega))
        ((CochainComplex.mappingCone.isZero_X_iff _ _).2 ⟨
          isZero_extend_X_of_pos K _ (by simp only [Int.ofNat_eq_natCast]; omega),
          isZero_extend_X_of_pos L _ (by simp only [Int.ofNat_eq_natCast]; omega)⟩)
  | .negSucc n =>
      exact (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat
        (i := n + 1) (i' := Int.negSucc n) rfl) ≪≫
        HomologicalComplex.homotopyCofiber.XIsoBiprod a (n + 1) n (by simp) ≪≫
        biprod.mapIso
          (HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).symm
          (HomologicalComplex.extendXIso L ComplexShape.embeddingDownNat
            (i := n + 1) (i' := Int.negSucc n) rfl).symm ≪≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat)
          (.negSucc n) (-(n : ℤ)) (by
            change Int.negSucc n + 1 = -(n : ℤ)
            omega)).symm

private lemma inlX_extendHomotopyCofiberXIso_inv
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K L : ChainComplex C ℕ) (a : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat)
        (-(n : ℤ)) (.negSucc n) (by change Int.negSucc n + 1 = -(n : ℤ); omega) ≫
      (extendHomotopyCofiberXIso K L a (.negSucc n)).inv =
    (HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.inlX a n (n + 1) (by simp) ≫
      (HomologicalComplex.extendXIso (HomologicalComplex.homotopyCofiber a)
        ComplexShape.embeddingDownNat (i := n + 1) (i' := Int.negSucc n) rfl).inv := by
  simp [extendHomotopyCofiberXIso, Category.assoc, biprod.mapIso]

private lemma inrX_extendHomotopyCofiberXIso_inv_negSucc
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K L : ChainComplex C ℕ) (a : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homotopyCofiber.inrX
        (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) (.negSucc n) ≫
      (extendHomotopyCofiberXIso K L a (.negSucc n)).inv =
    (HomologicalComplex.extendXIso L ComplexShape.embeddingDownNat
      (i := n + 1) (i' := Int.negSucc n) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.inrX a (n + 1) ≫
      (HomologicalComplex.extendXIso (HomologicalComplex.homotopyCofiber a)
        ComplexShape.embeddingDownNat (i := n + 1) (i' := Int.negSucc n) rfl).inv := by
  simp [extendHomotopyCofiberXIso, Category.assoc, biprod.mapIso]

private lemma inrX_extendHomotopyCofiberXIso_inv_zero
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K L : ChainComplex C ℕ) (a : K ⟶ L) :
    HomologicalComplex.homotopyCofiber.inrX
        (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) 0 ≫
      (extendHomotopyCofiberXIso K L a 0).inv =
    (HomologicalComplex.extendXIso L ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.inrX a 0 ≫
      (HomologicalComplex.extendXIso (HomologicalComplex.homotopyCofiber a)
        ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).inv := by
  simp only [extendHomotopyCofiberXIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc, isoZeroBiprod_inv,
    biprod.inr_snd_assoc]
  simp [HomologicalComplex.homotopyCofiber.inrX]

/-- Extension by zero from homological to cohomological degrees commutes with cones. -/
private noncomputable def extendHomotopyCofiberIso
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K L : ChainComplex C ℕ) (a : K ⟶ L) :
    (HomologicalComplex.homotopyCofiber a).extend
        ComplexShape.embeddingDownNat ≅
      CochainComplex.mappingCone
        (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun i => (extendHomotopyCofiberXIso K L a i).symm) (by
    intro i j hij
    dsimp only [Iso.symm_hom, CochainComplex.mappingCone, HomologicalComplex.homotopyCofiber_d]
    change i + 1 = j at hij
    subst j
    cases i with
    | ofNat n =>
        apply (isZero_extend_X_of_pos (HomologicalComplex.homotopyCofiber a) _
            (by simp only [Int.ofNat_eq_natCast]; omega)).eq_of_tgt
    | negSucc n =>
        cases n with
        | zero =>
            change (extendHomotopyCofiberXIso K L a (-1)).inv ≫ _ =
              _ ≫ (extendHomotopyCofiberXIso K L a 0).inv
            apply HomologicalComplex.homotopyCofiber.ext_from_X
              (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat)
              0 (-1) (by simp)
            · simp only [← Category.assoc]
              erw [inlX_extendHomotopyCofiberXIso_inv K L a 0]
              erw [HomologicalComplex.homotopyCofiber.inlX_d
                _ _ _ 1 (by simp) (by simp)]
              rw [HomologicalComplex.extend_d_from_eq_zero K
                ComplexShape.embeddingDownNat 0 1 0 rfl (by simp)]
              simp only [neg_zero, zero_comp, zero_add, Category.assoc,
                inrX_extendHomotopyCofiberXIso_inv_zero]
              erw [HomologicalComplex.extend_d_eq (HomologicalComplex.homotopyCofiber a)
                ComplexShape.embeddingDownNat (i := 1) (j := 0)
                  (i' := Int.negSucc 0) (j' := 0) rfl rfl,
                HomologicalComplex.extendMap_f a ComplexShape.embeddingDownNat
                  (i := 0) (i' := 0) rfl]
              simp only [Category.assoc, Iso.inv_hom_id_assoc,
                HomologicalComplex.homotopyCofiber_d,
                HomologicalComplex.homotopyCofiber.inlX_d'_assoc a 1 0 (by simp) (by simp)]
            · simp only [← Category.assoc]
              erw [inrX_extendHomotopyCofiberXIso_inv_negSucc K L a 0]
              erw [HomologicalComplex.homotopyCofiber.inrX_d]
              erw [HomologicalComplex.extend_d_eq (HomologicalComplex.homotopyCofiber a)
                ComplexShape.embeddingDownNat (i := 1) (j := 0)
                  (i' := Int.negSucc 0) (j' := 0) rfl rfl,
                HomologicalComplex.extend_d_eq L ComplexShape.embeddingDownNat
                  (i := 1) (j := 0) (i' := Int.negSucc 0) (j' := 0) rfl rfl]
              simp only [Category.assoc, Iso.inv_hom_id_assoc,
                HomologicalComplex.homotopyCofiber_d,
                HomologicalComplex.homotopyCofiber.inrX_d_assoc]
              erw [inrX_extendHomotopyCofiberXIso_inv_zero]
              simp only [Iso.inv_hom_id_assoc]
        | succ n =>
            have hi : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
            rw [hi]
            apply HomologicalComplex.homotopyCofiber.ext_from_X
              (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat)
              (Int.negSucc n) (Int.negSucc (n + 1)) (by
                change Int.negSucc (n + 1) + 1 = Int.negSucc n
                exact hi)
            · simp only [← Category.assoc]
              erw [inlX_extendHomotopyCofiberXIso_inv K L a (n + 1)]
              rw [HomologicalComplex.homotopyCofiber.inlX_d
                _ _ _ (-(n : ℤ)) (by exact hi) (by change Int.negSucc n + 1 = -(n : ℤ); omega)]
              rw [HomologicalComplex.extend_d_eq (HomologicalComplex.homotopyCofiber a)
                ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
                  (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) rfl rfl,
                HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
                  (i := n + 1) (j := n) (i' := Int.negSucc n) (j' := -(n : ℤ)) rfl rfl,
                HomologicalComplex.extendMap_f a ComplexShape.embeddingDownNat
                  (i := n + 1) (i' := Int.negSucc n) rfl]
              simp only [Category.assoc, Iso.inv_hom_id_assoc,
                HomologicalComplex.homotopyCofiber_d,
                HomologicalComplex.homotopyCofiber.inlX_d_assoc a (n + 2) (n + 1) n
                  (by simp) (by simp),
                Preadditive.add_comp, Preadditive.comp_add,
                Preadditive.neg_comp, Preadditive.comp_neg,
                inlX_extendHomotopyCofiberXIso_inv,
                inrX_extendHomotopyCofiberXIso_inv_negSucc]
            · simp only [← Category.assoc, inrX_extendHomotopyCofiberXIso_inv_negSucc]
              rw [HomologicalComplex.homotopyCofiber.inrX_d]
              rw [HomologicalComplex.extend_d_eq (HomologicalComplex.homotopyCofiber a)
                ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
                  (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) rfl rfl,
                HomologicalComplex.extend_d_eq L ComplexShape.embeddingDownNat
                  (i := n + 2) (j := n + 1)
                  (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) rfl rfl]
              simp only [Category.assoc, Iso.inv_hom_id_assoc,
                HomologicalComplex.homotopyCofiber_d,
                HomologicalComplex.homotopyCofiber.inrX_d_assoc,
                inrX_extendHomotopyCofiberXIso_inv_negSucc])).symm

/-- After adjoining `f * g` to a linear functional, its Koszul complex is homotopy equivalent to
the mapping cone of a map from the shifted complex obtained by adjoining `f` to the complex
obtained by adjoining `g`. -/
@[stacks 062B]
theorem exists_homotopyEquiv_koszulComplex_coprod_mul_mappingCone
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f g : R) :
    let K (a : R) : CochainComplex (ModuleCat.{max u v} R) ℤ :=
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} R)).obj
        (Koszul.complex (φ.coprod (a • LinearMap.id)))
    ∃ ψ : (K f)⟦(-1 : ℤ)⟧ ⟶ K g,
      Nonempty (HomotopyEquiv (K (f * g)) (CochainComplex.mappingCone ψ)) := by
  dsimp
  let F := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} R)
  let A := F.obj (Koszul.complex φ)
  let m (a : R) : A ⟶ A := F.map (a • 𝟙 (Koszul.complex φ))
  have coneIso (a : R) : Nonempty
      (F.obj (Koszul.complex (φ.coprod (a • LinearMap.id))) ≅
        CochainComplex.mappingCone (m a)) := by
    obtain ⟨e⟩ := koszulComplex_coprod_smul_id_iso_homotopyCofiber φ a
    exact ⟨F.mapIso e ≪≫ extendHomotopyCofiberIso (Koszul.complex φ) (Koszul.complex φ)
      (a • 𝟙 (Koszul.complex φ))⟩
  obtain ⟨ef⟩ := coneIso f
  obtain ⟨eg⟩ := coneIso g
  obtain ⟨efg⟩ := coneIso (f * g)
  obtain ⟨ψ₀, ⟨hψ₀⟩⟩ :=
    exists_homotopyEquiv_mappingCone_comp A (m f) (m g)
  let ψ := ef.hom⟦(-1 : ℤ)⟧' ≫ ψ₀ ≫ eg.inv
  refine ⟨ψ, ⟨(HomotopyEquiv.ofIso efg).trans ?_⟩⟩
  have hsource : CochainComplex.mappingCone (m (f * g)) =
      CochainComplex.mappingCone (m g ≫ m f) := by
    congr 1
    dsimp [m]
    rw [← F.map_comp]
    congr 1
    simp [smul_smul]
  refine (HomotopyEquiv.ofIso (eqToIso hsource)).trans (hψ₀.trans ?_)
  let arrowIso : Arrow.mk ψ ≅ Arrow.mk ψ₀ :=
    Arrow.isoMk ((shiftFunctor _ (-1 : ℤ)).mapIso ef) eg (by simp [ψ])
  exact HomotopyEquiv.ofIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso ψ ψ₀
      (fun j => ⟨j - 1, by simp⟩) arrowIso).symm

/-! ## A Koszul complex whose last entry is a product -/

/-- Replacing the source and target of a morphism by isomorphic complexes replaces its mapping
cone by an isomorphic one. -/
private noncomputable def mappingConeIsoOfIso
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
    (φ : K₁ ⟶ L₁) :
    CochainComplex.mappingCone φ ≅
      CochainComplex.mappingCone (a.inv ≫ φ ≫ b.hom) := by
  let comm : φ ≫ b.hom = a.hom ≫ (a.inv ≫ φ ≫ b.hom) := by simp
  let comm' : (a.inv ≫ φ ≫ b.hom) ≫ b.inv = a.inv ≫ φ := by simp
  let F := CochainComplex.mappingCone.map φ (a.inv ≫ φ ≫ b.hom)
      a.hom b.hom comm
  let G := CochainComplex.mappingCone.map (a.inv ≫ φ ≫ b.hom) φ
      a.inv b.inv comm'
  exact
    { hom := F
      inv := G
      hom_inv_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simpa using CochainComplex.mappingCone.map_id φ
      inv_hom_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simpa using CochainComplex.mappingCone.map_id (a.inv ≫ φ ≫ b.hom) }

/-- The Koszul complex on a finite sequence ending in `f * g` is homotopy equivalent to the mapping
cone of a map from the shifted complex ending in `f` to the complex ending in `g`. -/
@[stacks 062C]
theorem exists_homotopyEquiv_koszulComplex_snoc_mul_mappingCone
    {R : Type u} [CommRing R] {n : ℕ} (s : Fin n → R) (f g : R) :
    let K (a : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj
        (Koszul.complex (Fintype.linearCombination R (Fin.snoc s a)))
    ∃ ψ : (K f)⟦(-1 : ℤ)⟧ ⟶ K g,
      Nonempty (HomotopyEquiv (K (f * g)) (CochainComplex.mappingCone ψ)) := by
  dsimp
  let E := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)
  let φ := Koszul.seqDual s
  let P (a : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
    E.obj (Koszul.complex (φ.coprod (a • LinearMap.id)))
  let K (a : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
    E.obj (Koszul.complex (Fintype.linearCombination R (Fin.snoc s a)))
  have hchain (a : R) :
      Koszul.complex (φ.coprod (a • LinearMap.id)) ≅
        Koszul.complex (Fintype.linearCombination R (Fin.snoc s a)) := by
    let h := complexLinearEquiv (snocLinearEquiv n)
      (Koszul.seqDual (Fin.snoc s a))
    rw [seqDual_comp_snocLinearEquiv] at h
    exact h
  let q (a : R) : P a ≅ K a := E.mapIso (hchain a)
  obtain ⟨ψ₀, ⟨hψ₀⟩⟩ :=
    exists_homotopyEquiv_koszulComplex_coprod_mul_mappingCone φ f g
  let qf := (shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)).mapIso (q f)
  exact ⟨qf.inv ≫ ψ₀ ≫ (q g).hom, ⟨(HomotopyEquiv.ofIso (q (f * g)).symm).trans
    (hψ₀.trans (HomotopyEquiv.ofIso (mappingConeIsoOfIso qf (q g) ψ₀)))⟩⟩

end Koszul
